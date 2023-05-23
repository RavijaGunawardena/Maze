/* Robot
 * Author: RavijaGunawardana
 * Creation date: 12/25/2022
 */
MACHINE
    Robot

SEES
    Maze

SETS
    // REPORT set of the Robot
    REPORT = { 
            CANNOT_MOVE_INTERNAL_WALL_DETECTED, CANNOT_MOVE_OUT_OF_THE_MAZE, CANNOT_TELEPORT_TO_INTERNAL_WALLS, CANNOT_TELEPORT_OUT_OF_MAZE,
            INVALID_ENTRY_HIT_INTERNAL_WALL, INVALID_ENTRY_OUT_OF_MAZE, SUCCESSFULLY_TELEPORTED, CANNOT_TELEPORT_IMMEDIATELY_FROM_START_TO_EXIT,
            CANNOT_TELEPORT_IMMEDIATELY_TO_EXIT, CANNOT_TELEPORT_TO_SAME_POSITION, MOVE_SUCCESSFULLY, CANNOT_MOVE_FURTHER, YES_VISITED, NO_NOT_VISITED,
            YES_CURRENT_POSITION_HAS_BEEN_VISITED_BEFORE, NO_CURRENT_POSITION_HAS_NOT_BEEN_VISITED_BEFORE 
    };
    
    OUTPUT_MESSAGES = { YES, NO, CAN_RESET, CANNOT_RESET }       
               
VARIABLES
    robot_current_position,
    robot_visited_path,
    robot_x_position, 
    robot_y_position     

INVARIANT
    
    // Robot's x-axis and y-axis positions are being within the Maze x(1-7) and y(1-5) range 
    robot_x_position : NATURAL1 & 
    robot_x_position : maze_x_range &
    
    robot_y_position : NATURAL1 & 
    robot_y_position : maze_y_range &

    (robot_x_position |-> robot_y_position) : maze &
    (robot_x_position |-> robot_y_position) /: internal_wall &

    robot_current_position = (robot_x_position |-> robot_y_position) &
    robot_current_position : (maze) & 
    
    // current position of the Robot is not an element of the Internal wall
    robot_current_position /: internal_wall &

    // squares that the robot has visited are stored here
    robot_visited_path : seq(maze) 

INITIALISATION
    // Initializing all variables by assuming Robot is in the initial square (1,1).
    robot_current_position := ( 1 |-> 1 ) ||
    robot_visited_path := [( 1 |-> 1 )] ||
    robot_x_position := 1 ||
    robot_y_position := 1 

OPERATIONS

// Moves to North

    result <-- MoveNorth =
        PRE result : REPORT
        THEN
            // Checks if there is any internal wall or external wall
            IF
               ((robot_x_position |-> robot_y_position + 1) /: maze)               
            THEN
                result := CANNOT_MOVE_OUT_OF_THE_MAZE
            ELSIF
                ((robot_x_position |-> robot_y_position + 1) : internal_wall)       
            THEN
                result := CANNOT_MOVE_INTERNAL_WALL_DETECTED

            // Checks if the robot has been visited to exit square
            ELSIF
                (robot_current_position = exit_square)       
            THEN
                result := CANNOT_MOVE_FURTHER
            
            // Moves the robot to North
            ELSE
                robot_visited_path := robot_visited_path <- (robot_x_position |-> robot_y_position + 1) ||
                robot_current_position := (robot_x_position |-> robot_y_position + 1) ||
                robot_y_position := robot_y_position + 1 ||
                result := MOVE_SUCCESSFULLY
            END
        END;


// Moves to East

    result <-- MoveEast =
        PRE result : REPORT
        THEN
            
            IF  
                ((robot_x_position + 1 |-> robot_y_position ) /: maze)   
            THEN
                result := CANNOT_MOVE_OUT_OF_THE_MAZE
            ELSIF
                ((robot_x_position + 1 |-> robot_y_position) : internal_wall)
            THEN
                result := CANNOT_MOVE_INTERNAL_WALL_DETECTED

            ELSIF
                (robot_current_position = exit_square)       
            THEN
                result := CANNOT_MOVE_FURTHER

            ELSE
                robot_visited_path := robot_visited_path <- (robot_x_position + 1 |-> robot_y_position) ||
                robot_current_position := (robot_x_position + 1 |-> robot_y_position) ||
                robot_x_position := robot_x_position + 1 ||
                result := MOVE_SUCCESSFULLY 
            END
        END;
        

// Moves to South

    result <-- MoveSouth =
        PRE result : REPORT
        THEN

            IF
                ((robot_x_position |-> robot_y_position - 1 ) /: maze)
            THEN
                result := CANNOT_MOVE_OUT_OF_THE_MAZE
            ELSIF
                ((robot_x_position |-> robot_y_position - 1 ) : internal_wall)
            THEN
                result := CANNOT_MOVE_INTERNAL_WALL_DETECTED

            ELSIF
                (robot_current_position = exit_square)       
            THEN
                result := CANNOT_MOVE_FURTHER

            ELSE
                robot_visited_path := robot_visited_path <- (robot_x_position |-> robot_y_position - 1) ||                    
                robot_current_position := (robot_x_position |-> robot_y_position - 1) ||
                robot_y_position := robot_y_position - 1 ||
                result := MOVE_SUCCESSFULLY
            END
        END;

// Moved to West

    result <-- MoveWest =
        PRE result : REPORT
        THEN

            IF
               ((robot_x_position - 1 |-> robot_y_position ) /: maze)
            THEN
                result := CANNOT_MOVE_OUT_OF_THE_MAZE
            ELSIF
                ((robot_x_position - 1 |-> robot_y_position) : internal_wall)
            THEN
                result := CANNOT_MOVE_INTERNAL_WALL_DETECTED

            ELSIF
                (robot_current_position = exit_square)       
            THEN
                result := CANNOT_MOVE_FURTHER
                
            ELSE
                robot_visited_path := robot_visited_path <- (robot_x_position - 1 |-> robot_y_position) ||
                robot_current_position := (robot_x_position - 1 |-> robot_y_position) ||
                robot_x_position := robot_x_position - 1 ||
                result := MOVE_SUCCESSFULLY
            END
        END;
        

// Teleport the robot

    result <-- Teleport (goto_x_position, goto_y_position) = 
        PRE
            goto_x_position : maze_x_range &
            goto_y_position : maze_y_range &
            result : REPORT
        THEN
            
            // Cannot teleport without doing the first move to 
            IF
                (size(robot_visited_path) = 1 & 
                (goto_x_position |-> goto_y_position) = exit_square) 
            THEN
                result := CANNOT_TELEPORT_IMMEDIATELY_FROM_START_TO_EXIT

            // Avoid teloporting to the exit square directly
            ELSIF
                ((goto_x_position |-> goto_y_position) = exit_square)
            THEN
                result := CANNOT_TELEPORT_IMMEDIATELY_TO_EXIT

            // validation to prevent teleport to the same current position
            ELSIF
                ((goto_x_position |-> goto_y_position) = (robot_x_position |-> robot_y_position))           
            THEN
                result := CANNOT_TELEPORT_TO_SAME_POSITION
                
            ELSIF     
                ((goto_x_position |-> goto_y_position) : internal_wall)
            THEN
                result := CANNOT_TELEPORT_TO_INTERNAL_WALLS

            // Cannot teloport from the exit square 
            ELSIF
                (robot_current_position = exit_square)       
            THEN
                result := CANNOT_MOVE_FURTHER

            ELSE
                robot_x_position := goto_x_position ||
                robot_y_position := goto_y_position ||
                robot_current_position := (goto_x_position |-> goto_y_position) ||
                robot_visited_path := (robot_visited_path <- (goto_x_position |-> goto_y_position)) ||
                result := SUCCESSFULLY_TELEPORTED
             END
        END;        
        
// Checks the current visited position
    answer <-- hasVisitedSquare =
        PRE 
            answer : REPORT
        THEN
            IF
                ((robot_x_position |-> robot_y_position) : ran(front(robot_visited_path)))
            THEN
                answer := YES_CURRENT_POSITION_HAS_BEEN_VISITED_BEFORE
                
            ELSE                 
                answer := NO_CURRENT_POSITION_HAS_NOT_BEEN_VISITED_BEFORE
            END
        END;        
        

// Reset operation
    result <-- Reset =
        PRE result : OUTPUT_MESSAGES
        THEN
            // Reset is available when only staying exit square
            IF (robot_current_position = exit_square)
            THEN 
                robot_x_position := 1 ||
                robot_y_position := 1 ||
                robot_current_position := (1 |-> 1) ||
                robot_visited_path := [( 1 |-> 1 )] ||
               
                result := CAN_RESET
            ELSE 
                result := CANNOT_RESET
            END
        END;


// Found exit?
    answer <-- foundExit =
        PRE answer : OUTPUT_MESSAGES
        THEN
            // Checks if the Robot's current position is equal to the exit square (1,5)
            IF (robot_current_position = exit_square)
            THEN 
                answer := YES 
            ELSE 
                answer := NO
            END
        END;
        

// Get the current position of the robot   
    answer <-- getPosition =
        BEGIN
            answer := robot_current_position
        END;
        

// List of visited paths
    answer <-- robotsRoute =
        BEGIN
            answer := robot_visited_path 
        END        
        

END
