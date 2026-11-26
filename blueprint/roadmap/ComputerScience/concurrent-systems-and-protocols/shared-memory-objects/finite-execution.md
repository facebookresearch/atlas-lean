# Finite Execution

A finite execution starts in the model's initial configuration and follows each event
legally to the next configuration, ending at `last`. The configuration list has one more
entry than the event list, including a single initial configuration in a zero-step execution.
