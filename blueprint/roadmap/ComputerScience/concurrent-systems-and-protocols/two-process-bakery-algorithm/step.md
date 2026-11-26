# Step

One move of process `i`, by its program counter: from the noncritical section it raises its `choosing` flag; it then reads the other process's ticket, writes its own ticket as that value plus one, and lowers its flag; it waits while the other process is choosing and then until it may enter; it enters the critical section, exits, and returns to the noncritical section with ticket `0`.
