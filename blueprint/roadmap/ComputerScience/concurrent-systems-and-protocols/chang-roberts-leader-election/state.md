# Chang–Roberts global states

For a ring of $n + 1$ processes $0, \dots, n$, a global
state assigns to each process $k$ the FIFO channel of messages waiting at $k$, oldest first,
where each message is the index of the process whose identifier it carries, and records for
each process whether it has declared itself leader.
