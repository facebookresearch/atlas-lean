# Validity for the coordinator

In every reachable state of the two-phase commit protocol,
if the coordinator has decided commit, then every participant voted yes, that is, every
participant is prepared or committed.

This is the coordinator form of condition AC3 of Bernstein, Hadzilacos and Goodman.

## Sources

- P. A. Bernstein, V. Hadzilacos, N. Goodman, *Concurrency Control and Recovery in Database Systems*, Addison-Wesley, 1987: Chapter 7, atomic commitment condition AC3.
