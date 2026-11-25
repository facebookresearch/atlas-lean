# Atomicity between participants

For every set $P$ of participants, in every reachable
state of the two-phase commit protocol, if some participant $p$ has committed, then no
participant $q$ has aborted.

This is the participant part of condition AC1 of Bernstein, Hadzilacos and Goodman.

## Sources

- P. A. Bernstein, V. Hadzilacos, N. Goodman, *Concurrency Control and Recovery in Database Systems*, Addison-Wesley, 1987: Chapter 7, atomic commitment condition AC1.
