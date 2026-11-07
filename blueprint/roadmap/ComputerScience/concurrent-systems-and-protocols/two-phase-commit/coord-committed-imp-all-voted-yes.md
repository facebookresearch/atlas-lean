# Validity for the coordinator

In every reachable state of the two-phase commit protocol,
if the coordinator has decided commit, then every participant voted yes, that is, every
participant is prepared or committed.

This is the coordinator form of condition AC3 of Bernstein, Hadzilacos and Goodman.
