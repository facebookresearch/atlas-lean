# An aborted coordinator has no committed participant

In every reachable state of the
two-phase commit protocol, if the coordinator has decided abort, then no participant has
committed.

This is the coordinator–participant part of condition AC1 of Bernstein, Hadzilacos and
Goodman.
