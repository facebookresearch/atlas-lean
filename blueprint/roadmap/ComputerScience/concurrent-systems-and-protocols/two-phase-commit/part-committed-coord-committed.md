# A committed participant has a committed coordinator

In every reachable state of the
two-phase commit protocol, if some participant has committed, then the coordinator has
committed.

This is the atomicity condition AC1 of Bernstein, Hadzilacos and Goodman between a participant
and the coordinator.
