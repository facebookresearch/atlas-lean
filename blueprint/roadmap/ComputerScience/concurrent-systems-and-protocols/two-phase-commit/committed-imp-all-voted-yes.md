# Validity for participants

In every reachable state of the two-phase commit protocol, if
some participant has committed, then every participant voted yes, that is, every participant is
prepared or committed.

This is the participant form of condition AC3 of Bernstein, Hadzilacos and Goodman; that the
coordinator has then decided commit is the separate result that a committed participant has a
committed coordinator.
