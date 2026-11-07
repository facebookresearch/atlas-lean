# Atomicity between participants

For every set $P$ of participants, in every reachable
state of the two-phase commit protocol, if some participant $p$ has committed, then no
participant $q$ has aborted.

This is the participant part of condition AC1 of Bernstein, Hadzilacos and Goodman.
