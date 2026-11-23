# Multistep transitions preserve the two-phase commit invariant

If a state $s$ of the
two-phase commit protocol satisfies the inductive invariant and a state $t$ is reached from $s$
by a finite sequence of transitions, then $t$ satisfies the invariant.
