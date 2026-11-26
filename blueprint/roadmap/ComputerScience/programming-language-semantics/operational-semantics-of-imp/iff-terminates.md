# Hoare validity via small-step termination

For assertions $P$ and $Q$ on states and an IMP
command $c$, the partial-correctness Hoare triple with precondition $P$, command $c$ and
postcondition $Q$ is valid if and only if, for all states $s$ and $s'$, whenever $P$ holds in $s$
and $c$ started in $s$ terminates by small steps in $s'$, $Q$ holds in $s'$.
