# Total correctness gives a terminating small-step run

If the total-correctness Hoare
triple with precondition $P$, command $c$ and postcondition $Q$ is valid and a state $s$
satisfies $P$, then there is a state $t$ such that $c$, started in $s$, reaches
$\mathtt{skip}$ with state $t$ in finitely many small steps, and $t$ satisfies $Q$.
