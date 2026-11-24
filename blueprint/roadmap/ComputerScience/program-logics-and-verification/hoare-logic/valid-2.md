# Total correctness implies partial correctness

For assertions $P$, $Q$ and a command
$c$, if the total-correctness Hoare triple with precondition $P$, command $c$ and
postcondition $Q$ is valid, then the partial-correctness Hoare triple with the same
precondition, command and postcondition is valid.
