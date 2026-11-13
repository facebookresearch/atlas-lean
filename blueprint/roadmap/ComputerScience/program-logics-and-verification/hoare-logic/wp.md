# Weakest precondition for total correctness

For a command $c$ and a postcondition $Q$,
the weakest precondition $\mathrm{wp}(c, Q)$ is the assertion that holds at a state $s$ exactly
when there is a terminating big-step execution of $c$ from $s$ ending in a state that satisfies
$Q$.
