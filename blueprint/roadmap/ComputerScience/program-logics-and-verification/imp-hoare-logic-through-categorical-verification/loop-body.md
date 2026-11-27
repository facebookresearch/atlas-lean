# Loop body of a while command

For a boolean guard $b$ and a command $c$, the loop body is a relation from a state on one of two input wires (the external input or the feedback input; which one is ignored) to a state on one of two output wires. From either input carrying $s$, the external output carries $t$ exactly when $b$ is false in $s$ and $t = s$, and the feedback output carries $t$ exactly when $b$ is true in $s$ and $c$ has a terminating big-step execution from $s$ to $t$. In particular a false guard passes on even a state that arrives on the feedback input.
