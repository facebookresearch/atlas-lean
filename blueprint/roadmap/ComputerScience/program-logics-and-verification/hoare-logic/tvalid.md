# Validity of total-correctness Hoare triples

For assertions $P$ and $Q$ on states and a
command $c$, the total-correctness Hoare triple with precondition $P$, command $c$ and
postcondition $Q$ is valid when every state $s$ satisfying $P$ has a terminating big-step
execution of $c$ from $s$ ending in a state $t$ that satisfies $Q$.
