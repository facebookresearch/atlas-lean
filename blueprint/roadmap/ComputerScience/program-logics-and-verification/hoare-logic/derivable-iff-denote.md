# Partial-correctness Hoare logic matches the denotational semantics

For all assertions
$P$ and $Q$ and every command $c$, the partial-correctness triple with precondition $P$, command
$c$ and postcondition $Q$ is derivable if and only if, for all states $s$ and $t$ such that $P$
holds at $s$ and the pair $(s, t)$ lies in the relational denotation of $c$, $Q$ holds at $t$.
