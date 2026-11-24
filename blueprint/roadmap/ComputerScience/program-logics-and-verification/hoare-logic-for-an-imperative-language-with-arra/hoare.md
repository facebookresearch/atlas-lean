# Partial-correctness Hoare triples for the imperative language with arrays

For predicates $P$ and $Q$ on states and a statement $c$, the partial-correctness Hoare triple $\lbrace P \rbrace\ c\ \lbrace Q \rbrace$ holds when for all states $s$ and $s'$, if $P(s)$ holds and $c$ takes $s$ to $s'$ in the big-step semantics, then $Q(s')$ holds. An out-of-bounds read and a diverging loop have no execution, so a triple asserts neither safety nor termination.
