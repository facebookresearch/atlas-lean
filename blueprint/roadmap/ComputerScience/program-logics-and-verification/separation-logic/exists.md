# Existential rule for separation-logic triples

Let $c$ be a heap command, let $\iota$ be
an arbitrary index (any type or proposition), and let $P_i$ and $Q_i$ be heap assertions for
each $i$ in $\iota$. If for every $i$ the triple with precondition $P_i$, command $c$ and
postcondition $Q_i$ is valid, then the triple with precondition "there is $i$ with $P_i$",
command $c$ and postcondition "there is $i$ with $Q_i$" is valid.
