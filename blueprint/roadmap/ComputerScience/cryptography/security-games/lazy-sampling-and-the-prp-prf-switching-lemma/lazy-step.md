# Lazy sampling step

For each table $T$ and query $x$, let $\nu_T(x)$ be a distribution on answers. One step of the
lazily sampled oracle with table $T$ answers a recorded query from the table, which it leaves
unchanged, and answers a query $x$ without a recorded answer by a sample $y$ of $\nu_T(x)$, recording
$x \mapsto y$. In the words of Katz and Lindell (Section 5.5.1), the oracle keeps a table and answers
a new query with a fresh random value.
