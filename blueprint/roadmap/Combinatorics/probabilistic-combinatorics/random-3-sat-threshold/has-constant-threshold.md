# Random 3-SAT threshold conjecture

There is a real number $c$ that is both a lower and
an upper threshold cutoff: for every real $r < c$, the probability that a uniformly random
formula with $\lfloor r n \rfloor$ clauses on $n$ variables is satisfiable tends to $1$ as
$n \to \infty$, and for every real $r > c$ this probability tends to $0$ (when $r n < 0$ the
formula has no clauses).

This page defines a proposition, rather than asserting that the cutoff exists. Friedgut's sharp-threshold theorem allows an $n$-dependent threshold. The [limiting threshold result for every fixed clause size](../random-k-sat/limiting-clause-density.md) includes this precise $k=3$ assertion: use the same clause law, and use the empty formula for negative densities. The statement and the limiting-threshold proof are separate.
