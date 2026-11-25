# Variable elimination computes BN marginals

Let a Bayesian network over finite-valued variables $X_1, \dots, X_n$ have conditional probability tables
$P(X_i \mid \mathrm{pa}(X_i))$, let $E = e$ be evidence on a set $E$ of variables and let $Q$ be a query set
disjoint from $E$. Bucket elimination over $(\mathbb{R}_{\ge 0}, +, \times)$, applied to the $n$ tables
together with the evidence indicator factors $\mathbf{1}[X_j = e_j]$ and eliminating all variables outside
$Q$ along an ordering $d$, computes the table $q \mapsto P(Q = q, E = e)$. With domains of size at most $k$ and
$w^*(d)$ the induced width along $d$ of the moral graph with all pairs of query variables joined, where the
query variables come first in $d$ (so they are never eliminated), it uses
$O\bigl((n + \lvert E \rvert)\, k^{w^*(d) + 1}\bigr)$ arithmetic operations.

## Depends on

- [Bayesian network](bayesian-networks/bayes-net.md)
- [Induced width of an ordering](induced-width-of-an-ordering.md)

## Proof depends on

- [Bucket elimination over a commutative semiring](bucket-elimination-over-a-commutative-semiring.md)

## Related topics

- [Variable elimination computes the unnormalized root marginal](variable-elimination-and-belief-propagation/root-marginal-eq.md)

## Sources

- R. Dechter, *Bucket elimination: a unifying framework for reasoning*, Artificial Intelligence 113 (1999) 41–85, Section 4: algorithm elim-bel (Fig. 17) for an ordering initiated by the query variable, Theorem 3 (p. 58), Theorem 4 (complexity exponential in the induced width of the ordered moral graph, p. 61) and the handling of evidence (Section 4.3). <http://ics.uci.edu/~dechter/publications/r76A.pdf>
