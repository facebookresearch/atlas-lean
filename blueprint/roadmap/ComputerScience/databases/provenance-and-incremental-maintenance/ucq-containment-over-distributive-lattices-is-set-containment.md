# Containment of unions of conjunctive queries over nontrivial distributive lattices is set containment

For a naturally ordered commutative semiring $K$ and queries $q_1, q_2$ on $K$-relations, write
$q_1 \sqsubseteq_K q_2$ when $q_1(R)(t) \le q_2(R)(t)$ for every $K$-instance $R$ and every tuple $t$; for
$K = \mathbb B$ and $K = \mathbb N$ this is set and bag containment. If $K$ is a nontrivial bounded distributive lattice
($0 \ne 1$, with join as addition and meet as multiplication), then for all unions of conjunctive queries $q_1, q_2$,
$q_1 \sqsubseteq_K q_2$ if and only if $q_1 \sqsubseteq_{\mathbb B} q_2$. Nontriviality is needed: over the one-element lattice
$R(x)$ is contained in $S(x)$, which fails under set semantics.

## Depends on

- [K-relations and positive relational algebra over a semiring](k-relations-and-positive-relational-algebra-over-a-semiring.md)
- [Positive relational algebra = unions of conjunctive queries = positive existential calculus](../relational-calculus/positive-relational-algebra-unions-of-conjunctive-queries-po.md)

## Proof depends on

- [Universality of provenance polynomials](universality-of-provenance-polynomials.md)
- [Chandra-Merlin containment criterion](../conjunctive-queries/conjunctive-queries-and-the-chandra-merlin-theor/contained-iff-hom.md)

## Sources

- T. J. Green, G. Karvounarakis and V. Tannen, *Provenance semirings*, PODS 2007, Definition 9.1 and Theorem 9.2. <http://www.cs.ucdavis.edu/~green/papers/pods07.pdf>
