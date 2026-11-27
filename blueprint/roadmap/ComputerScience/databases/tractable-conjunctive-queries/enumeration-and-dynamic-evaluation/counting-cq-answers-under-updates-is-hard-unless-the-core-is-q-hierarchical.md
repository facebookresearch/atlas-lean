# Counting answers under updates is hard unless the core is q-hierarchical

A dynamic algorithm for a conjunctive query receives the query and an initial database, preprocesses them, and then
processes single-tuple insertions and deletions; the preprocessing, update, delay, answer and counting times are measured on
a random access machine as in [enumeration with constant delay](enumeration-with-linear-preprocessing-and-constant-delay.md),
with $n$ the size of the active domain.

**Theorem.** Fix $\varepsilon > 0$ and a conjunctive query $\varphi$ whose [core](../../conjunctive-queries/cores-and-minimization/minimizations-and-cores-of-conjunctive-queries.md)
is not [q-hierarchical](q-hierarchical-conjunctive-queries.md). Assuming the OMv conjecture and the Orthogonal Vectors conjecture,
no dynamic algorithm with arbitrary preprocessing time and update time $O(n^{1-\varepsilon})$ computes $|\varphi(D)|$ in time
$O(n^{1-\varepsilon})$. If $\varphi$ is q-hierarchical, $|\varphi(D)|$ is computed in constant time after linear preprocessing and
with constant update time.

## Depends on

- [Q-hierarchical conjunctive queries](q-hierarchical-conjunctive-queries.md)
- [Minimizations and cores of conjunctive queries](../../conjunctive-queries/cores-and-minimization/minimizations-and-cores-of-conjunctive-queries.md)
- [The online matrix-vector multiplication conjecture](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-online-matrix-vector-multiplication.md)
- [The 3SUM, APSP and Orthogonal Vectors hypotheses](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-3sum-apsp-and-orthogonal-vectors-hypotheses.md)
- [Enumeration with linear preprocessing and constant delay](enumeration-with-linear-preprocessing-and-constant-delay.md)

## Proof depends on

- [Q-hierarchical conjunctive queries can be maintained under updates](q-hierarchical-cqs-can-be-maintained-under-updates.md)

## Sources

- C. Berkholz, J. Keppeler and N. Schweikardt, "Answering conjunctive queries under updates", *Proceedings of the 36th ACM PODS*, 2017, pp. 303–318; arXiv:1702.06370 <https://arxiv.org/abs/1702.06370>, Theorems 1.3 and 3.5.
