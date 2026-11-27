# Answering Boolean conjunctive queries under updates is OMv-hard unless the core is q-hierarchical

A dynamic algorithm for a conjunctive query receives the query and an initial database, preprocesses them, and then
processes single-tuple insertions and deletions; the preprocessing, update, delay, answer and counting times are measured on
a random access machine as in [enumeration with constant delay](enumeration-with-linear-preprocessing-and-constant-delay.md),
with $n$ the size of the active domain.

**Theorem.** Fix $\varepsilon > 0$ and a Boolean conjunctive query $\varphi$ whose [core](../../conjunctive-queries/cores-and-minimization/minimizations-and-cores-of-conjunctive-queries.md)
is not [q-hierarchical](q-hierarchical-conjunctive-queries.md). Unless the OMv conjecture fails, no dynamic algorithm with arbitrary
preprocessing time and update time $O(n^{1-\varepsilon})$ answers $\varphi$ in time $O(n^{2-\varepsilon})$. If the core is
q-hierarchical, the query is answered in constant time after linear preprocessing and with constant update time.

## Depends on

- [Q-hierarchical conjunctive queries](q-hierarchical-conjunctive-queries.md)
- [Minimizations and cores of conjunctive queries](../../conjunctive-queries/cores-and-minimization/minimizations-and-cores-of-conjunctive-queries.md)
- [The online matrix-vector multiplication conjecture](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-online-matrix-vector-multiplication.md)
- [Enumeration with linear preprocessing and constant delay](enumeration-with-linear-preprocessing-and-constant-delay.md)

## Proof depends on

- [Q-hierarchical conjunctive queries can be maintained under updates](q-hierarchical-cqs-can-be-maintained-under-updates.md)

## Sources

- C. Berkholz, J. Keppeler and N. Schweikardt, "Answering conjunctive queries under updates", *Proceedings of the 36th ACM PODS*, 2017, pp. 303–318; arXiv:1702.06370 <https://arxiv.org/abs/1702.06370>, Theorems 1.2 and 3.4.
