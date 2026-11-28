# Enumerating non-q-hierarchical conjunctive queries under updates is OMv-hard

A dynamic algorithm for a conjunctive query receives the query and an initial database, preprocesses them, and then
processes single-tuple insertions and deletions; the preprocessing, update, delay, answer and counting times are measured on
a random access machine as in [enumeration with constant delay](enumeration-with-linear-preprocessing-and-constant-delay.md),
with $n$ the size of the active domain. Here conjunctive queries are those of the source: every argument of every atom is a variable, and the output lists the
free variables, each once; queries with constants in atoms are not covered.

**Theorem.** Fix $\varepsilon > 0$ and a self-join free conjunctive query $\varphi$ that is not
[q-hierarchical](q-hierarchical-conjunctive-queries.md). Unless the
[OMv conjecture](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-online-matrix-vector-multiplication.md)
fails, no dynamic algorithm with arbitrary preprocessing time and update time $O(n^{1-\varepsilon})$ enumerates $\varphi(D)$ with
delay $O(n^{1-\varepsilon})$. Together with the [upper bound](q-hierarchical-cqs-can-be-maintained-under-updates.md) this gives a
dichotomy for self-join free conjunctive queries.

## Depends on

- [Enumeration with linear preprocessing and constant delay](enumeration-with-linear-preprocessing-and-constant-delay.md)
- [Q-hierarchical conjunctive queries](q-hierarchical-conjunctive-queries.md)
- [The online matrix-vector multiplication conjecture](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-online-matrix-vector-multiplication.md)
- [Q-hierarchical conjunctive queries can be maintained under updates](q-hierarchical-cqs-can-be-maintained-under-updates.md)

## Proof depends on

- [Answering Boolean conjunctive queries under updates is OMv-hard unless the core is q-hierarchical](boolean-cqs-under-updates-are-omv-hard-unless-the-core-is-q-hierarchical.md)

## Sources

- C. Berkholz, J. Keppeler and N. Schweikardt, "Answering conjunctive queries under updates", *Proceedings of the 36th ACM PODS*, 2017, pp. 303–318; arXiv:1702.06370 <https://arxiv.org/abs/1702.06370>, Theorems 1.1 and 3.3, proved in Section 5.
