# Finite DS dimension gives a list PAC learner from one-inclusion orientations

Let $H \subseteq Y^X$ have DS dimension $d < \infty$ and let $t \in \mathbb{N}$. There is a list learner that, on $n = d + t$ realizable examples, outputs a list predictor of list size at most $p = \binom{n}{t}$ whose probability of missing the label of a fresh realizable example is at most $1 - \dfrac{t+1}{d+t+1}$.

## Proof sketch

For each $t$-subset of the sample, run the out-degree-$d$ orientation of the one-inclusion hypergraph on the remaining points plus the test point and collect the predicted labels into the menu. By the leave-one-out symmetrization over the $d + t + 1$ examples, the test label is missed only when the orientation errs on the test point for every subset, and the out-degree bound limits such errors to at most $d$ of the $d+t+1$ positions, giving success probability at least $(t+1)/(d+t+1)$.

## Depends on

- [List PAC learners and list learnability](list-pac-learner.md)
- [k-pseudo-cubes and the k-DS dimension](k-pseudo-cube.md)

## Proof depends on

- [Pseudo-cubes force out-degree at least half their dimension](pseudo-cube-outdegree-lower-bound.md)
- [One-inclusion hypergraphs, orientations and out-degree](one-inclusion-hypergraph.md)

## Sources

- N. Brukhim, D. Carmon, I. Dinur, S. Moran, A. Yehudayoff, "A Characterization of Multiclass Learnability", FOCS (2022), arXiv:2203.01550.
