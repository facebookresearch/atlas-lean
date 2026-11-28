# Finite DS dimension gives a list PAC learner from one-inclusion orientations

Let $H \subseteq Y^X$ have DS dimension $d < \infty$ and let $t \in \mathbb{N}$. There is a list learner that maps every sample $S$ of $n = d + t$ examples to a menu $\mu_S : X \to \{A \subseteq Y : |A| \le p\}$ with $p = \binom{n}{t}$, such that for every $H$-realizable distribution $D$,

$$
\Pr_{(S,(x,y)) \sim D^{n+1}}\big[y \in \mu_S(x)\big] \ge \frac{t+1}{d+t+1}.
$$

## Proof sketch

For each of the $p$ subsamples of $S$ of size $d$, run the one-inclusion algorithm, which on $d$ training points and one test point uses an orientation of out-degree at most $d$ of the one-inclusion hypergraph on $d+1$ coordinates, and put the $p$ predicted labels into the menu. By leave-one-out symmetrization over the $n+1 = d+t+1$ examples, it suffices to find, for a realizable sequence of $d+t+1$ examples, at least $t+1$ indices $i$ whose label is in the menu built from the other $d+t$ examples; the out-degree bound on $d+1$ coordinates gives such indices one at a time, so the success probability is at least $(t+1)/(d+t+1)$.

## Depends on

- [List PAC learners and list learnability](list-pac-learner.md)
- [k-pseudo-cubes and the k-DS dimension](k-pseudo-cube.md)

## Proof depends on

- [Pseudo-cubes force out-degree at least half their dimension](pseudo-cube-outdegree-lower-bound.md)
- [One-inclusion hypergraphs, orientations and out-degree](one-inclusion-hypergraph.md)

## Sources

- N. Brukhim, D. Carmon, I. Dinur, S. Moran, A. Yehudayoff, "A Characterization of Multiclass Learnability", FOCS (2022), arXiv:2203.01550, Definitions 30 and 31, Algorithm 2 and Proposition 32.
