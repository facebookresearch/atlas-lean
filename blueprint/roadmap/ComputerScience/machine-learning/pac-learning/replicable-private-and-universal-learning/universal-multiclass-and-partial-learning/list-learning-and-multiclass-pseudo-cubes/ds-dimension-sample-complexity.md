# Quantitative multiclass PAC bounds from the DS dimension

Let $H \subseteq Y^X$ have DS dimension $d < \infty$, with $Y$ arbitrary. There is a realizable learner which, for every $H$-realizable $D$, every $\delta > 0$ and every $n$, outputs from $S \sim D^n$ a hypothesis $h$ with

$$
\Pr_{(x,y) \sim D}[h(x) \ne y] \le \tilde O\!\left(\frac{d^{3/2} + \log(1/\delta)}{n}\right)
$$

with probability at least $1-\delta$, and an agnostic learner with excess error $\tilde O\big(\sqrt{(d^{3/2} + \log(1/\delta))/n}\big)$, where $\tilde O$ hides factors polylogarithmic in $n$ and $d$.

## Proof sketch

The list learner of the previous lemma is boosted to a list learner with small error and list size depending only on $d$; on the support of a realizable menu of size $p$ the class has Natarajan dimension that controls an orientation of out-degree $O(d_N \log p)$ via shifting. Combining the two stages gives a sample compression scheme of size $\tilde O(d^{3/2})$, and the compression generalization bound yields the realizable rate; the agnostic rate follows from the standard realizable-to-agnostic reduction for compression schemes.

## Depends on

- [k-pseudo-cubes and the k-DS dimension](k-pseudo-cube.md)
- [The realizable distribution family](../../../occam-bound-for-consistent-learners/realizable-family.md)

## Proof depends on

- [Finite DS dimension gives a list PAC learner from one-inclusion orientations](finite-ds-dimension-list-learner.md)
- [Generalization bound for sample compression schemes](../../../../generalization-bounds-and-concentration/generalization-bound-for-sample-compression-schemes.md)
- [DS dimension characterizes multiclass PAC learnability](../../../ds-dimension-characterizes-multiclass-pac-learnability.md)

## Sources

- N. Brukhim, D. Carmon, I. Dinur, S. Moran, A. Yehudayoff, "A Characterization of Multiclass Learnability", FOCS (2022), arXiv:2203.01550.
