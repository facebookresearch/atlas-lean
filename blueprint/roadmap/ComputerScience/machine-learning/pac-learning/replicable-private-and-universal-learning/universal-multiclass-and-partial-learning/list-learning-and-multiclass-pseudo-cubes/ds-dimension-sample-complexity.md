# Quantitative multiclass PAC bounds from the DS dimension

Let $H \subseteq Y^X$ have DS dimension $d < \infty$, with $Y$ arbitrary. There is a realizable learner which, for every $H$-realizable $D$, every $\delta > 0$ and every $n$, outputs from $S \sim D^n$ a hypothesis $h$ with

$$
\Pr_{(x,y) \sim D}[h(x) \ne y] \le \tilde O\!\left(\frac{d^{3/2} + \log(1/\delta)}{n}\right)
$$

with probability at least $1-\delta$, and an agnostic learner with excess error $\tilde O\big(\sqrt{(d^{3/2} + \log(1/\delta))/n}\big)$, where $\tilde O$ hides factors polylogarithmic in $n$ and $d$.

## Proof sketch

The list learner from one-inclusion orientations, with $t$ of order $\sqrt d$, is applied repeatedly to subsamples, each round covering a constant fraction of the remaining examples, which gives a list sample compression scheme whose menus have size depending only on $d$ and $n$ through $\log n$. Given a menu of size $p$, a class of Natarajan dimension $d_N \le d$ has, by shifting, one-inclusion orientations of out-degree $O(d_N \log p)$, which give a sample compression scheme relative to the menu. Composing the two stages gives an $n \to r$ sample compression scheme with $r = \tilde O(d^{3/2})$, and the compression generalization bound yields the realizable rate; the agnostic rate follows from the agnostic version of that bound.

## Depends on

- [k-pseudo-cubes and the k-DS dimension](k-pseudo-cube.md)
- [The realizable distribution family](../../../occam-bound-for-consistent-learners/realizable-family.md)

## Proof depends on

- [Finite DS dimension gives a list PAC learner from one-inclusion orientations](finite-ds-dimension-list-learner.md)
- [Generalization bound for sample compression schemes](../../../../generalization-bounds-and-concentration/generalization-bound-for-sample-compression-schemes.md)

## Sources

- N. Brukhim, D. Carmon, I. Dinur, S. Moran, A. Yehudayoff, "A Characterization of Multiclass Learnability", FOCS (2022), arXiv:2203.01550, Theorem 1, Theorem 36, Lemmas 17, 39 and 40, Proposition 34.
