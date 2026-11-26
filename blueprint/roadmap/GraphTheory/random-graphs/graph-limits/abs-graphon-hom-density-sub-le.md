# Counting lemma for graphons

For graphons $U, W$ with values in $[0, 1]$ and every simple graph $F$,

$$|t(F, U) - t(F, W)| \le |E(F)| \cdot \|U - W\|_\square .$$

The proof is the telescoping argument of the finite [counting lemma](abs-hom-density-sub-hom-density-le.md), with sums replaced by integrals.

## Background

- [Bilinear forms are bounded by the cut norm](abs-sum-sum-mul-le-cut-max.md): the finite form of the identity $\sup_{0 \le f, g \le 1} |\int W(x,y) f(x) g(y)| = \|W\|_\square$ that the proof uses to bound each telescoping term.

## Sources

- L. Lovász and B. Szegedy, "Limits of dense graph sequences", *J. Combin. Theory Ser. B* 96 (2006), 933–957, arXiv:math/0408173, Lemma 4.1 (and the identity (6) used in its proof).
