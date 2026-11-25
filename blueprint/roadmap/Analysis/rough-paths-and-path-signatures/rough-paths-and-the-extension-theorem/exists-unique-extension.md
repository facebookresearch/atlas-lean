# Lyons's extension theorem: existence and uniqueness

Let $p \ge 1$, $n = \lfloor p \rfloor$, let $J$ be an interval, and let $X$ be a
[multiplicative functional](is-multiplicative-functional.md) of degree $n$ on $J$ with
[finite $p$-variation](has-finite-pvariation.md). Then there is a multiplicative functional $Y$ of
every degree, with $Y^i_{s,t} = X^i_{s,t}$ for $i \le n$ and $s \le t$ in $J$, of finite
$p$-variation in every degree; and every multiplicative functional of some degree $m$ with finite
$p$-variation that agrees with $X$ up to level $n$ agrees with $Y$ up to level $m$.

So a $p$-rough path, a multiplicative functional of degree $\lfloor p \rfloor$, has unique
higher iterated integrals, and hence a signature: for a path of bounded variation, $p = 1$, the
extension of its increments is its [signature](../signature-of-a-path/signature.md); for Brownian
motion, $2 < p < 3$, the two levels are the increments and the Lévy area. Fewer levels do not
suffice: given a multiplicative functional of degree $n < \lfloor p \rfloor$ and finite
$p$-variation, an extension of finite $p$-variation, if one exists, need not be unique (Lyons 1998,
Remark 2.2.1(2); compare Chevyrev and Kormilitzin, §1.5.1, for paths of infinite $p$-variation
for every $p < 2$).

Tensor series are given here by their coefficients on words over a finite alphabet $\iota$, and each
tensor level carries the $\ell^1$ norm, an admissible family of tensor norms in Lyons's sense.

## Sources

- T. Lyons, *Differential equations driven by rough signals*, Rev. Mat. Iberoam. 14 (1998),
  Theorem 2.2.1 and Remark 2.2.1(2) (with Definition 2.1.2 and Lemma 2.1.1).
- I. Chevyrev and A. Kormilitzin, *A primer on the signature method in machine learning*,
  arXiv:1603.03788v2, §1.5.1.
- H. Boedihardjo, X. Geng, T. Lyons and D. Yang, *The signature of a rough path: uniqueness*,
  Adv. Math. 293 (2016), arXiv:1406.7871, Proposition 2.1 (the theorem as used for weakly
  geometric rough paths).
