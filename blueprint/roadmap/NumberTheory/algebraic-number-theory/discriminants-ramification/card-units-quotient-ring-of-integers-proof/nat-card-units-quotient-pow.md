# Number of units modulo a power of a prime ideal

Let $S$ be a Dedekind domain that is a
finite free $\mathbb{Z}$-module (for example the ring of integers $\mathcal{O}_K$ of a number
field $K$), and for a nonzero ideal $\mathfrak{b}$ let $N(\mathfrak{b}) = \#(S/\mathfrak{b})$
be its absolute norm (`Ideal.absNorm`). If $\mathfrak{p}$ is a nonzero prime ideal of $S$ and
$k \ge 1$, then the unit group of $S/\mathfrak{p}^k$ has
$N(\mathfrak{p})^k - N(\mathfrak{p})^{k-1}$ elements (`Nat.card`; the ring $S/\mathfrak{p}^k$ is
finite).

Keune states this for $\mathcal{O}_K$ as $N(\mathfrak{p})^k (1 - 1/N(\mathfrak{p}))$ (F. Keune,
*Number Fields*, 2023, Chapter 6, Exercise 1(ii), p. 141); the two agree as
$N(\mathfrak{p}) \ge 1$. The ring is any Dedekind domain that is a finite free
$\mathbb{Z}$-module.
