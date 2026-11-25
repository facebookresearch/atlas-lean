# Talagrand's concentration inequality around a median

There are absolute constants $C, c > 0$ with the following property. Let $K > 0$, let
$X_1, \dots, X_n$ be independent real random variables with $|X_i| \le K$, let
$F : \mathbb{R}^n \to \mathbb{R}$ be convex and $1$-Lipschitz for the Euclidean metric, and let $m$
be a median of $F(X)$, where $X = (X_1, \dots, X_n)$. Then

$$\mathbb{P}\big(|F(X) - m| \ge \lambda K\big) \le C e^{-c\lambda^2} \quad \text{for every }
\lambda > 0.$$

The constants depend on neither $n$, $K$, $F$ nor the laws of the $X_i$.

Tao states the theorem for complex variables and $F : \mathbb{C}^n \to \mathbb{R}$, identifying
$\mathbb{C}^n$ with $\mathbb{R}^{2n}$; the real case follows by composing $F$ with
$z \mapsto \operatorname{Re} z$. His "for any $\lambda$" means $\lambda > 0$: for $\lambda < 0$ the
event is certain while the bound tends to $0$.

## Background

- [McDiarmid's inequality](../mcdiarmid-s-inequality/README.md): background; for a $1$-Lipschitz
  $F$ the bounded-differences inequality gives fluctuations of order $\sqrt{n}\,K$, while
  convexity brings them down to $O(K)$.
- [Talagrand's convex-distance inequality](lintegral-exp-convex-distance-sq-le.md): background;
  the product-space inequality of Talagrand's 1995 paper, cited in the sources, for the convex
  distance to a set.

## Sources

- T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, American Mathematical Society, 2012, Theorem 2.1.13, inequality (2.18).
- M. Talagrand, "Concentration of measure and isoperimetric inequalities in product spaces",
  Publ. Math. IHÉS 81 (1995), 73–205.
