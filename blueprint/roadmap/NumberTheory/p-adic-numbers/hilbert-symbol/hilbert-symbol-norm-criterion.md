# The Hilbert symbol and norms from a quadratic extension

Let $K$ be the field $\mathbb{R}$ or the field $\mathbb{Q}_p$ for a prime $p$, let $a, b \in K^\times$,
and let $(a, b)_K$ be the Hilbert symbol of $K$: $1$ if $a x^2 + b y^2 = 1$ has a solution in $K$, and
$-1$ otherwise. Then $(a, b)_K = 1$ if and only if $a$ is a norm from $K(\sqrt b)$: if $b$ is a square
in $K$, every $a$ is; if $b$ is not a square, $a = z^2 - b y^2$ for some $y, z \in K$, the norm of
$z + y\sqrt b$.

Write $F(z, x, y) = z^2 - a x^2 - b y^2$; every triple below is in the order $(z, x, y)$. For nonzero
$a, b$ the symbol is $1$ exactly when $F$ has a nonzero zero in $K^3$: a solution $(x, y)$ of
$a x^2 + b y^2 = 1$ gives the zero $(1, x, y)$, and a nonzero zero with $z = 0$ makes $a x^2 + b y^2$ a
hyperbolic plane, which takes the value $1$. With this description the proof is short. If $b = c^2$,
$F$ has the zero $(c, 0, 1)$. Otherwise, if $a = z^2 - b y^2$, $F$ has the zero $(z, 1, y)$;
conversely, a nonzero zero $(z, x, y)$ of $F$ has $x \neq 0$, as $b$ is not a square, and then $a$ is
the norm of $z/x + (y/x)\sqrt b$.

## Depends on

- [The $p$-adic Hilbert symbol](padic-hilbert-symbol.md), for $(a, b)_K$ when $K = \mathbb{Q}_p$
- [Real Hilbert symbol](real-hilbert-symbol.md), for $(a, b)_K$ when $K = \mathbb{R}$

## Proof depends on

Its proof is the short argument above, which uses no other result.

## Sources

- J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973: Chapter III,
  §1.1, Proposition 1 and its proof, p. 19, for the symbol defined by nonzero zeros of
  $z^2 - a x^2 - b y^2$.
