# The Hilbert symbol and norms from a quadratic extension

Let $K$ be a field in which $2 \neq 0$, such as $\mathbb{R}$ or $\mathbb{Q}_p$ for a prime $p$, let
$a, b \in K^\times$, and let $(a, b)_K$ be the Hilbert symbol of $K$: $1$ if $a x^2 + b y^2 = 1$ has a
solution in $K$, and $-1$ otherwise. Let $\beta$ be an element with $\beta^2 = b$ of a field extension
$L$ of $K$, so that the subfield $K(\beta)$ of $L$ is $K(\sqrt b)$. Then $(a, b)_K = 1$ if and only if
$a$ is the norm $N_{K(\beta)/K}(\xi)$ of some nonzero $\xi \in K(\beta)$. Explicitly, $(a, b)_K = 1$ if
and only if $a = z^2 - b y^2$ for some $y, z \in K$; and if $b$ is a square in $K$, then $(a, b)_K = 1$
for every $a$.

Write $F(z, x, y) = z^2 - a x^2 - b y^2$; every triple below is in the order $(z, x, y)$. For nonzero
$a, b$ the symbol is $1$ exactly when $F$ has a nonzero zero in $K^3$: a solution $(x, y)$ of
$a x^2 + b y^2 = 1$ gives the zero $(1, x, y)$, and a nonzero zero with $z = 0$ makes $a x^2 + b y^2$ a
hyperbolic plane, which takes the value $1$. With this description the proof is short. If $b = c^2$,
$F$ has the zero $(c, 0, 1)$, and $K(\beta) = K$, where every $a$ is a norm. Otherwise $1, \beta$ is a
basis of $K(\beta)$ over $K$, in which the norm of $z + y \beta$ is $z^2 - b y^2$. If
$a = z^2 - b y^2$, $F$ has the zero $(z, 1, y)$; conversely, a nonzero zero $(z, x, y)$ of $F$ has
$x \neq 0$, as $b$ is not a square, and then $a$ is the norm of $z/x + (y/x)\beta$.

## Sources

- J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973: Chapter III,
  §1.1, Proposition 1 and its proof, p. 19, for the symbol defined by nonzero zeros of
  $z^2 - a x^2 - b y^2$. Serre takes $K = \mathbb{R}$ or $\mathbb{Q}_p$; the proof uses only $2 \neq 0$.
