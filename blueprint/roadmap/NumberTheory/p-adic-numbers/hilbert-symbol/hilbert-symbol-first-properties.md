# First properties of the Hilbert symbol

Let $K$ be a field in which $2 \neq 0$, such as $\mathbb{R}$ or $\mathbb{Q}_p$ for a prime $p$, and let
$(a, b)$ be the Hilbert symbol of $K$: for $a, b \in K^\times$, $1$ if $a x^2 + b y^2 = 1$ has a
solution in $K$, and $-1$ otherwise. For $a, a', b, c \in K^\times$, with $a \neq 1$ wherever $1 - a$
appears:

1. $(a, b) = (b, a)$ and $(a, c^2) = 1$;
2. $(a, -a) = 1$ and $(a, 1 - a) = 1$;
3. if $(a, b) = 1$, then $(a a', b) = (a', b)$;
4. $(a, b) = (a, -ab) = (a, (1 - a) b)$.

Write $F(z, x, y) = z^2 - a x^2 - b y^2$; triples below are in the order $(z, x, y)$. Part 1 is clear
from the description of the symbol by nonzero zeros of $F$. For part 2, $F$ has the zero $(0, 1, 1)$
when $b = -a$ and $(1, 1, 1)$ when $b = 1 - a$. For part 3,
$(a, b) = 1$ puts $a$ in the group of norms from $K(\sqrt b)$, so $a'$ is a norm exactly when $a a'$ is.
Part 4 follows from parts 1–3.

## Sources

- J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973: Chapter III,
  §1.1, Proposition 2 and its proof, pp. 19–20. Serre takes $K = \mathbb{R}$ or $\mathbb{Q}_p$; the proof
  uses only $2 \neq 0$.
