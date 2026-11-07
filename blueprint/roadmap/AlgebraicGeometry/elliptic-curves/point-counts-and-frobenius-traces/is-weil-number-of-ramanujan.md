# Ramanujan graphs give Weil numbers

Let $q$ be a natural number and let $A$ be a symmetric
$n \times n$ matrix with integer entries such that every complex root $\mu \ne q + 1$ of its
characteristic polynomial satisfies $|\mu| \le 2\sqrt{q}$. Let $\mu \ne q + 1$ be a complex root
of the characteristic polynomial of $A$ and let $\alpha \in \mathbb{C}$ satisfy
$\alpha^2 - \mu\alpha + q = 0$. Then $\alpha$ is an algebraic integer, and every complex root of
the minimal polynomial of $\alpha$ over $\mathbb{Q}$ has absolute value $\sqrt{q}$; that is,
$\alpha$ is a Weil $q$-number.

When $A$ is the adjacency matrix of a $(q + 1)$-regular graph $X$, the hypothesis says that $X$ is
Ramanujan, and the numbers $\alpha$ are the inverse roots of
$P_X(u) = \prod_{\mu \ne q + 1} (1 - \mu u + q u^2)$. The paper takes $q = p^a$ and $X$
connected; neither assumption is needed.

## Sources

- Daniel Vallières, *Elliptic Curves over Finite Fields and Ramanujan Graphs on Two Vertices*, INTEGERS 24 (2024), Article A8, Proposition 1 (`integers-2024-A8-prop-1`).
