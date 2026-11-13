# Ranks after a union

Let $S$ be a union-find structure, write $\rho(i)$ for the rank of
$i$ in $S$ ($0$ if $i$ is not a node of $S$) and $r(i)$ for the root of $i$ in $S$. For nodes
$x, y$ of $S$ and every natural number $i$, the rank of $i$ in the union of $x$ and $y$ in $S$
(union by rank with path compression) is $\rho(r(y)) + 1$ if $r(x) \ne r(y)$,
$\rho(r(x)) = \rho(r(y))$ and $r(y) = i$, and is $\rho(i)$ otherwise.
