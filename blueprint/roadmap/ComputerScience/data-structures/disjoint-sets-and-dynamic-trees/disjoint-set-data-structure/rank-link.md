# Ranks after linking in a union-find structure

Let $S$ be a union-find structure, write
$\rho(i)$ for the rank of $i$ in $S$ ($0$ if $i$ is not a node of $S$), and let $x, y$ be nodes of
$S$ such that $y$ is a root, that is, the parent of $y$ is $y$. Let $S'$ be the result of linking
$x$ and $y$ by rank. Then for every natural number $i$, the rank of $i$ in $S'$ is $\rho(y) + 1$
if $x \ne y$, $\rho(x) = \rho(y)$ and $i = y$, and is $\rho(i)$ otherwise.
