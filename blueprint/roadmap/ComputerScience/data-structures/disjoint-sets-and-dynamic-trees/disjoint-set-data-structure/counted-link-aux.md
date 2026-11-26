# Linking by rank with operation counts

Given an array $A$ of union-find nodes, each
storing a parent index and a rank, and indices $x, y$ of $A$, this computation returns an array
together with a count $(t, p, w)$ of rank tests $t$, parent writes $p$ and rank writes $w$. If
$x = y$ it returns $A$ with count $(0, 0, 0)$. Otherwise it makes one rank test; if the rank of $y$
is less than the rank of $x$, it sets the parent of $y$ to $x$ (one parent write). If not, it sets
the parent of $x$ to $y$ (one parent write) and makes a second rank test, and if the ranks of $x$
and $y$ are equal it also increases the rank of $y$ by one (one rank write).

The equality test $x = y$ is not counted as a rank test.
