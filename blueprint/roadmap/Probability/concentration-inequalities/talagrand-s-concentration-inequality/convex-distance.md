# Talagrand's convex distance

For $A \subseteq \Omega^N$ and $x \in \Omega^N$, $f_c(A, x)$ is the Euclidean distance from $0$ to
the convex hull $V_A(x)$ of $U_A(x)$ in $\mathbb{R}^N$. For nonempty $A$, by duality (Lemma 4.1.2 of
the source), $f_c(A, x) \le t$ means that for every nonnegative weight vector $\alpha$ some $y \in A$ differs
from $x$ on a set of coordinates of $\alpha$-weight at most $t\,\|\alpha\|_2$: one distance
controls all weighted Hamming distances at once.

When $A$ is empty, $V_A(x)$ is empty and the distance is taken to be $0$, while the source's
distance is $+\infty$; the convex-distance inequality is unaffected, its right-hand side
$1/P(\emptyset)$ being $+\infty$.

## Background

- [Talagrand's set $U_A(x)$](convex-support.md): the set whose convex hull defines the distance.

## Sources

- M. Talagrand, *Concentration of measure and isoperimetric inequalities in product spaces*,
  Publications Mathématiques de l'IHÉS 81 (1995), 73–205, Section 4.1.
