# Uncrossing minimum cuts of symmetric submodular functions

Let $f$ be symmetric and submodular. If $X$ is a minimum $s$-$t$ cut and $Y$ is a minimum $u$-$v$ cut, then (depending on which sides contain $s$, $t$, $u$, $v$) one of $X \cap Y$, $X \cup Y$, $X \setminus Y$, $Y \setminus X$ is again a minimum cut for the corresponding pair; in particular, a minimum $u$-$v$ cut can always be chosen so that it does not cross a given minimum $s$-$t$ cut $X$. Moreover if $X$ separates $u$ from $v$ then $\lambda_f(u, v) \le f(X)$, and the complement of a minimum $s$-$t$ cut is a minimum $t$-$s$ cut.

## Proof sketch

Submodularity $f(X \cap Y) + f(X \cup Y) \le f(X) + f(Y)$ and its symmetric form (posimodularity) $f(X \setminus Y) + f(Y \setminus X) \le f(X) + f(Y)$; each of the two sets on the left is a candidate cut for one pair, so both must be minimum.

## Depends on

- [Minimum s-t cuts of a set function](minimum-cuts-of-a-set-function.md)

## Sources

- R. E. Gomory and T. C. Hu, "Multi-Terminal Network Flows", Journal of the Society for Industrial and Applied Mathematics 9(4), 1961.
- A. Schrijver, "Combinatorial Optimization: Polyhedra and Efficiency", Springer, 2003.
