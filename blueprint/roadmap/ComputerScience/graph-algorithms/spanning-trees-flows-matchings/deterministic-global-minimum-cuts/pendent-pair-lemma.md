# The last vertex of an MA ordering is a minimum cut for the pendent pair

If $(s, t) = (v_{n-1}, v_n)$ is the pendent pair of an MA ordering of a weighted graph (or of a symmetric submodular function $f$), then $\{t\}$ is a minimum $t$-$s$ cut: $f(\{t\}) \le f(X)$ for every $X$ with $t \in X$, $s \notin X$. Consequently the global minimum of $f$ over nontrivial subsets equals the minimum of $f(\{t\})$ and the global minimum of the function obtained by merging $s$ and $t$.

## Proof sketch

Stoer and Wagner prove by induction along the ordering that for each prefix the cut of the phase is at most the restriction of any cut separating the current vertex from its predecessor; for symmetric submodular functions, Queyranne's posimodularity argument gives the same inequality.

## Depends on

- [Maximum adjacency orderings](maximum-adjacency-ordering.md)

## Sources

- M. Stoer and F. Wagner, "A Simple Min-Cut Algorithm", Journal of the ACM 44(4), 1997.
- M. Queyranne, "Minimizing Symmetric Submodular Functions", Mathematical Programming 82, 1998.
