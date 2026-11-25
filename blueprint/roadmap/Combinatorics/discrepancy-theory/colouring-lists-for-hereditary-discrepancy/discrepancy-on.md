# Discrepancy of a matrix on a set of columns

For a real $n \times m$ matrix $A$ and a set
$S$ of columns of $A$, the discrepancy of $A$ on $S$ is the minimum, over all sign vectors
$\varepsilon \in \{-1, 1\}^m$, of $\max_i \left|\sum_{j \in S} A_{ij} \varepsilon_j\right|$, the
largest absolute value of a row sum of $A$ restricted to $S$ and weighted by $\varepsilon$
(taken to be $0$ when $A$ has no rows).
