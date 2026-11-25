# Linear recycle networks

Consider a steady, nonreactive finite network of process units, with the flows of one species in common units. For an edge
$e = (j \to i)$, unit $j$ returns the fraction $r_e \ge 0$ of its throughput $x_j$ to unit $i$; the fractions leaving each unit
add up to at most $1$, and the remainder of each unit's throughput leaves through its terminal product or purge port. Let
$f \in \mathbb{R}^n_{\ge 0}$ be the fresh feeds and $K_{ij} = \sum_{e = (j \to i)} r_e$. Then:

1. the unit balances are equivalent to $x = f + Kx$;
2. if the spectral radius of $K$ is below $1$, then $I - K$ is invertible, $x = (I - K)^{-1} f$ is the unique solution, and
   $x \ge 0$ because $(I - K)^{-1}$ has nonnegative entries;
3. the terminal flows add up to the fresh feed: $\sum_j \bigl(1 - \sum_{e \text{ from } j} r_e\bigr) x_j = \sum_i f_i$.

Part 3 follows by summing $x - Kx = f$, since the column sums of $K$ are the fractions returned by each unit. The condition on the
spectral radius is sufficient, not necessary, for a particular feed to admit a nonnegative solution.

## Depends on

## Proof depends on

- [Invertibility of 1 − K when the spectral radius is below one](../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-unit-one-sub-of-spectral-radius-lt-on.md)
- [Neumann series](../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/inv-one-sub-nonneg.md), for nonnegativity

## Sources

- *Introduction to Chemical Engineering Processes*, Wikibooks, chapter "How to Analyze a Recycle System" (splitter balances with equal composition of the outlets), <https://en.wikibooks.org/wiki/Introduction_to_Chemical_Engineering_Processes/How_to_Analyze_a_Recycle_System>.
