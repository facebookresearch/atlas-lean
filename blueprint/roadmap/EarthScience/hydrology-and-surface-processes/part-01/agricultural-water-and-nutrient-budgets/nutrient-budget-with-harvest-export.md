# Nutrient budget with harvest export

For a field nutrient stock with nonnegative inputs $a_k$, losses $\ell_k$ and harvest export $e_k$ in season $k$, the stock evolves as
$N_{k+1}=N_k+a_k-\ell_k-e_k$. Starting from $N_0\ge0$, the stock remains nonnegative through season $m$ exactly when
$N_0+\sum_{k<j}a_k\ge\sum_{k<j}(\ell_k+e_k)$ for every $0\le j\le m$: initial stock plus cumulative inputs must cover
cumulative removals at every prefix. Harvest export
removes nutrient from the field, so a closed recycling budget with constant stock fails when harvest is exported without matching
inputs: $N_0 = 10$, $a_0 = \ell_0 = 0$ and $e_0 = 2$ give $N_1 = 8$. Soil chemistry is outside this result.

## Depends on

## Proof depends on

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 4.3, Equation 4.36, the species balance with accumulation, flows and production (p. 127).
