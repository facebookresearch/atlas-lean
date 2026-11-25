# A fully polynomial-time approximation scheme for knapsack

For the 0–1 knapsack problem with $N$ items of positive integer sizes $s_i$ and nonnegative integer values $v_i$ and capacity $B$, and any rational $0 < \varepsilon \le 1$: discard, in $O(N)$ time, items with $s_i > B$ and items with $v_i = 0$; if none remain, the empty set is optimal (value $0$) and is returned. Otherwise let $n$ be the number of remaining items, $M = \max_i v_i > 0$ and $\mu = \varepsilon M/n$ (rational), round values to $v_i' = \lfloor v_i/\mu \rfloor$ (rounded values $0$ are allowed and the dynamic program treats them like any other value), and solve the rounded instance exactly by dynamic programming over non-dominated (size, value) pairs. The returned set is feasible, has value at least $(1 - \varepsilon)\mathrm{OPT}$, and is found in $O(N + n^3/\varepsilon)$ time; so this is a fully polynomial-time approximation scheme.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- Exact dynamic programming over non-dominated (size, value) pairs for 0–1 knapsack, in time $O(n \min(B, \sum_i v_i))$.

## Background

- [Multiple-choice knapsack problem](../dynamic-programming/multiple-choice-knapsack-problem/README.md): a related exact knapsack dynamic program.

## Sources

- D. P. Williamson and D. B. Shmoys, *The Design of Approximation Algorithms*, Cambridge University Press, 2011, <https://www.designofapproxalgs.com/>, §3.1, Algorithms 3.1–3.2 and Theorems 3.1 and 3.5
