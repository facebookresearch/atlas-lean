# Hoey–Sloane words with permuted digits are unions of cycles

Let $n \ge 1$ and $b \ge 2$
be natural numbers, and let $s = (d_0, \hat d_0) \cdots (d_k, \hat d_k)$ be an input string in
the language $L$ of the $(n, b)$-Hoey–Sloane machine such that $\hat d_j = d_{\sigma(j)}$ for all
$j$, for some permutation $\sigma$ of $\{0, \dots, k\}$. Let
$E = \{(d_j, \hat d_j) : 0 \le j \le k\}$ be the set of inputs of $s$. Then every $e \in E$ lies
on a directed cycle with edges in $E$: there are $m \ge 0$ and pairwise distinct natural numbers
$v_0, \dots, v_m$ such that $(v_i, v_{i+1}) \in E$ for all $0 \le i \le m$, with indices taken
modulo $m + 1$, and $e = (v_i, v_{i+1})$ for some $i$.

## Sources

- B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25 (2025), Article A13, Corollary 1 (`integers-2025-A13-cor-1`).
