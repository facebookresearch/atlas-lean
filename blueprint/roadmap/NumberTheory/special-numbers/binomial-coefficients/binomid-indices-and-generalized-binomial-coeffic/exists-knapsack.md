# Partial sums of a lex-minimal extension solve a knapsack problem

Let $m \ge 1$, let
$\eta = (e_1, e_2, \dots)$ be the lex-minimal extension of its first $m$ entries, and write
$S_i = e_1 + \dots + e_i$. Then for every $c \ge 1$ there are nonnegative integers
$n_1, \dots, n_m$ with $\sum_{i=1}^m n_i i = c$ and $S_c = \sum_{i=1}^m n_i S_i$ that solve the
unbounded knapsack problem with values $S_i$, weights $i$ and capacity $c$: all nonnegative
integers $n'_1, \dots, n'_m$ with $\sum_{i=1}^m n'_i i \le c$ satisfy
$\sum_{i=1}^m n'_i S_i \le \sum_{i=1}^m n_i S_i$.

## Sources

- Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113, Proposition 2.
