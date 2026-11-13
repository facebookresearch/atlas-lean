# Partial-sum criterion for lex-minimal extensions

Let $k \ge 1$, let
$\eta = (e_1, e_2, \dots)$ be a sequence of nonnegative integers and write
$S_i = e_1 + \dots + e_i$. Suppose $S_i + S_j \le S_{i+j}$ for all $i, j \ge 1$ with
$i + j \le k$. Then $\eta$ is the lex-minimal extension of $(e_1, \dots, e_k)$ if and only if,
for every $r > k$, $S_i + S_j \le S_r$ for all $i, j \ge 1$ with $i + j = r$, with equality for
at least one such pair $(i, j)$.

In the paper's notation, the condition says that $\Delta_\eta(r) = 0$ for every $r > k$, where
$\Delta_\eta(r) = \min \{S_r - S_i - S_j : i + j = r,\ i, j \ge 1\}$.

## Sources

- Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113, Proposition 1.
