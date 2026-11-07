# Determinants of logarithms in a split Thue family

Let $(d, G, \gamma, \delta)$ be a
split Thue recurrence family, let $\alpha_i(n)$ ($i, n \in \mathbb{N}$) be reals for which there
is $N$ such that for all $n \ge N$ and $1 \le i \le d$,
$\prod_{l=1}^{d} (\alpha_i(n) - G_l(n)) = 1$ and $|\alpha_i(n) - G_i(n)| < 1$, and let
$1 \le k \le d - 1$. Let $B_k(n)$ be the $k \times k$ matrix with entries
$\log |\alpha_i(n) - G_j(n)|$ for $1 \le i, j \le k$, where $\log 0 = 0$. Then there are
$c_1 > 0$, $c_2 > 0$ and $N'$ such that $c_1 n^k \le |\det B_k(n)| \le c_2 n^k$ for all
$n \ge N'$.

## Sources

- Tobias Hilgart, *On Split Families of Thue Equations with Linear Recurrence Sequences as Factors*, INTEGERS 25 (2025), Article A35, Lemma 3 (`integers-2025-A35-lem-3`). `Real.log` is the logarithm of the absolute value; `Θ` is the paper's two-sided bound `c₁ n ^ k ≤ |det B_k| ≤ c₂ n ^ k` for large `n`.
