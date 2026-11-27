# Martingale CLT under the conditional-variance normalization

On a probability space, let $(X_{n,k})$ be a square-integrable array whose row partial sums $\sum_{j<k} X_{n,j}$ are martingales for filtrations $(\mathcal F_{n,k})_k$, and let $r_n$ be row lengths. If the predictable quadratic variation $\sum_{k<r_n} \mathbb{E}[X_{n,k}^2 \mid \mathcal F_{n,k}]$ tends to $v \ge 0$ in probability and the conditional Lindeberg condition $\sum_{k<r_n} \mathbb{E}[X_{n,k}^2 \mathbf 1\{|X_{n,k}| > \varepsilon\} \mid \mathcal F_{n,k}] \to 0$ in probability holds for every $\varepsilon > 0$, then $\sum_{k<r_n} X_{n,k}$ converges in distribution to $N(0, v)$. Compared with McLeish's form, the realized quadratic variation is replaced by the predictable one and McLeish's maximal-moment condition is not assumed.

The proof cuts each row predictably, keeping increment $k$ while $\sum_{j \le k} \mathbb{E}[X_{n,j}^2 \mid \mathcal F_{n,j}] \le v + 1$, and applies McLeish's theorem to the cut row, which agrees with the original one outside an event of vanishing probability.

## Sources

- B. M. Brown, "Martingale central limit theorems", Annals of Mathematical Statistics 42 (1971), 59–66.
- P. Hall and C. C. Heyde, *Martingale Limit Theory and Its Application*, Academic Press (1980), Corollary 3.1, with a constant limit.
