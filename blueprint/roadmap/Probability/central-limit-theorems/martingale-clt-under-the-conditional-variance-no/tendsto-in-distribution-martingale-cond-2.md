# Martingale central limit theorem, Lindeberg form

On a probability space, let $(X_{n,k})$ be a square-integrable array whose row partial sums are martingales for filtrations $(\mathcal F_{n,k})_k$, satisfying the (unconditional) Lindeberg condition for triangular arrays. If the predictable quadratic variation $\sum_{k<n} \mathbb{E}[X_{n,k}^2 \mid \mathcal F_{n,k}]$ tends to $v \ge 0$ in probability, then $\sum_{k<n} X_{n,k}$ converges in distribution to $N(0, v)$. The Lindeberg condition implies the conditional Lindeberg condition, so this is a corollary of the conditional-variance form.

## Sources

- P. Hall and C. C. Heyde, *Martingale Limit Theory and Its Application*, Academic Press (1980), Corollary 3.1, with the remark that the Lindeberg condition implies the conditional one.
- B. M. Brown, "Martingale central limit theorems", Annals of Mathematical Statistics 42 (1971), 59–66.
