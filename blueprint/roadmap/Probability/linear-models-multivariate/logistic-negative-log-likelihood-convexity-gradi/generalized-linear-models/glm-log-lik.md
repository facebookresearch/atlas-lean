# Log-likelihood of a canonical-link generalized linear model

Let $(\Theta, b, \mu, V)$ be a canonical cumulant specification: an open convex natural-parameter domain $\Theta \subseteq \mathbb{R}$, a cumulant $b$ with $b' = \mu$ and $\mu' = V \ge 0$ on $\Theta$. For a design $X$, offset $o$, responses $y$ and dispersion $\varphi > 0$, the log-likelihood objective is

$$\ell(\beta) = \frac1\varphi\sum_i\big(y_i\eta_i(\beta) - b(\eta_i(\beta))\big), \qquad \eta(\beta) = X\beta + o,$$

which for an exponential family with log-partition $b$ is the log-likelihood up to a term free of $\beta$.
