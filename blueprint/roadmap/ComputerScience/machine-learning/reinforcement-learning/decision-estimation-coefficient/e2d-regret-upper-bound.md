# Estimation-to-decisions regret is bounded by the DEC plus the estimation error

For every $\gamma > 0$, the E2D algorithm satisfies

$$
\mathbb{E}[\mathrm{Reg}_T] \le T\cdot \sup_{\bar M} \mathrm{dec}_\gamma(\mathcal{M}, \bar M) + \gamma\cdot \mathbb{E}[\mathrm{Est}_H],
$$

where the supremum ranges over the possible oracle outputs. For a finite model class, an online estimator based on exponential weights with the log loss (tempered aggregation) achieves $\mathbb{E}[\mathrm{Est}_H] \le O(\log|\mathcal{M}|)$ with proper or convex-hull estimates, so that

$$
\mathbb{E}[\mathrm{Reg}_T] \le O\Big(\inf_{\gamma > 0}\big\{T\cdot\mathrm{dec}_\gamma(\mathrm{co}(\mathcal{M})) + \gamma\log|\mathcal{M}|\big\}\Big).
$$

## Proof sketch

At round $t$, by the choice of $p_t$ and since $M^\star \in \mathcal{M}$, the instantaneous regret $\mathbb{E}_{\pi \sim p_t}[f^{M^\star}(\pi_{M^\star}) - f^{M^\star}(\pi)]$ is at most $\mathrm{dec}_\gamma(\mathcal{M}, \hat M_t) + \gamma\,\mathbb{E}_{\pi \sim p_t} D_H^2(M^\star(\pi), \hat M_t(\pi))$. Summing over $t$ gives the first bound. For finite classes, the Hellinger error of exponential weights under log loss is bounded by its log-loss regret, which is at most $\log|\mathcal{M}|$, using that the Hellinger distance is dominated by the Kullback–Leibler divergence.

## Depends on

- [Estimation-to-decisions meta-algorithm](estimation-to-decisions.md)
- [Decision-estimation coefficient](decision-estimation-coefficient.md)

## Proof depends on

- [Online Hellinger estimation for finite model classes by tempered aggregation](tempered-aggregation-hellinger-estimation.md)

## Sources

- D. J. Foster, S. M. Kakade, J. Qian, A. Rakhlin, "The Statistical Complexity of Interactive Decision Making", arXiv:2112.13487 (2021).
