# Estimation-to-decisions regret is bounded by the DEC plus the estimation error

For every $\gamma > 0$ and every online estimation oracle with estimates in a class $\widehat{\mathcal{M}}$, the E2D algorithm with parameter $\gamma$ satisfies, for every realization,

$$
\mathrm{Reg}_T \le \sum_{t=1}^T \mathrm{dec}_\gamma(\mathcal{M}, \hat M_t) + \gamma\cdot \mathrm{Est}_H \le T\cdot \sup_{\bar M \in \widehat{\mathcal{M}}} \mathrm{dec}_\gamma(\mathcal{M}, \bar M) + \gamma\cdot \mathrm{Est}_H .
$$

For a finite model class, averaged exponential weights with the logarithmic loss is an oracle with estimates in $\widehat{\mathcal{M}} = \mathrm{co}(\mathcal{M})$ and $\mathrm{Est}_H \le \log|\mathcal{M}| + 2\log(1/\delta)$ with probability at least $1 - \delta$, so that for each $\gamma > 0$, with probability at least $1 - \delta$,

$$
\mathrm{Reg}_T \le T\cdot\mathrm{dec}_\gamma(\mathcal{M}) + \gamma\big(\log|\mathcal{M}| + 2\log(1/\delta)\big),
$$

where $\mathrm{dec}_\gamma(\mathcal{M}) = \sup_{\bar M \in \mathrm{co}(\mathcal{M})} \mathrm{dec}_\gamma(\mathcal{M}, \bar M)$.

## Proof sketch

At round $t$, by the choice of $p_t$ and since $M^\star \in \mathcal{M}$, the instantaneous regret $\mathbb{E}_{\pi \sim p_t}[f^{M^\star}(\pi_{M^\star}) - f^{M^\star}(\pi)]$ is at most $\mathrm{dec}_\gamma(\mathcal{M}, \hat M_t) + \gamma\,\mathbb{E}_{\pi \sim p_t} D_H^2(M^\star(\pi), \hat M_t(\pi))$. Summing over $t$ gives the first bound, and $\hat M_t \in \widehat{\mathcal{M}}$ gives the second. The finite-class bound plugs in the estimation guarantee of exponential weights.

## Depends on

- [Estimation-to-decisions meta-algorithm](estimation-to-decisions.md)
- [Decision-estimation coefficient](decision-estimation-coefficient.md)

## Proof depends on

- [Online Hellinger estimation for finite model classes by exponential weights with the logarithmic loss](tempered-aggregation-hellinger-estimation.md)

## Sources

- D. J. Foster, A. Rakhlin, "Foundations of Reinforcement Learning and Interactive Decision Making", lecture notes, revised edition (September 2026), arXiv:2312.16730v2, Section 7.4 (Theorem 7.1 and Eq. (7.23)).
