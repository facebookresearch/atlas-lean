# Online Hellinger estimation for finite model classes by tempered aggregation

For a finite model class $\mathcal{M}$ with densities bounded away from zero (or after mixing with a small uniform component), the exponential-weights estimator that, at each round, predicts the posterior-tempered mixture $\hat M_t = \sum_M w_t(M)\,M$ with weights proportional to $\exp\big(\eta\sum_{s < t}\log M(\pi_s)(r_s, o_s)\big)$ and $\eta = 1/2$ achieves

$$
\mathrm{Est}_H = \sum_{t=1}^T \mathbb{E}_{\pi_t \sim p_t} D_H^2\big(M^\star(\pi_t), \hat M_t(\pi_t)\big) \le O\big(\log(|\mathcal{M}|/\delta)\big)
$$

with probability at least $1-\delta$, for every adaptively chosen sequence of decisions; the estimates lie in the convex hull of $\mathcal{M}$.

## Proof sketch

With $\eta = 1/2$, the tempered log-likelihood ratio of $\hat M_t$ against $M^\star$ is a supermartingale whose expected increment is $-\log(1 - D_H^2/2) \ge D_H^2/2$ (the Bhattacharyya coefficient appears because of the square root). Summing over rounds, the cumulative Hellinger error is bounded by the log of the prior mass of $M^\star$, namely $\log|\mathcal{M}|$, plus a martingale deviation term of order $\log(1/\delta)$ by Freedman's inequality.

## Depends on

- [Estimation-to-decisions meta-algorithm](estimation-to-decisions.md)
- [Hellinger distance](../../../../Probability/convergence-of-measures/hellinger-distance/hellinger-dist.md)

## Sources

- D. J. Foster, S. M. Kakade, J. Qian, A. Rakhlin, "The Statistical Complexity of Interactive Decision Making", arXiv:2112.13487 (2021).
