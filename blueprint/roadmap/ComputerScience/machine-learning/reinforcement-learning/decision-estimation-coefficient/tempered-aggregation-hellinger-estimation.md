# Online Hellinger estimation for finite model classes by exponential weights with the logarithmic loss

Let $\mathcal{M}$ be a finite model class containing $M^\star$, and write $m_M(r, o \mid \pi)$ for the conditional density of $(r, o)$ under $M(\pi)$. The averaged exponential weights estimator for the logarithmic loss $\ell^t_{\log}(M) = \log\big(1/m_M(r_t, o_t \mid \pi_t)\big)$ predicts the mixture $\hat M_t = \sum_{M} w_t(M)\,M$ with weights $w_t(M) \propto \prod_{s < t} m_M(r_s, o_s \mid \pi_s)$ (the Bayesian posterior under the uniform prior). Its log-loss regret against the best model in $\mathcal{M}$ is at most $\log|\mathcal{M}|$, and consequently, for every adaptively chosen sequence of decision distributions $p_t$,

$$
\mathbb{E}[\mathrm{Est}_H] \le \log|\mathcal{M}| \qquad\text{and}\qquad \mathrm{Est}_H = \sum_{t=1}^T \mathbb{E}_{\pi_t \sim p_t} D_H^2\big(M^\star(\pi_t), \hat M_t(\pi_t)\big) \le \log|\mathcal{M}| + 2\log(1/\delta)
$$

with probability at least $1-\delta$, where $D_H^2(P, Q) = \int \big(\sqrt{dP/d\nu} - \sqrt{dQ/d\nu}\big)^2\, d\nu = 2\, d_{\mathrm{Hell}}(P, Q)^2$ is the unnormalized squared Hellinger distance, twice the square of the linked Hellinger distance $d_{\mathrm{Hell}}$; the estimates lie in the convex hull of $\mathcal{M}$.

## Proof sketch

The log-loss regret of the Bayesian mixture is at most $-\log w_1(M^\star) = \log|\mathcal{M}|$, since the mixture's cumulative likelihood is at least $w_1(M^\star)$ times that of $M^\star$. Under realizability, the expected log-loss regret dominates the expected cumulative Kullback–Leibler divergence $\sum_t \mathbb{E}_{\pi_t \sim p_t} D_{\mathrm{KL}}(M^\star(\pi_t) \,\|\, \hat M_t(\pi_t))$, which dominates the Hellinger estimation error. The high-probability bound uses the moment generating function of the log-likelihood ratio, whose square root has conditional expectation equal to the Bhattacharyya coefficient $\int \sqrt{dP\,dQ} = 1 - D_H^2/2 = 1 - d_{\mathrm{Hell}}^2$, so the deviation term is $2\log(1/\delta)$ regardless of $T$.

## Depends on

- [Estimation-to-decisions meta-algorithm](estimation-to-decisions.md)
- [Hellinger distance](../../../../Probability/convergence-of-measures/hellinger-distance/hellinger-dist.md)

## Sources

- D. J. Foster, A. Rakhlin, "Foundations of Reinforcement Learning and Interactive Decision Making", lecture notes, revised edition (September 2026), arXiv:2312.16730v2, Section 7.4.1 (Lemma 7.3 and the averaged exponential weights example following it).
