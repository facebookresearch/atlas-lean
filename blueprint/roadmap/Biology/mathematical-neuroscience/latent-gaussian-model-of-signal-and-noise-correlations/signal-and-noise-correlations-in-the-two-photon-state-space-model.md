# Signal and noise correlations in the two-photon state-space model

**Forward model.** For $N$ neurons, $T$ frames and $L$ repeated trials of a stimulus $s_t \in \mathbb{R}^M$, the fluorescence $y_{t,l}$, calcium concentrations $z_{t,l}$ and spikes $n_{t,l} \in \{0,1\}^N$ satisfy

$$y_{t,l} = A z_{t,l} + w_{t,l}, \qquad z_{t,l} = \alpha z_{t-1,l} + n_{t,l},$$

with $w_{t,l}$ i.i.d. $\mathcal N(0,\Sigma_w)$ and $0 \le \alpha < 1$, and

$$n^{(j)}_{t,l} \sim \mathrm{Bernoulli}\big(\lambda^{(j)}_{t,l}\big), \qquad \lambda^{(j)}_{t,l} = \frac{\exp\big(x^{(j)}_{t,l} + d_j^\top s_t\big)}{1 + \exp\big(x^{(j)}_{t,l} + d_j^\top s_t\big)},$$

where $d_j \in \mathbb{R}^M$ is the receptive-field kernel of neuron $j$ and the latent trial-dependent covariates are $x_{t,l} \sim \mathcal N(\mu_x, \Sigma_x)$.

**Correlations.** The *noise covariance* is $\Sigma_x$ and the *signal covariance* is $\Sigma_s = D^\top\operatorname{cov}(s_t,s_t)D$ with $D = [d_1,\dots,d_N]$. The signal and noise correlation matrices are their normalizations

$$S_{ij} = \frac{(\Sigma_s)_{ij}}{\sqrt{(\Sigma_s)_{ii}(\Sigma_s)_{jj}}}, \qquad N_{ij} = \frac{(\Sigma_x)_{ij}}{\sqrt{(\Sigma_x)_{ii}(\Sigma_x)_{jj}}} .$$

**Performance bound (informal).** For a scalar stimulus, i.i.d. latent inputs held constant over windows of $W$ frames and $K$ windows per trial, the maximum likelihood estimators $\hat d$ and $\hat\Sigma_x$ computed from fluorescence satisfy, on an event of probability at least $1-\eta$, bias and variance bounds equal to those of the oracle estimator that observes $x$ directly (of order $1/(KL)$, e.g. $\operatorname{Var}(\hat d_j) \lesssim (\Sigma_x)_{jj}/(KL\sigma_s^2(1-\eta))$), plus excess terms of order $W^{-(1-2\epsilon)}$ (times $\log W$ for $\hat\Sigma_x$) and $O(\sigma_w^2)$, provided $\log W$ exceeds explicit thresholds. So for long windows and low observation noise the estimators approach oracle performance with few trials.

## Expansion

In this model trial-to-trial variability enters only through $x$, so $\Sigma_x$ is the natural noise covariance, while stimulus-locked variability enters through $D^\top s_t$. Conventional correlations of spike counts mix the two through the logistic nonlinearity and need many trials to converge. The bound is proved by showing that on a high-probability event the windowed spike averages stay away from $0$ and $1$, so the truncated inverse logistic map is Lipschitz there; Laplace approximations then compare the maximum likelihood estimators with closed-form oracle estimators up to $O(\sigma_w^2)$ and $O(1/W)$ factors. Estimation in practice uses variational inference with an inverse-Wishart prior on $\Sigma_x$.

## Sources

- A. Rupasinghe, N. Francis, J. Liu, Z. Bowen, P. O. Kanold, B. Babadi, "Direct extraction of signal and noise correlations from two-photon calcium imaging of ensemble neuronal activity", eLife 10 (2021) e68046, Methods ("Proposed forward model"), Theorem 1 and Appendix 2 (Lemmas 1–3), <https://doi.org/10.7554/eLife.68046>, PMCID PMC8354639.
