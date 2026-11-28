# Signal and noise correlations in the two-photon state-space model

**Forward model.** For $N$ neurons, $T$ frames and $L$ repeated trials of a stimulus $s_t \in \mathbb{R}^M$, the fluorescence $y_{t,l}$, calcium concentrations $z_{t,l}$ and spikes $n_{t,l} \in \{0,1\}^N$ satisfy

$$y_{t,l} = A z_{t,l} + w_{t,l}, \qquad z_{t,l} = \alpha z_{t-1,l} + n_{t,l},$$

with $w_{t,l}$ i.i.d. $\mathcal N(0,\Sigma_w)$ and $0 \le \alpha < 1$, and

$$n^{(j)}_{t,l} \sim \mathrm{Bernoulli}\big(\lambda^{(j)}_{t,l}\big), \qquad \lambda^{(j)}_{t,l} = \frac{\exp\big(x^{(j)}_{t,l} + d_j^\top s_t\big)}{1 + \exp\big(x^{(j)}_{t,l} + d_j^\top s_t\big)},$$

where $d_j \in \mathbb{R}^M$ is the receptive-field kernel of neuron $j$ and the latent trial-dependent covariates are $x_{t,l} \sim \mathcal N(\mu_x, \Sigma_x)$.

**Correlations.** The *noise covariance* is $\Sigma_x$ and the *signal covariance* is $\Sigma_s = D^\top\operatorname{cov}(s_t,s_t)D$ with $D = [d_1,\dots,d_N]$. Here $\operatorname{cov}(u_t,v_t) = \frac1T\sum_{t=1}^T\big(u_t - \frac1T\sum_{t'}u_{t'}\big)\big(v_t - \frac1T\sum_{t'}v_{t'}\big)^\top$ is the empirical covariance over the $T$ frames (the stimulus is a fixed, repeated sequence). When the diagonal entries of $\Sigma_s$ and $\Sigma_x$ are positive, the signal and noise correlation matrices are their normalizations

$$S_{ij} = \frac{(\Sigma_s)_{ij}}{\sqrt{(\Sigma_s)_{ii}(\Sigma_s)_{jj}}}, \qquad N_{ij} = \frac{(\Sigma_x)_{ij}}{\sqrt{(\Sigma_x)_{ii}(\Sigma_x)_{jj}}} .$$

## Expansion

In this model trial-to-trial variability enters only through $x$, so $\Sigma_x$ is the natural noise covariance, while stimulus-locked variability enters through $D^\top s_t$. Conventional correlations of spike counts mix the two through the logistic nonlinearity and need many trials to converge. For a scalar stimulus and latent inputs held constant over windows of frames, the source's Theorem 1 bounds the bias and variance of the maximum likelihood estimators of $d_j$ and $\Sigma_x$ from fluorescence by those of an oracle estimator that observes $x$ directly plus excess terms that vanish for long windows and low observation noise. Estimation in practice uses variational inference with an inverse-Wishart prior on $\Sigma_x$.

## Sources

- A. Rupasinghe, N. Francis, J. Liu, Z. Bowen, P. O. Kanold, B. Babadi, "Direct extraction of signal and noise correlations from two-photon calcium imaging of ensemble neuronal activity", eLife 10 (2021) e68046, Methods ("Proposed forward model"), Theorem 1 and Appendix 2 (Lemmas 1–3), <https://doi.org/10.7554/eLife.68046>, PMCID PMC8354639.
