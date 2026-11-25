# Polynomial sampling guarantees for score-based diffusion models

This node collects the convergence guarantee of Chen et al. for score-based diffusion sampling.

## Expansion

A sound expansion has separate pages for:

1. **Model.** The forward process (an Ornstein–Uhlenbeck diffusion from the data distribution), the
   discretized reverse process with step size and horizon, its initialization at the stationary Gaussian, and
   the score estimate with error measured in $L^2$ under the forward marginals.
2. **Assumptions.** The data distribution has finite second moment and the true score is Lipschitz along the
   forward process (or, without the Lipschitz assumption, the early-stopped, smoothed target); no
   log-concavity or functional inequality is assumed.
3. **Guarantee.** With step size $h = T/N \lesssim 1/L$ and $L \ge 1$ the Lipschitz constant of the scores, the output
   law $p_T$ of the discretized reverse process satisfies
   $\mathrm{TV}(p_T, q) \lesssim \sqrt{\mathrm{KL}(q \Vert \gamma^d)}\, e^{-T} + (L\sqrt{dh} + L m_2 h)\sqrt T + \varepsilon_{\mathrm{score}}\sqrt T$,
   where $q$ is the data distribution, $\gamma^d$ the standard Gaussian, $m_2^2$ the second moment of $q$ and
   $\varepsilon_{\mathrm{score}}$ the $L^2$ score error; choosing $T$ and $h$ makes the iteration count polynomial in $d$, $L$,
   $m_2$ and $1/\varepsilon$.

## Sources

- Sampling is as easy as learning the score (Chen, Chewi, Li, Li, Salim, Zhang, ICLR 2023; arXiv:2209.11215) — arXiv / ICLR: Assumptions 1–3 and Theorem 2 (DDPM). <https://arxiv.org/abs/2209.11215>
