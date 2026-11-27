# Sampling guarantees for score-based diffusion models

The convergence guarantee of Chen et al. for score-based diffusion sampling: the forward Ornstein–Uhlenbeck process from the data distribution, the DDPM sampler with its step size and horizon, started at the standard Gaussian and driven by score estimates whose error is measured in $L^2$ under the forward marginals, and its bound in total variation. The bound assumes a finite moment of order $2 + \eta$ for some $\eta > 0$ (it depends only on the second moment), a Lipschitz score along the forward process and a finite KL divergence from the standard Gaussian, and no log-concavity or functional inequality; choosing $T$ and $h$ makes the iteration count polynomial in $d$, $L$, $m_2$ and $1/\varepsilon$. Without the Lipschitz assumption, stopping the sampler early gives guarantees for compactly supported data.

- [Forward Ornstein–Uhlenbeck marginal](ou-marginal.md)
- [Score of a density](log-density-score.md)
- [DDPM sampler step](ddpm-step.md)
- [DDPM sampler laws](ddpm-law.md)
- [DDPM output law](ddpm-output.md)
- [Forward process at time zero](ou-marginal-zero.md)
- [Stationarity of the standard Gaussian](ou-marginal-std-gaussian.md)
- [One-step DDPM run](ddpm-output-one.md)
- [Estimates the DDPM output depends on](ddpm-output-congr.md)
- [Convergence of the Ornstein–Uhlenbeck process in KL divergence](kl-convergence-of-the-ornstein-uhlenbeck-process.md)
- [Path-space discretization error for DDPM](ddpm-path-space-discretization-error.md)
- [Sampling guarantee for score-based diffusion (DDPM)](tv-dist-ddpm-output-le.md)
- [Early-stopped sampling guarantees for compactly supported data](early-stopped-sampling-for-compactly-supported-data.md)
