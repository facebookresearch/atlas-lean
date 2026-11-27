# Diffusion and flow-based generative models

Linear algebra of diffusion and flow-based generative models: for Gaussian data, the score and the optimal denoiser are spectral functions of the data covariance and the probability-flow ODE is a linear system with commuting coefficients whose flow map is an explicit affine map; for any differentiable velocity field, the divergence in the log-density computations of flow models is the trace of a Jacobian. For data distributions with finite second moment whose score is Lipschitz along the forward process (or for an early-stopped, smoothed target), score-based diffusion samplers with $L^2$-accurate score estimates have polynomial convergence guarantees in total variation, with no log-concavity assumed. These pages are expositions of published results; each names what it relies on, and how, under Informally uses, and marks results not stated in its sources as derived.

- [Score and optimal denoiser for Gaussian data](gaussian-data-score-and-denoiser.md)
- [Exact probability-flow solution for Gaussian data](gaussian-probability-flow-exact-solution.md)
- [Divergence is the trace of the Jacobian](divergence-eq-trace-jacobian.md)
- [Polynomial sampling guarantees for score-based diffusion models](polynomial-sampling-guarantees-for-score-based-diffusion-mod.md)
