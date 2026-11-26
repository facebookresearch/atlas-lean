# Convergence of the Ornstein–Uhlenbeck process in KL divergence

Let $\gamma^d$ be the standard Gaussian on $\mathbb{R}^d$, let $q$ be a probability measure on $\mathbb{R}^d$, and let $q_t$ be the law at time $t$ of the Ornstein–Uhlenbeck process $dX = -X\,dt + \sqrt2\,dB$ started from $q$. Then for every $t \ge 0$,

$$
\mathrm{KL}(q_t \,\|\, \gamma^d) \le e^{-2t}\, \mathrm{KL}(q \,\|\, \gamma^d) .
$$

## Depends on

- [Forward Ornstein–Uhlenbeck marginal](ou-marginal.md)

## Proof depends on

- [Gross' logarithmic Sobolev inequality](../../../../Probability/concentration-inequalities/transport-cost-inequalities/kl-div-with-density-std-gaussian-le.md)

## Expansion

A sound expansion has separate pages for:

1. **Entropy dissipation.** Along the Ornstein–Uhlenbeck process, $\frac{d}{dt}\, \mathrm{KL}(q_t \,\|\, \gamma^d) = -I(q_t \,\|\, \gamma^d)$, where $I(\mu \,\|\, \gamma^d) = \int \|\nabla \log (d\mu/d\gamma^d)\|^2\, d\mu$ is the relative Fisher information.
2. **Exponential decay.** Gross' inequality $\mathrm{KL} \le \tfrac12 I$ turns this into $\frac{d}{dt}\, \mathrm{KL}(q_t \,\|\, \gamma^d) \le -2\, \mathrm{KL}(q_t \,\|\, \gamma^d)$, and Grönwall's lemma gives the bound.

## Sources

- S. Chen, S. Chewi, J. Li, Y. Li, A. Salim and A. R. Zhang, *Sampling is as easy as learning the score: theory for diffusion models with minimal data assumptions*, ICLR 2023, proof of Theorem 2 (Appendix B.3), which uses this convergence and cites D. Bakry, I. Gentil and M. Ledoux, *Analysis and Geometry of Markov Diffusion Operators*, Grundlehren der Mathematischen Wissenschaften 348 (Springer, 2014), Theorem 5.2.1. <https://par.nsf.gov/servlets/purl/10502932>
