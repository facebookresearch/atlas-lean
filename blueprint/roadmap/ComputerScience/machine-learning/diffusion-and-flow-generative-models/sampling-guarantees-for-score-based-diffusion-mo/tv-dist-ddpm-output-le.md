# Sampling guarantee for score-based diffusion (DDPM)

There are universal constants $C, c > 0$ such that the following holds. Let $q$ be a probability measure on $\mathbb{R}^d$ with full support and a smooth density $q = e^{-U}$, $U\colon \mathbb{R}^d \to \mathbb{R}$, let $q_t$ be the law at time $t$ of the forward Ornstein–Uhlenbeck process $dX = -X\,dt + \sqrt2\,dB$ started from $q$, and let $\gamma^d$ be the standard Gaussian on $\mathbb{R}^d$. Suppose that

1. for some $\eta > 0$, $\mathbb{E}_q[\|x\|^{2+\eta}] < \infty$; write $m_2^2 = \mathbb{E}_q[\|x\|^2]$;
2. for every $t \ge 0$ the score $\nabla \ln q_t$ is $L$-Lipschitz, where $L \ge 1$;
3. $\mathrm{KL}(q \,\|\, \gamma^d) < \infty$;
4. $T > 0$, $N \ge 1$ and the step size $h = T/N$ satisfies $h \le c/L$;
5. $\varepsilon \ge 0$, and the score estimates $s_{kh}$ are measurable and satisfy $\mathbb{E}_{q_{kh}}[\|s_{kh} - \nabla \ln q_{kh}\|^2] \le \varepsilon^2$ for $k = 1, \dots, N$.

Then the output law $p_T$ of the DDPM sampler with step $h$ and $N$ steps, started at $\gamma^d$, satisfies

$$
\mathrm{TV}(p_T, q) \le C \Bigl( \sqrt{\mathrm{KL}(q \,\|\, \gamma^d)}\, e^{-T} + \bigl(L \sqrt{d h} + L m_2 h\bigr) \sqrt{T} + \varepsilon \sqrt{T} \Bigr),
$$

where $\mathrm{TV}(\mu, \nu) = \sup_B |\mu(B) - \nu(B)|$. The moment of order $2 + \eta$ is needed for the proof; the bound depends only on $m_2$.

## Depends on

- [Forward Ornstein–Uhlenbeck marginal](ou-marginal.md)
- [Score of a density](log-density-score.md)
- [DDPM output law](ddpm-output.md)
- [Total variation distance between finite measures](../../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Proof depends on

- [Path-space discretization error for DDPM](ddpm-path-space-discretization-error.md)
- [Convergence of the Ornstein–Uhlenbeck process in KL divergence](kl-convergence-of-the-ornstein-uhlenbeck-process.md)
- [Data-processing inequality for total variation](../../../../InformationTheory/information-inequalities/strong-data-processing-and-dobrushin-s-coefficie/total-variation-dist-comp-le-self.md)
- [Triangle inequality for total variation distance](../../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist-triangle.md)
- [Pinsker's inequality, square-root form](../../../../InformationTheory/information-inequalities/total-variation-and-pinsker-s-inequality/total-variation-dist-le-sqrt-kl-div.md)

## Sources

- S. Chen, S. Chewi, J. Li, Y. Li, A. Salim and A. R. Zhang, *Sampling is as easy as learning the score: theory for diffusion models with minimal data assumptions*, ICLR 2023, Section 3.1: Theorem 2 with Assumptions 1–3, and its proof in Appendix B.3. <https://par.nsf.gov/servlets/purl/10502932> Full support and a smooth density $q = e^{-U}$ are the standing assumptions of its Section 2; finiteness of the KL divergence is assumption A3 of its introduction (the bound is vacuous without it); measurability of the estimates is implicit there (it makes $p_T$ a law).
