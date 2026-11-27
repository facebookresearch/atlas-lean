# Convergence of the Ornstein–Uhlenbeck process in KL divergence

Let $\gamma^d$ be the standard Gaussian on $\mathbb{R}^d$, let $q$ be a probability measure on $\mathbb{R}^d$, and let $q_t$ be the law at time $t$ of the Ornstein–Uhlenbeck process $dX = -X\,dt + \sqrt2\,dB$ started from $q$. Then for every $t \ge 0$,

$$
\mathrm{KL}(q_t \,\|\, \gamma^d) \le e^{-2t}\, \mathrm{KL}(q \,\|\, \gamma^d)
$$

in $[0, \infty]$. The bound needs no hypothesis on $q$: at $t = 0$ it is an equality, and when $\mathrm{KL}(q \,\|\, \gamma^d) = \infty$, for instance when $q$ has no density with respect to $\gamma^d$, its right side is infinite.

## Depends on

- [Forward Ornstein–Uhlenbeck marginal](ou-marginal.md)

## Proof depends on

- [Gross' logarithmic Sobolev inequality](../../../../Probability/concentration-inequalities/transport-cost-inequalities/kl-div-with-density-std-gaussian-le.md)
- [Lower semicontinuity of the Kullback–Leibler divergence](../../../../InformationTheory/information-inequalities/donsker-varadhan-variational-formula/lower-semicontinuity-of-the-kl-divergence.md)

## Expansion

A sound expansion has separate pages for:

1. **Entropy dissipation for regular densities.** Suppose that $q = f \gamma^d$, where $f$ is smooth, bounded above and below by positive constants, and has bounded derivatives of all orders. Then for $t > 0$, $q_t = f_t \gamma^d$, where $f_t = P_t f$ is the Ornstein–Uhlenbeck semigroup applied to $f$ and has the same properties; $\mathrm{KL}(q_t \,\|\, \gamma^d)$ and the relative Fisher information $I(q_t \,\|\, \gamma^d) = \int \|\nabla \log f_t\|^2\, dq_t$ are finite; and $\frac{d}{dt}\, \mathrm{KL}(q_t \,\|\, \gamma^d) = -I(q_t \,\|\, \gamma^d)$. These hypotheses are what the derivative needs: a positive density whose logarithm is defined, finite entropy and Fisher information, and enough regularity to differentiate under the integral and integrate by parts against $\gamma^d$. The decay bound itself needs none of them.
2. **Exponential decay for regular densities.** Gross' inequality $\mathrm{KL}(q_t \,\|\, \gamma^d) \le \tfrac12 I(q_t \,\|\, \gamma^d)$ makes the derivative of $e^{2t}\, \mathrm{KL}(q_t \,\|\, \gamma^d)$ nonpositive on $(0, \infty)$; since $\mathrm{KL}(q_t \,\|\, \gamma^d) \to \mathrm{KL}(q \,\|\, \gamma^d)$ as $t \to 0$, the bound holds for such $q$.
3. **Approximation.** If $\mathrm{KL}(q \,\|\, \gamma^d) < \infty$, let $f = dq/d\gamma^d$. Truncating $f$ from below and above, applying the Ornstein–Uhlenbeck semigroup for a short time and renormalizing gives densities $f_n$ as in step 1 with $f_n \to f$ in $L^1(\gamma^d)$ and $\int f_n \log f_n\, d\gamma^d \to \int f \log f\, d\gamma^d$. The laws $q^n = f_n \gamma^d$ converge weakly to $q$, so $q^n_t \to q_t$ weakly for each $t$, and the lower semicontinuity of the KL divergence gives $\mathrm{KL}(q_t \,\|\, \gamma^d) \le \liminf_n \mathrm{KL}(q^n_t \,\|\, \gamma^d) \le \liminf_n e^{-2t}\, \mathrm{KL}(q^n \,\|\, \gamma^d) = e^{-2t}\, \mathrm{KL}(q \,\|\, \gamma^d)$.

## Sources

- S. Chen, S. Chewi, J. Li, Y. Li, A. Salim and A. R. Zhang, *Sampling is as easy as learning the score: theory for diffusion models with minimal data assumptions*, ICLR 2023, proof of Theorem 2 (Appendix B.3), which uses this convergence and cites D. Bakry, I. Gentil and M. Ledoux, *Analysis and Geometry of Markov Diffusion Operators*, Grundlehren der Mathematischen Wissenschaften 348 (Springer, 2014), Theorem 5.2.1. <https://par.nsf.gov/servlets/purl/10502932>
