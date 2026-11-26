# Mixed-Sellke fluid limit and heterogeneous SIR closures

**Individual-based model.** In a population of size $N$, each initially susceptible individual $j$ carries an i.i.d. susceptibility $\Lambda_j\sim\mu$ on $[0,\infty)$ with finite mean, and a Sellke resistance threshold $Q_j\mid\Lambda_j\sim\mathrm{Exp}(\Lambda_j)$. It stays susceptible while the cumulative infection pressure $A_N(t)=\tau\int_0^t\iota_N(u)\,du$ is below $Q_j$ ($\iota_N$ the infected fraction, $\tau$ the transmission rate). Infectious periods are i.i.d. $\mathrm{Exp}(\gamma)$. Let $G(a)=\mathbb E[e^{-a\Lambda}]$ be the Laplace transform of the susceptibility law, the probability of escaping infection pressure $a$.

**Theorem (fluid limit).** If the initial fractions converge to $(s_0,\iota_0,r_0)$ with $s_0,\iota_0>0$, then for every $T$, $\sup_{t\le T}\|(s_N,\iota_N,r_N,A_N)-(s,\iota,r,A)\|\to0$ in probability, where
$$\dot A=\tau\big[1-r_0-s_0G(A)\big]-\gamma A,\quad A(0)=0,\qquad s=s_0G(A),\quad r=r_0+\tfrac\gamma\tau A,\quad \iota=1-s-r .$$
Equivalently $\dot s=-\tau\,\bar\lambda(A)\,s\,\iota$ with **effective susceptibility** $\bar\lambda(a)=-G'(a)/G(a)$, the mean of $\Lambda$ among those who escaped pressure $a$.

**Proposition (selection identity).** If $\mathbb E\Lambda^2<\infty$, then $\bar\lambda'(a)=-\operatorname{Var}_a(\Lambda)\le0$, the variance under the exponentially tilted law $\mu_a(d\lambda)\propto e^{-a\lambda}\mu(d\lambda)$. So the most susceptible are infected first, and effective susceptibility falls strictly for non-degenerate heterogeneity.

**Proposition (final size).** With $\mathbb E\Lambda=1$ and all else fixed, the heterogeneous epidemic has smaller final infection pressure and final size than the homogeneous one, $A_\infty\le A_\infty^{\mathrm{hom}}$ and $r_\infty\le r_\infty^{\mathrm{hom}}$, strictly if $\Lambda$ is non-degenerate.

**Finite closures.** Writing $\bar\lambda$ as a function $\psi(s/s_0)$ closes the system in $(s,\iota)$. Gamma$(\alpha,\kappa)$ susceptibility gives $G(a)=(\kappa/(\kappa+a))^\alpha$ and power-law incidence $\dot s=-\tau\frac\alpha\kappa(s/s_0)^{1/\alpha}s\iota\propto s^{1+1/\alpha}\iota$; Poisson$(\theta)$ susceptibility gives $G(a)=\exp\{\theta(e^{-a}-1)\}$, logarithmic incidence and a fully resistant subpopulation $\{\Lambda=0\}$; negative binomial gives a difference-of-powers incidence; finite discrete laws allow arbitrary multimodality; and the inverse Gaussian gives another logarithmic-incidence model.

## Depends on

- [Kermack-McKendrick SIR model](../kermack-mckendrick-sir-model/README.md)

## Expansion

The Sellke construction turns the epidemic into a deterministic threshold problem given the infection pressure. Conditionally on $A_N$, the susceptible fraction is an empirical survival function with mean $s_0G(A_N)$, and recoveries are a time-changed Poisson process with intensity $N\gamma\int\iota_N$. The law of large numbers for both, together with the identity $r_N-r_0=\frac\gamma\tau A_N+o(1)$, reduces everything to the scalar integral equation for $A$, whose Lipschitz vector field gives uniqueness and convergence. The selection identity is the derivative of the log-Laplace transform: $-\frac{d^2}{da^2}\log G(a)$ is the variance of the tilted law. The final-size comparison uses Jensen's inequality, $G(a)\ge e^{-a}$, so the heterogeneous vector field for $A$ is dominated by the homogeneous one. These closures give a probabilistic derivation of the phenomenological power-law incidences used in heterogeneous SIR models.

## Sources

- O. Izyumtseva, W. R. KhudaBukhsh, M. G. M. Gomes, G. A. Rempala, "From individual-based stochastic epidemics to heterogeneous SIR equations", arXiv:2608.22122 (2026), Section 2 (finite-population model, Laplace transform), Section 3 (Theorem 1, Propositions 2-3) and Section 4 (gamma, Poisson, negative-binomial, finite discrete and inverse-Gaussian closures), <https://doi.org/10.48550/arXiv.2608.22122>.
