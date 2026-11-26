# Central limit theorem for epidemics with infection memory and waning immunity

**Model.** Each of $N$ individuals has an age of infection $a^N_k(t)\ge0$ (time since its last infection) and a trait $\theta^N_k(t)\in\Theta\subseteq\mathbb R^d$, with infectivity $\lambda(a,\theta)\in[0,\lambda_*]$ and susceptibility $\gamma(a,\theta)\in[0,1]$, so immunity wanes gradually as $\gamma$ recovers with age. Individual $k$ is (re)infected at rate $\mathfrak F^N(t)\gamma(a^N_k,\theta^N_k)$, where $\mathfrak F^N(t)=\frac1N\sum_j\lambda(a^N_j(t),\theta^N_j(t))=\langle\mu^N_t,\lambda\rangle$ is the force of infection and $\mu^N_t=\frac1N\sum_k\delta_{(a^N_k(t),\theta^N_k(t))}$; at infection its age resets to $0$ and its new trait is drawn from $K(\theta,\tilde\theta)\nu(d\tilde\theta)$, a memory kernel with $\int K(\theta,\tilde\theta)\nu(d\tilde\theta)=1$. As $N\to\infty$, $\mu^N\to\mu$, the unique solution of

$$\langle\mu_t,f_t\rangle=\langle\mu_0,f_0\rangle+\int_0^t\langle\mu_s,\partial_af_s+\partial_sf_s\rangle ds+\int_0^t\langle\mu_s,\lambda\rangle\langle\mu_s,Rf_s\rangle ds,$$

$$Rf(a,\theta)=\int_\Theta\big(f(0,\tilde\theta)-f(a,\theta)\big)\gamma(a,\theta)K(\theta,\tilde\theta)\,\nu(d\tilde\theta).$$

**Theorem (FCLT).** Assume moreover $\mathbb E[a_0^{2\alpha}]<\infty$ for the initial ages and $\int_\Theta\sup_\theta K(\theta,\tilde\theta)\nu(d\tilde\theta)<\infty$. Then for every $\alpha>1/2$ the fluctuations $\hat\mu^N=\sqrt N(\mu^N-\mu)$ converge in distribution in $D(\mathbb R_+,\mathcal W^{-(m_d+1),\alpha}_0)$ (the dual of a weighted Sobolev space, $m_d$ depending on $d$) to the continuous solution $\hat\mu$ of the linear stochastic equation

$$\langle\hat\mu_t,\varphi_t\rangle=\langle\hat\mu_0,\varphi_0\rangle+\int_0^t\langle\hat\mu_s,\partial_s\varphi_s+\partial_a\varphi_s\rangle ds+\int_0^t\big(\langle\hat\mu_s,\lambda\rangle\langle\mu_s,R\varphi_s\rangle+\langle\mu_s,\lambda\rangle\langle\hat\mu_s,R\varphi_s\rangle\big)ds+W_t(\varphi_t),$$

where $\hat\mu_0$ is the Gaussian limit of the initial fluctuations and $W$ is a centred continuous Gaussian process with

$$\mathbb E[W_t(\varphi)W_{t'}(\psi)]=\int_0^{t\wedge t'}\langle\mu_s,\lambda\rangle\,\langle\mu_s,\tilde R(\varphi_s,\psi_s)\rangle ds,$$

$\tilde R(\varphi,\psi)(a,\theta)=\int(\varphi(0,\tilde\theta)-\varphi(a,\theta))(\psi(0,\tilde\theta)-\psi(a,\theta))\gamma(a,\theta)K(\theta,\tilde\theta)\nu(d\tilde\theta)$. If $\hat\mu_t$ has a density $\hat u_t(a,\theta)$, it is the unique weak solution of the corresponding transport SPDE with Gaussian noise, and the fluctuations of the force of infection and the mean susceptibility solve a closed system of stochastic Volterra equations.

## Expansion

The fluctuation equation is the linearization of the law-of-large-numbers equation: the bilinear infection term $\langle\mu,\lambda\rangle\langle\mu,R\varphi\rangle$ produces two linear terms, one perturbing the force of infection and one the infected population, and the martingale part of the jump process gives the Gaussian noise $W$ whose quadratic variation is the infection rate times the squared jump of the test function at a reinfection. Tightness is proved in a Hilbert space of distributions via Aldous's criterion, using weighted Sobolev norms in the age variable and a conditional moment bound that allows unbounded initial ages (needed to recover ODE-type epidemic models); a counting process of reinfections controls the interactions. Without memory ($K\equiv1$) the result reduces to the known FCLT for varying-infectivity models with gradual loss of immunity.

## Sources

- A. B. Zotsa-Ngoufack, "Functional Central Limit Theorem and SPDE for epidemic model with memory of the last infection and waning immunity", arXiv:2505.15617 (2025), Section 2 (Assumptions 2.1–2.3, Theorem 2.1, Definition 2.5, Theorem 2.6, Proposition 2.7 and the Volterra-system proposition), <https://doi.org/10.48550/arXiv.2505.15617>.
