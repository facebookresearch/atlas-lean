# Poisson binomial likelihood of a heterogeneous agent-based infection model

**Setting.** A population of $N$ distinguishable agents has binary infection states $X=(X^n)_{n\le N}\in\{0,1\}^N$. In the static model, $X^n\sim\mathrm{Bernoulli}(\alpha^n)$ independently, with agent-specific probabilities $\alpha^n=(1+e^{-\beta^\top w^n})^{-1}$ driven by covariates $w^n$. Only an aggregate is observed: given $I(X)=\sum_nX^n$ infected agents, each is reported independently with probability $\rho$, so $Y\mid X\sim\mathrm{Binomial}(I(X),\rho)$. The law of $I(X)$ is the **Poisson binomial distribution** $\mathrm{PB}(\alpha)$.

**Statement.**

1. *(Recursion.)* Let $q(i,n)=\mathbb P\big(\sum_{m=n}^NX^m=i\big)$. Then $q(0,n)=\prod_{m\ge n}(1-\alpha^m)$, $q(1,N)=\alpha^N$, and

$$q(i,n)=\alpha^n\,q(i-1,n+1)+(1-\alpha^n)\,q(i,n+1).$$

So all of $\mathrm{PB}(\alpha)$ is computed in $O(N^2)$ operations instead of the $O(2^N)$ cost of summing over configurations.
2. *(Thinning.)* Marginally $Y\sim\mathrm{PB}(\rho\alpha)$. Hence the marginal likelihood $p_\theta(y)=\mathrm{PB}(y;\rho\alpha)$ is exact and costs $O(N^2)$. The posterior of the agent states $p_\theta(x\mid y)$ can also be sampled exactly in $O(N^2)$ operations.
3. *(Stability of PB laws.)* For probability vectors $\alpha,\bar\alpha\in[0,1]^N$,

$$\sum_{i=0}^N\big(\mathrm{PB}(i;\bar\alpha)-\mathrm{PB}(i;\alpha)\big)^2\le\Big(\sum_{n=1}^N|\bar\alpha^n-\alpha^n|\Big)^2,$$

$$\mathrm{KL}\big(\mathrm{PB}(\bar\alpha)\,\|\,\mathrm{PB}(\alpha)\big)\le\Big(\sum_{i}\frac{\mathrm{PB}(i;\bar\alpha)^2}{\mathrm{PB}(i;\alpha)^2}\Big)^{1/2}\sum_{n=1}^N|\bar\alpha^n-\alpha^n| .$$

4. *(Controlled SMC for the dynamic model.)* In the agent-based SIS model on a network, $X_t^n\mid X_{t-1}\sim\mathrm{Bernoulli}(\alpha^n(X_{t-1}))$. Here $\alpha^n=\lambda^n\mathcal D(n)^{-1}\sum_{m\in\mathcal N(n)}X_{t-1}^m$ if agent $n$ is susceptible and $\alpha^n=1-\gamma^n$ if it is infected, where $\mathcal D(n)$ and $\mathcal N(n)$ are the degree and neighbourhood of agent $n$. Twist a particle filter by approximate backward information filters $\psi_t$ of the optimal ones $\psi_t^\star$. Its path proposal $q_\theta$ satisfies

$$\mathrm{KL}\big(p_\theta(x_{0:T}\mid y_{0:T})\,\|\,q_\theta\big)\le\sum_{t=0}^T\eta_t^\star\big(\log(\psi_t^\star/\psi_t)\big)+M_{t-1}\,\eta_t\big(\log(\psi_t/\psi_t^\star)\big),$$

where $M_{-1}=1$ and $M_t=\max_x\eta_t^\star(x)/\eta_t(x)$. Each log-error term is in turn bounded by sums of $L^2$ norms of the error $\Delta_\theta$ made by replacing agent-level infection probabilities with their mean-field approximations.

## Expansion

Item 1 conditions on the state of agent $n$ and uses independence. For item 2, the characteristic function of $I(X)$ is $\prod_n\big(\alpha^ne^{i\omega}+1-\alpha^n\big)$. Binomial thinning replaces $e^{i\omega}$ by $\rho e^{i\omega}+1-\rho$, which gives $\prod_n\big(\rho\alpha^ne^{i\omega}+1-\rho\alpha^n\big)$, the characteristic function of $\mathrm{PB}(\rho\alpha)$. For item 3, Parseval's identity turns the $\ell^2$ distance between the PMFs into the $L^2(-\pi,\pi)$ distance between their characteristic functions. The difference of the products telescopes into $\sum_n(\bar\alpha^n-\alpha^n)(e^{i\omega}-1)\times(\text{factors of modulus}\le1)$. Repeated use of the triangle inequality then bounds the distance by $\sum_n|\bar\alpha^n-\alpha^n|$. The KL bound uses $\log u\le u-1$ and Cauchy–Schwarz. Item 3 is what turns the mean-field error in $\alpha$ into the error bounds of item 4, since the backward filters are built from Poisson binomial approximations of the number of infected neighbours. Without the interchangeability and homogeneous-mixing assumptions, the population cannot be reduced to counts. These exact and controlled computations make likelihood-based inference feasible when the forward algorithm would cost $O(2^{2N}T)$.

These are Section 2 (static model), the controlled-SMC propositions of Sections 3–4, and the Poisson-binomial lemmas in the appendix of the source.

## Sources

- N. Ju, J. Heng, P. E. Jacob, "Sequential Monte Carlo algorithms for agent-based models of disease transmission", arXiv:2101.12156 (2021). <https://doi.org/10.48550/arXiv.2101.12156>
