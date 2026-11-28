# Reversed reconstructed process as a time-rescaled Yule process

**Setting.** Consider a linear birth–death process $\mathrm{BDP}(\lambda,\mu,\psi)$ with birth rate $\lambda$ and death rate $\mu$, where $0\le\mu<\lambda$. It starts from one individual at an unknown time of origin with an improper uniform prior, and at the present each extant individual is sampled independently with probability $\psi\in(0,1]$. We condition on $n$ sampled individuals. The **reversed reconstructed process (RRP)** $X_\psi$ follows the genealogy of the sample backwards from the present ($\tau=0$). It is a time-inhomogeneous pure-death process started from $n$ lineages, in which each lineage dies (coalesces) independently at rate

$$m_\psi(\tau)=\frac{\psi\lambda\,e^{(\lambda-\mu)\tau}}{1+\frac{\psi\lambda}{\lambda-\mu}\big(e^{(\lambda-\mu)\tau}-1\big)} .$$

Its integrated rate is

$$\rho_\psi(\tau)=\int_0^\tau m_\psi=\log\Big(1+\frac{\psi\lambda}{\lambda-\mu}\big(e^{(\lambda-\mu)\tau}-1\big)\Big).$$

The **time-reversed Yule rate-1 process** $Y$ is the homogeneous pure-death process in which each lineage dies at rate $1$.

**Theorem (time rescaling).**

1. With $t=g_1(\tau):=\rho_\psi(\tau)$, so that $g_1^{-1}(t)=\frac{1}{\lambda-\mu}\log\big(1+\frac{\lambda-\mu}{\psi\lambda}(e^{t}-1)\big)$,

$$X_\psi(\tau)\overset{d}{=}Y(g_1(\tau)),\qquad X_\psi(g_1^{-1}(t))\overset{d}{=}Y(t)$$

as processes. In particular, let $E_1,\dots,E_n$ be the successive holding times of $Y$ started from $n$ lineages, independent with $E_j\sim\mathrm{Exp}(n-j+1)$, and let $U_k=E_1+\dots+E_k$ be its event times. Then the event times of $X_\psi$ are jointly distributed as $T_k=g_1^{-1}(U_k)$, $k=1,\dots,n$, and its inter-event times as $T_{k+1}-T_k=g_1^{-1}(U_{k+1})-g_1^{-1}(U_k)$. Because $g_1^{-1}$ is nonlinear, these are not $g_1^{-1}(E_{k+1})$ and are in general neither independent nor exponential: the clock change acts on the event times, not on each holding time separately. The tree topology is that of the Yule/Kingman coalescent.
2. *(Incomplete sampling as rescaling.)* With $g_2(\tau)=\frac{1}{\lambda-\mu}\log\big(1+\psi(e^{(\lambda-\mu)\tau}-1)\big)$, the incompletely sampled RRP is a deterministic time change of the completely sampled one: $X_\psi(\tau)\overset{d}{=}X_1(g_2(\tau))$.
3. *(Consequences.)* For $1\le k\le n$, the time $T_k$ of the $k$-th event of $X_\psi$ has density

$$f_{T_k}(\tau)=\binom nk\,k\,m_\psi(\tau)\big(1-e^{-\rho_\psi(\tau)}\big)^{k-1}e^{-(n-k+1)\rho_\psi(\tau)}.$$

The time to origin $T_n$ has distribution function $\big(1-e^{-\rho_\psi(\tau)}\big)^n$. The length $E$ of a uniformly chosen pendant edge has density

$$f_E(\tau)=\frac{2\psi\lambda(\lambda-\mu)^3e^{(\lambda-\mu)\tau}}{\big(\lambda\psi e^{(\lambda-\mu)\tau}-[\mu-\lambda(1-\psi)]\big)^3}.$$

## Expansion

If a pure-death process has per-lineage rate $m(\tau)$ and time is changed by a monotone differentiable map $\zeta=g(\tau)$, the new rate is $m(g^{-1}(\zeta))\,|(g^{-1})'(\zeta)|$. Choosing $g=\rho_\psi$ makes this rate identically $1$. This is the point-process time-rescaling theorem, which turns any integrable intensity into a unit-rate Poisson clock. A pure-death process with per-lineage survival probability $e^{-\rho(\tau)}$ has binomial transition probabilities, and this yields the order-statistic formulas in item 3 at once. Earlier derivations of these formulas integrated over the prior on the origin time. Because $g_1$ is explicit, the RRP can also be simulated exactly: draw a Yule rate-1 coalescent and map its event times (the partial sums $U_k$ of its holding times) through $g_1^{-1}$. In the subcritical case one conditions on extinction, which swaps $\lambda$ and $\mu$. In the critical case $\lambda=\mu$ the rate becomes $m(\tau)=\psi\lambda/(1+\psi\lambda\tau)$.

These are Sections 1.2, 2.1–2.2 and 3.1–3.2 of the source, including Proposition 1 (pendant-edge density, Section 3.2).

## Sources

- A. Ignatieva, J. Hein, P. A. Jenkins, "A characterisation of the reconstructed birth-death process through time rescaling", arXiv:1912.04861 (2019). <https://doi.org/10.48550/arXiv.1912.04861>
- Published version: A. Ignatieva, J. Hein, P. A. Jenkins, "A characterisation of the reconstructed birth–death process through time rescaling", Theoretical Population Biology 134 (2020), 61–76, <https://doi.org/10.1016/j.tpb.2020.05.001>.
