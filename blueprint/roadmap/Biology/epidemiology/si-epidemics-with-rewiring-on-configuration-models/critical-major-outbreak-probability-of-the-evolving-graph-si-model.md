# Critical major-outbreak probability of the evolving-graph SI model

**Model (evoSI).** Let $\mathrm{CM}(n,\mathbf d_n)$ be the configuration model on $n$ vertices with degree sequence $\mathbf d_n$, whose empirical degree law $p_{k,n}$ converges to $p^*_k$ with uniformly bounded exponential moments $\frac1n\sum_ie^{\eta d_{i,n}}\le C$ and the concentration condition $\sum_k(k+1)^4|np_{k,n}-np^*_k|\le n^{c}$ for some $c<2/3$. Each susceptible–infected edge transmits at rate $\lambda$ (becoming infected–infected) and, independently, is broken at rate $\rho$, after which the susceptible endpoint rewires to a uniformly chosen vertex. Let $m_r=\sum_kk^rp^*_k$ and $\Lambda_n$ the final number of infected vertices started from one infected vertex. The critical infection rate is
$$\lambda_c=\frac{\rho\,m_1}{m_2-2m_1},$$
and the sign of
$$\Delta=-\frac{m_3-3m_2+2m_1}{m_1}+3(m_2-2m_1)$$
was known to decide whether the epidemic-size phase transition at $\lambda_c$ is continuous ($\Delta<0$) or discontinuous ($\Delta>0$).

**Theorem.** At $\lambda=\lambda_c$:
1. If $\Delta>0$, there are $C,\varepsilon_0>0$ such that for every fixed $\varepsilon\in(0,\varepsilon_0)$,
$$\lim_{n\to\infty}n^{1/3}\,\mathbb P_1(\Lambda_n/n>\varepsilon)=C .$$
2. If $\Delta<0$, then $n^{1/3}\,\mathbb P_1(\Lambda_n/n>\varepsilon)\to0$ for every $\varepsilon>0$.

The same holds for the two Markovian comparison models (avoSI and AB-avoSI) that stochastically bound evoSI from above and below.

## Expansion

Exploring the graph together with the epidemic, the number $X_{I,t}$ of infected half-edges behaves at criticality like a random walk with zero drift and variance $\sigma^2$ plus a deterministic quadratic correction $\tfrac12m_1\Delta t^2n$ coming from depletion of susceptibles and rewiring. On the time scale $t\asymp n^{-1/3}$ the walk survives to height $\asymp n^{1/3}$ with probability $\asymp n^{-1/3}$ (a gambler's-ruin estimate with explicit constant $\big(\tfrac{\pi\sigma^2}{2m_1}(1+\rho/\lambda_c)\big)^{-1/2}q^{-1/2}$ for survival past time $qn^{-1/3}$). If $\Delta>0$ the quadratic drift is self-reinforcing and such a survivor grows to a macroscopic outbreak; if $\Delta<0$ the drift pulls it back, as for the largest component of a critical Erdős–Rényi graph, so the outbreak probability is $o(n^{-1/3})$.

## Sources

- W. Chen, H. Hou, R. Ma, D. Yao, "Susceptible-Infected Epidemics on Evolving Graphs at Critical Infection Rate", arXiv:2603.03009 (2026), Section 1.1 (Assumption (H), critical rate, Theorem 1) and Section 1.4 (comparison models and three-stage analysis, Theorems 2–6, Corollary 1), <https://doi.org/10.48550/arXiv.2603.03009>.
