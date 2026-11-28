# Stress-structured SIR model and outbreak probability

**Setting.** Hosts (for example fish in aquaculture) are susceptible in a normal state $S_N$ or a stressed state $S_S$, entering at rate $\Lambda$, becoming stressed at rate $\alpha$ (driven by water quality) and dying at rate $\mu$. Infected hosts $I_N,I_S$ keep the physiological state they were infected in and differ in transmission rates $\beta_N,\beta_S$, recovery rates $\gamma_N,\gamma_S$ and disease mortality $d_N,d_S$; $R$ are recovered. With constant stress rate,

$$\begin{aligned}\dot S_N&=\Lambda-(\alpha+\lambda+\mu)S_N,&\dot S_S&=\alpha S_N-(\lambda+\mu)S_S,\\ \dot I_N&=\lambda S_N-\nu_NI_N,&\dot I_S&=\lambda S_S-\nu_SI_S,\qquad \dot R=\gamma_NI_N+\gamma_SI_S-\mu R,\end{aligned}$$

with force of infection $\lambda=\beta_NI_N+\beta_SI_S$ and $\nu_j=\gamma_j+\mu+d_j$. At the disease-free equilibrium $S_N^0=\Lambda/(\alpha+\mu)$, $S_S^0=\alpha\Lambda/(\mu(\alpha+\mu))$, and the next-generation method gives

$$\mathcal R_0=\mathcal R_{01}+\mathcal R_{02}=\frac{\beta_NS_N^0}{\nu_N}+\frac{\beta_SS_S^0}{\nu_S}.$$

**Proposition 3 (forward bifurcation).** In the biologically feasible region the system undergoes a forward transcritical bifurcation at $\mathcal R_0=1$: for $\mathcal R_0<1$ the disease-free equilibrium is globally asymptotically stable, and for $\mathcal R_0>1$ it is unstable and a unique endemic equilibrium appears (no backward bifurcation).

**Theorem 7 (probability of extinction).** In the stochastic (continuous-time Markov chain) version near the disease-free state, the associated two-type branching process is positive, regular and nonsingular, with offspring generating functions

$$f_N(u_N,u_S)=\frac{\beta_NS_N^0u_N^2+\beta_NS_S^0u_Nu_S+\nu_N}{\nu_N+\beta_N(S_N^0+S_S^0)},\qquad f_S(u_N,u_S)=\frac{\beta_SS_S^0u_S^2+\beta_SS_N^0u_Nu_S+\nu_S}{\nu_S+\beta_S(S_N^0+S_S^0)}.$$

Starting from $i_{N0}$ normal and $i_{S0}$ stressed infected hosts, the probability that the infection dies out is $\mathbb P_{\mathrm{ext}}=(u_N^*)^{i_{N0}}(u_S^*)^{i_{S0}}$, where $\mathbf u^*$ is the smallest fixed point of $\mathbf f=(f_N,f_S)$ in $[0,1]^2$. If $\mathcal R_0\le1$ then $\mathbf u^*=(1,1)$ and extinction is certain; if $\mathcal R_0>1$ there is a unique fixed point $\mathbf u^*\in(0,1)^2$ and $\mathbb P_{\mathrm{ext}}<1$.

## Expansion

Each infected host of type $j$ either leaves the infected class (rate $\nu_j$) or infects a susceptible of type $N$ or $S$ in proportion to $S_N^0$ and $S_S^0$, producing a new infected host of the susceptible's type while remaining infected; this gives the quadratic generating functions. The branching process is supercritical exactly when the spectral radius of its mean matrix, which equals $\mathcal R_0$, exceeds $1$. Since stressed hosts typically shed more and recover more slowly ($\beta_S>\beta_N$, $\nu_S<\nu_N$), the paper shows that introducing infection through stressed hosts gives a markedly higher outbreak probability than introduction through normal hosts, even at the same $\mathcal R_0$, which the deterministic threshold does not reveal.

## Sources

- C. Djuikem, J. Arino, "Deterministic and stochastic infection dynamics in a population subject to stress", *Bulletin of Mathematical Biology* 88(6) (2026), 104, Proposition 3, Eq. for $\mathcal R_0$ (Section 2.2), Theorem 7, <https://doi.org/10.1007/s11538-026-01671-x> (preprint arXiv:2602.07134).
