# Functional law of large numbers for infection-age SIR on heterogeneous random graphs

**Model.** $N$ individuals carry characteristics $X_i^N$ in a Polish space $\mathbb{X}$. Nodes $i,j$ are connected independently with probability $\kappa^N(X_i^N,X_j^N)$, and an edge $(i,j)$ carries a random weight $\omega^N(i,j)$ with conditional mean $\gamma^N(X_i^N,X_j^N)$. An infected individual $j$ with infection age $a$ exerts infectivity $\lambda_j^N(a)\le\lambda^*$ (random, depending on its characteristic), so a susceptible $i$ is infected at rate $\sum_{j\sim i}\omega^N(i,j)\lambda_j^N(\text{age}_j)$. Infected periods have survival function $F^c_x$ and mean infectivity $\bar\lambda(x,a)=\mathbb{E}\lambda(a)$. Write $\bar\mu^{S,N}_t,\bar\mu^{R,N}_t$ for the empirical measures (scaled by $1/N$) of characteristics of susceptible and recovered individuals, and $\bar\mu^{I,N}_t$ for that of (characteristic, infection age) of infected ones.

**Assumptions.** The initial empirical measures converge to $\bar\mu^S_0,\bar\mu^I_0,\bar\mu^R_0$; the effective kernel $\bar\omega^N=N\kappa^N\gamma^N$ converges uniformly to a bounded, a.e. continuous $\bar\omega$ and is bounded by $\omega^*$; and the variance terms $\bar\gamma^N=N^{-2}\sum_{i,j}\gamma^N(X_i^N,X_j^N)$ and $\Upsilon^N$ (the normalized second moments of the edge weights) tend to $0$. The edge weights are independent (given the characteristics); $\bar\mu^I_0$ is absolutely continuous with respect to $\mu_{\mathbb X}\otimes\mathrm{Leb}$, and $a\mapsto F_x(a)$ and $\bar\lambda$ are almost everywhere continuous. The graph may be dense or sparse as long as these hold; $\bar\omega$ need not be symmetric.

**Statement.** $(\bar\mu^{S,N},\bar\mu^{I,N},\bar\mu^{R,N})\to(\bar\mu^S,\bar\mu^I,\bar\mu^R)$ in probability in the Skorokhod spaces of measure-valued paths, where $(\bar\mu^S,\overline{\mathfrak{F}})$ is the unique solution of

$$\bar\mu^S_t(dx)=\bar\mu^S_0(dx)-\int_0^t\overline{\mathfrak{F}}(s,x)\,\bar\mu^S_s(dx)\,ds,$$

$$\overline{\mathfrak{F}}(t,x)=\int_0^\infty\!\!\int_{\mathbb{X}}\bar\omega(x,x')\frac{\bar\lambda(x',a'+t)}{F^c_{x'}(a')}\bar\mu^I_0(dx',da')+\int_0^t\!\!\int_{\mathbb{X}}\bar\omega(x,x')\,\bar\lambda(x',t-s)\,\overline{\mathfrak{F}}(s,x')\,\bar\mu^S_s(dx')\,ds,$$

and $\bar\mu^I,\bar\mu^R$ are explicit: for test functions $\psi$,

$$\langle\bar\mu^I_t,\psi\rangle=\int\!\!\int\psi(x,a+t)\frac{F^c_x(a+t)}{F^c_x(a)}\bar\mu^I_0(dx,da)+\int_0^t\!\!\int\psi(x,t-s)F^c_x(t-s)\,\overline{\mathfrak{F}}(s,x)\,\bar\mu^S_s(dx)\,ds .$$

If $F_x$ has a bounded continuous hazard rate $h_x$ and $\bar\mu^I_0(\mathbb X\times\{0\})=0$, then $\bar\mu^I$ is the unique weak solution of the transport equation $\partial_t\bar\mu^I+\partial_a\bar\mu^I=-h\,\bar\mu^I$ with boundary influx $\overline{\mathfrak{F}}(t,x)\bar\mu^S_t(dx)$ at age $0$.

## Proof depends on

- [Gronwall inequality in integral form](../../../../Analysis/ordinary-differential-equations/gronwall-inequality/gronwall-inequality-integral-form.md)

## Expansion

$\overline{\mathfrak{F}}(t,x)$ is the limiting force of infection on a susceptible of characteristic $x$: the first term is the remaining expected infectivity of the initially infected (conditioned on their current age), the second sums over individuals infected at time $s$ with characteristic $x'$, weighted by the contact kernel. On a graph, the pressure on $i$ is a sum over neighbours, whose conditional mean is $\frac1N\sum_j\bar\omega^N(X_i,X_j)\lambda_j$; the variance conditions make this sum concentrate around its mean uniformly over individuals, so the individual forces of infection converge to $\overline{\mathfrak{F}}(t,X_i)$ in $L^1$ over the susceptibles. Uniqueness of the limiting system follows from a Gronwall argument on the linear Volterra structure for $\overline{\mathfrak{F}}$, and tightness of the measure-valued processes is checked through compact containment and projections onto a separating class.

## Sources

- Guodong Pang, Étienne Pardoux and Aurélien Velleret, "Stochastic Heterogeneous SIR Model with Infection-Age Dependent Infectivity on Large Random Graphs", Mathematical Physics, Analysis and Geometry 29 (2026), 44, <https://doi.org/10.1007/s11040-026-09582-y>; numbering as in arXiv:2502.04225: Section 2 (model, Assumptions 1-8), Theorem 3.1, Propositions 4.1 and 4.3.
