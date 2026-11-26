# Functional law of large numbers for SIR on co-evolving dense random graphs

**Model.** Vertices $[n]$ start on an Erdős-Rényi graph $G(n,p_0)$, each infected independently with probability $q_0$. The **type** of vertex $i$ is $y_i(t)=-1$ if susceptible, its infection age $t-t_i^{I}$ if infected, and $T+1$ if recovered; $F_n(t;\cdot)$ is the empirical distribution of types. A susceptible vertex becomes infected at rate $\frac\lambda n\sum_{j\text{ infected neighbor}}\mathscr I(y_j(t))$, with a continuous infectivity profile $\mathscr I:[0,\infty)\to[0,1]$, and infected vertices recover at rate 1. Each edge between a pair of susceptible, susceptible-infected or infected vertices switches on at rate $\gamma\pi_s(\cdot)$ and off at rate $\gamma(1-\pi_s(\cdot))$, $s\in\{SS,SI,II\}$. Here $\pi_s$ may depend on the endpoints' infection ages and on the whole type distribution $F_n(t;\cdot)$, and is Lipschitz in these arguments in the Lévy metric. Recovered vertices resample their edges once with probability $p_0$, after which the edges are frozen. Vertex and edge dynamics thus feed back on each other in both directions.

**Theorem (limit equations).** With $p_S$ the susceptible density, $f_I(t;u)$ the density of infection ages, $H(t;u,v,\cdot)$ the limiting probability that an edge between types $u,v$ is active, and force of infection
$$\mathcal J(t)=\int_0^t dF(t;u)\,H(t;-1,u,F)\,\mathscr I(u),$$
the system
$$\partial_tp_S=-\lambda\mathcal J(t)p_S,\qquad \partial_tf_I+\partial_uf_I=-f_I,\qquad f_I(t;0)=\lambda\mathcal J(t)p_S(t),\qquad \partial_tp_R=p_I$$
with $p_S(0)=1-q_0$, $p_I(0)=q_0$ has a unique solution on $[0,T]$. In particular $p_S(t)=(1-q_0)\exp\!\big(-\lambda\int_0^t\mathcal J\big)$, and $f_I$ solves the fixed point $f_I(t;u)=e^{-t}f_I(0;u-t)+\lambda\int_0^te^{-(t-s)}\mathcal J(s)p_S(s)\,ds$.

**Theorem (joint FLLN).** As $n\to\infty$, $(F_n(t;\cdot))_{t\le T}\Rightarrow(F(t;\cdot))_{t\le T}$ in the Skorokhod space over distributions with the Lévy metric, and jointly the empirical graphons converge, $(h^{G_n(t)})_{t\le T}\Rightarrow(g^{[F]}(t;\cdot,\cdot))_{t\le T}$, in the space of graphons with the cut distance.

## Depends on

- [Epidemics on networks](../epidemics-on-networks/README.md)

## Expansion

The difficulty is the two-way feedback: edges depend on vertex states and vice versa. The proof constructs a **mimicking process** in which edges respond only to a deterministic mean-field type distribution, a one-way feedback, so that edges are conditionally independent given the types and existing graphon limits for dense graphs with independently evolving edges apply. A coupling then shows that the true and mimicking graphs stay within $\delta$ in $L^1$ graphon norm except on events of sub-exponential probability, $\frac1n\log\mathbb P(\cdot)\to0$. The map $F\mapsto g^{[F]}$ is continuous, which transfers convergence of types to convergence of graphs. Allowing the edge rates to depend on the global susceptible and infected proportions (behavioral response through rewiring) is a methodological extension. In simulations this feedback produces multiple epidemic peaks, and the speed of graph evolution $\gamma$ controls the peak height and the final epidemic size.

## Sources

- S. Baldassarri, P. Braunsteins, F. den Hollander, M. Mandjes, "Infection models on dense dynamic random graphs", arXiv:2602.14562 (2026), Section 2 (model definition, Theorems 2.1-2.2), Section 3 (illustrations), Section 4 (Properties 4.1-4.3) and Section 5 (Lemmas 5.1-5.2), <https://doi.org/10.48550/arXiv.2602.14562>.
