# Exponential absorption time of the voter model with quenched habitat preferences

**Model.** $N$ sites each hold one of two species, $\eta_i \in \{0,1\}$. The environment is a quenched i.i.d. field $h_1, \dots, h_N \in \{0,1\}$ with $\mathbb P(h_i = 1) = q \in (0,1)$, giving each site a preferred species; fix $\rho \in [0,1]$. At rate $1$ each site $i$ picks a uniformly random site $j$; if $\eta_j = h_i$ it copies $\eta_j$, and if $\eta_j \ne h_i$ it copies $\eta_j$ only with probability $\rho$. For $\rho = 1$ this is the neutral voter (Moran) model, whose mean absorption time is $\sim N\ln 2$. Track the macroscopic order parameters

$$m_N^+ = \frac1N\sum_{i} h_i\eta_i, \qquad m_N^- = \frac1N\sum_i (1-h_i)\eta_i,$$

the fractions of sites occupied by species $1$ in habitats preferring $1$ and $0$, respectively. Let $\tau_N$ be the time to reach monodominance (one of the two absorbing states).

**Theorem 1 (law of large numbers).** If $m_N^\pm(0) \to \bar m^\pm$ in probability with $(\bar m^+, \bar m^-) \in [0,q] \times [0,1-q]$, then $(m_N^+(t), m_N^-(t))$ converges in distribution to the solution of

$$\dot m^+ = -\rho\,m^+(1 - m^- - m^+) + (q - m^+)(m^+ + m^-), \qquad \dot m^- = -m^-(1 - m^- - m^+) + \rho\,(1 - q - m^-)(m^+ + m^-).$$

For $q \ge 1/2$: if $\frac{1-q}{q} < \rho < 1$ the monodominance state $(q, 1-q)$ (all sites species $1$) attracts every initial condition except $(0,0)$; if $\rho < \frac{1-q}{q}$ both absorbing states are unstable and an interior coexistence equilibrium attracts all other initial conditions. For $q = 1/2$ only the second regime occurs.

**Theorem 2 (metastable coexistence).** Let $q = 1/2$ and $\rho < 1$, so that the limit system has an interior (coexistence) equilibrium $\mathbf z$ attracting the interior $D$ of its domain. Let $V$ be the Freidlin–Wentzell quasipotential of the jump process relative to $\mathbf z$, with local rates $r_1(\mathbf x) = (1/2 - x)(x+y)$, $l_1(\mathbf x) = \rho x(1-x-y)$, $r_2(\mathbf x) = \rho(1/2 - y)(x+y)$, $l_2(\mathbf x) = y(1-x-y)$. Then $V(\mathbf x) > 0$ for $\mathbf x \ne \mathbf z$, and for almost every realization of the environment and every $\varepsilon > 0$,

$$\lim_{N\to\infty}\mathbb P_h\Big(e^{N(V_{\partial D} - \varepsilon)} \le \tau_N \le e^{N(V_{\partial D} + \varepsilon)}\Big) = 1, \qquad V_{\partial D} = \min_{\mathbf x \in \partial D} V(\mathbf x) > 0.$$

Any amount of habitat heterogeneity ($\rho < 1$) thus turns the linear-in-$N$ fixation time of neutral drift into an exponentially long coexistence. Near $\mathbf z$, the rescaled fluctuations $\sqrt N\,(m_N - \mathbf z)$ converge to a Gauss–Markov (Ornstein–Uhlenbeck) process whose drift carries an additional quenched Gaussian term from the environment.

## Expansion

The pair $(m^+_N, m^-_N)$ is a density-dependent jump Markov process with increments $\pm 1/N$ in each coordinate at rates $N r_i$ and $N l_i$; Kurtz's theorem gives the ODE limit, the quenched environment entering only through the law of large numbers for $\sum_i h_i/N$. The Hamiltonian $H(\mathbf x, \boldsymbol\alpha) = \sum_i [r_i(e^{\alpha_i} - 1) + l_i(e^{-\alpha_i} - 1)]$ and its Legendre transform give the large-deviation action; exit from the basin of $\mathbf z$ costs $V_{\partial D}$, and the classical Freidlin–Wentzell exit-time estimate, adapted to the degenerate rates on the boundary, yields the exponential bounds.

## Sources

- Claudio Borile, Paolo Dai Pra, Markus Fischer, Marco Formentin, "Time to absorption for a heterogeneous neutral competition model", arXiv (2013). Section 2 (model, Theorem 1), Section 3 (Theorem 2), Section 4 (Theorem 3, normal fluctuations). <https://doi.org/10.48550/arXiv.1311.4368>. Published version: Journal of Statistical Physics 156(1) (2014), 119–130, <https://doi.org/10.1007/s10955-014-0989-8>; locators above refer to the arXiv version.
