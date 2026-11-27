# Basic reproduction number of the multigroup delayed prion model

**Model.** Consider $n \ge 2$ neurons. Neuron $i$ carries normal prion protein $x_i(t) \ge 0$ (PrP$^C$) and misfolded prion protein $y_i(t) \ge 0$ (PrP$^{Sc}$), and

$$\frac{dx_i}{dt} = K_i\,\beta\big(y_i(t-T_i)\big) - \mu_i x_i(t) - d\,x_i(t)\Big(y_i(t) + \sum_{j \ne i} \kappa_{ji}\,\alpha_{j\to i}\,y_j(t)\Big),$$

$$\frac{dy_i}{dt} = d\,x_i(t)\Big(y_i(t) + \sum_{j \ne i} \kappa_{ji}\,\alpha_{j\to i}\,y_j(t)\Big) - \alpha_i\,y_i(t), \qquad \alpha_i := \sum_{j \ne i} \alpha_{i\to j},$$

with production rates $K_i > 0$, degradation rates $\mu_i > 0$, conversion rate $d > 0$, delays $T_i \ge 0$, migration (and loss) rates $\alpha_{i\to j} \ge 0$ with $\alpha_i > 0$, cross-neuron interaction factors $\kappa_{ji} \in [0,1]$, and a decreasing production feedback $\beta(y) = 1/(1 + (y/y_c)^p)$ with $\beta(0) = 1$, $\beta'(0) = 0$. Initial data are $(x_{i0}, \varphi_i) \in \mathbb{R}_+ \times C([-T,0], \mathbb{R}_+)$ with $T = \max_i T_i$. Solutions with nonnegative data stay nonnegative and bounded, and the disease-free equilibrium is

$$E_0 = \Big(\frac{K_1}{\mu_1}, \dots, \frac{K_n}{\mu_n}, 0, \dots, 0\Big).$$

**Proposition.** Let $R_{0i} = d K_i / (\mu_i \alpha_i)$ be the basic reproduction number of the isolated neuron $i$. The basic reproduction number of the network is $\mathcal{R}_0 = \rho(F)$, the spectral radius of the nonnegative $n \times n$ matrix

$$F_{ij} = \begin{cases} R_{0i}, & j = i, \\ \kappa_{ji}\,\alpha_{j\to i}\,R_{0i}, & j \ne i. \end{cases}$$

For $n = 2$ with $\kappa_{12} = \kappa_{21} = \kappa$, $\alpha_{1\to 2} = \alpha_1$, $\alpha_{2\to 1} = \alpha_2$,

$$\mathcal{R}_0 = \frac{R_{01} + R_{02} + \sqrt{(R_{01} - R_{02})^2 + 4\kappa^2\alpha_1\alpha_2 R_{01}R_{02}}}{2}.$$

## Depends on

- [Basic reproduction number as a spectral radius](../../../epidemiology/next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof sketch

At $E_0$ the delayed term enters the linearization only through $\beta'(0) = 0$, so the linearized $y$-subsystem is an ODE $\dot y = (M - V)y$ with new-infection matrix $M_{ij} = d (K_i/\mu_i)$ for $j = i$ and $d (K_i/\mu_i)\kappa_{ji}\alpha_{j\to i}$ for $j \ne i$, and removal matrix $V = \mathrm{diag}(\alpha_i)$. The next-generation matrix $M V^{-1}$ has the same spectrum as $V^{-1}M = F$ up to similarity by $V$, which gives $\mathcal{R}_0 = \rho(F)$. Coupling can make the network supercritical even when every $R_{0i} < 1$, since the off-diagonal entries raise the Perron root.

## Sources

- Mostafa Adimy, Abdennasser Chekroun, Laurent Pujo-Menjouet and Mattia Sensi, "A multigroup approach to delayed prion production", *Discrete and Continuous Dynamical Systems - B* 29 (2024), 2972–2998, <https://doi.org/10.3934/dcdsb.2023209>. Preprint version: arXiv:2307.05524 (2023), Section 2 (two-neuron eigenvalue formula), Section 3 (system and Propositions 1 and 2), <https://doi.org/10.48550/arXiv.2307.05524>.
