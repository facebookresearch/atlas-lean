# Fossilized birth–death process and its diversification parameterization

The fossilized birth–death (FBD) process with speciation rate $\lambda$, extinction rate $\mu$, fossil-sampling rate $\psi \ge 0$, extant sampling probability $\rho \in (0, 1]$ and origin time $x_0 > 0$ (measured back from the present) is the following random sampled tree. A single lineage starts at time $x_0$; each lineage independently splits at rate $\lambda$, goes extinct at rate $\mu$, and leaves a fossil sample at the points of a Poisson process of rate $\psi$; at the present each surviving lineage is sampled independently with probability $\rho$. The sampled tree is the subtree spanned by the samples, conditioned on at least one sampled extant lineage. A fossil sample that lies on the path from the origin to another sample appears as a degree-two node, a *sampled ancestor*.

For $\lambda > \mu > 0$ and $\psi \ge 0$, define the net diversification rate, the turnover and the fossil-sampling proportion

$$d = \lambda - \mu, \qquad \nu = \frac{\mu}{\lambda}, \qquad s = \frac{\psi}{\mu + \psi}. \tag{2}$$

1. The map $(\lambda, \mu, \psi) \mapsto (d, \nu, s)$ is a bijection from $\{\lambda > \mu > 0,\ \psi \ge 0\}$ onto $(0, \infty) \times (0, 1) \times [0, 1)$, with inverse

$$\lambda = \frac{d}{1 - \nu}, \qquad \mu = \frac{\nu d}{1 - \nu}, \qquad \psi = \frac{s\, \mu}{1 - s}.$$

2. $s$ is the probability that a lineage leaves a fossil sample before it goes extinct, counting only these two events (sampling at rate $\psi$, extinction at rate $\mu$).

## Expansion

From $\nu = \mu/\lambda$ and $d = \lambda - \mu = \lambda(1 - \nu)$ one solves $\lambda = d/(1 - \nu)$ and $\mu = \nu\lambda$, and $s(\mu + \psi) = \psi$ gives $\psi = s\mu/(1 - s)$; each step is invertible on the stated ranges. The interpretation of $s$ is the competing-exponentials identity $\mathbb{P}(E_\psi < E_\mu) = \psi/(\psi + \mu)$ for independent exponential clocks of rates $\psi$ and $\mu$. Conditioning on the origin time rather than on the age of the crown node allows the oldest fossil to be ancestral or sister to all other samples. For penguins (19 extant and 36 fossil species), the posterior means were $d = 0.039$ (95% HPD $[0.002, 0.089]$), $\nu = 0.88$ ($[0.72, 1]$) and $s = 0.23$ ($[0.06, 0.43]$). A birth–death prior without sampled ancestors pushed divergence times into the past and raised the mean of $d$ to $0.092$.

## Sources

- A. Gavryushkina, T. A. Heath, D. T. Ksepka, T. Stadler, D. Welch, A. J. Drummond, "Bayesian total-evidence dating reveals the recent crown radiation of penguins", Systematic Biology (2017), Methods, "Modeling the Speciation Process", Eq. (2), and Results (diversification parameters and the comparison without sampled ancestors), <https://doi.org/10.1093/sysbio/syw060> (PMC5410945).
