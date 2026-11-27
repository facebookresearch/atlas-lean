# Super-Brownian limit of long-range SIR epidemics in four or more dimensions

**Model.** Fix $d \ge 4$, an infection range $R \in \mathbb{N}$ and $\theta \in \mathbb{R}$. On the lattice $\mathbb{Z}^d / R$, two sites $x \ne y$ are neighbors if $\|x - y\|_\infty \le 1$. Each site is susceptible, infected or recovered. In the spatial SIR epidemic, each infected site recovers at rate $1$ and, at rate $\beta = 1 + \theta/N$, picks a uniformly random neighbor and infects it if that neighbor is susceptible (attempts on infected or recovered sites are suppressed); recovered sites are permanently immune. The scaling parameter $N$ is tied to $R$ by

$$R^d = N \ \ (d \ge 5), \qquad R^d = N \log N \ \ (d = 4).$$

Rescale time by $N$ and space by $\sqrt{N}$, and let $X^N_t = \frac{1}{N}\sum_{x \text{ infected at time } t} \delta_x$, a finite measure on $\mathbb{R}^d$.

**Theorem.** Suppose no site is recovered at time $0$. If $X^N_0 \to X_0$ in the space $M_F(\mathbb{R}^d)$ of finite measures, where $X_0$ has no atoms, then $(X^N_t)_{t \ge 0}$ converges weakly (in the Skorokhod space of measure-valued paths) to a super-Brownian motion $X$ started at $X_0$ with branching rate $\gamma_0 = 2$, diffusion coefficient $\sigma_0^2 = 1/3$ and drift $\theta_0 = \theta - b_d$; that is, for all $\phi \in C_b^2(\mathbb{R}^d)$,

$$X_t(\phi) - X_0(\phi) - \int_0^t X_s\!\left(\tfrac{\sigma_0^2}{2}\Delta\phi + \theta_0\,\phi\right) ds$$

is a continuous martingale with quadratic variation $\gamma_0 \int_0^t X_s(\phi^2)\,ds$. Here $b_4 = 9/(2\pi^2)$, and for $d \ge 5$, $b_d \in (0, \infty)$ is an explicit series of random-walk hitting probabilities measuring the rate at which births are lost to already-infected or recovered neighbors.

## Expansion

Without suppression the process is a critical branching random walk, which rescales to super-Brownian motion with branching rate $2$ and diffusion coefficient $1/3$ (the variance of a uniform step in $[-1,1]$). The choice of $N$ makes the expected number of previously visited sites in a neighborhood of a typical particle of order $R^d/N$, so suppressed births remove mass at rate of order one, which appears in the limit as the constant negative drift $-b_d$. The proof couples the epidemic with branching random walks from above and below and shows the gap between their masses vanishes. The same scaling matches the asymptotics of the critical probability of range-$R$ bond percolation.

## Sources

- Jieliang Hong, "Rescaled SIR Epidemic Processes Converge to Super-Brownian Motion in Four or More Dimensions", Memoirs of the American Mathematical Society 320 (2026), <https://doi.org/10.1090/memo/1629>; numbering as in arXiv:2309.08926: Theorem 1.1.
