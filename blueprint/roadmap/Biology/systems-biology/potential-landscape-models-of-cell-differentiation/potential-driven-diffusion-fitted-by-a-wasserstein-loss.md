# Potential-driven diffusion fitted to single-cell time series by a Wasserstein loss

Model the state $X(t) \in \mathbb{R}^k$ of a differentiating cell (for example its leading expression principal components) by the stochastic differential equation

$$dX(t) = \mu(X(t))\, dt + \sqrt{2\sigma^2}\, dW(t), \qquad \mu(x) = -\nabla \Psi(x),$$

where $W$ is a standard Brownian motion and $\Psi : \mathbb{R}^k \to \mathbb{R}$ is a potential, simulated by the Euler-Maruyama scheme $X(t + \Delta t) = X(t) + \mu(X(t))\Delta t + \sqrt{2\sigma^2 \Delta t}\, Z(t)$ with i.i.d. standard Gaussian $Z(t)$. Given only unpaired samples $\{x(t)_i \sim \rho(\cdot, t)\}_{i \le m_t}$ of the marginal law at observation times $t_1, \dots, t_n$, the potential is chosen in a function class $\mathcal{K}$ to solve

$$\min_{\Psi \in \mathcal{K}} \; \sum_{i=1}^{n} W_2\big(\hat\rho(t_i, \cdot), \rho_\Psi(t_i, \cdot)\big)^2 + \tau \sum_{j=1}^{m_n} \frac{\Psi(x_j)}{\sigma^2},$$

where $\hat\rho(t_i,\cdot)$ is the empirical distribution of the cells observed at $t_i$, $\rho_\Psi(t_i,\cdot)$ the distribution obtained by simulating the model forward from the previous time point, $W_2$ the quadratic Wasserstein distance and $\tau \ge 0$ the weight of an entropic regularizer.

## Expansion

The marginal density of the diffusion solves the Fokker-Planck equation $\partial_t \rho = \nabla\cdot(\rho \nabla\Psi) + \sigma^2 \Delta\rho$, whose stationary solution, when normalizable, is the Gibbs density $\propto e^{-\Psi/\sigma^2}$; cells therefore flow from high to low potential and accumulate in its basins, which play the role of fates in Waddington's landscape. Because cells are destroyed by sequencing, trajectories are never observed and individual cells at different times are indistinguishable; the Wasserstein distance between point clouds is the analogue, for cross-sections of indistinguishable particles, of the Euclidean error between observed and predicted trajectory points. In PRESCIENT, $\Psi$ is a two-layer neural network, $\mu = -\nabla\Psi$ is obtained by automatic differentiation, $W_2$ is approximated by a multiscale Sinkhorn algorithm, and the fitted model is used to simulate trajectories from unseen initial states and from in-silico perturbed expression profiles.

## Sources

- G. H. T. Yeo, S. D. Saksena and D. K. Gifford, "Generative modeling of single-cell time series with PRESCIENT enables prediction of cell trajectories with interventions", Nature Communications 12 (2021), <https://doi.org/10.1038/s41467-021-23518-w> (PMC8163769). Methods, Equations (1)-(3).
