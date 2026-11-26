# Quasi-stationary distributions of small-noise population chains concentrate on interior attractors

**Model.** For a system size $N$, let $X^N_k$ be a Markov chain on the lattice $\Delta_N = \{x \in \mathbb{R}^d_{\ge 0} : Nx \in \mathbb{Z}^d\}$ of scaled type counts of a $d$-type population,

$$X^N_{k+1} = X^N_k + \tfrac{1}{N}\eta^N_{k+1}(X^N_k),$$

where the increment $\eta^N(x) \in \mathbb{Z}^d$ has law $\theta^N(\cdot\mid x)$ supported in $\prod_i[-Nx_i,\infty)$. The boundary $\partial\Delta$ (some type extinct) is absorbing. A **quasi-stationary distribution** (QSD) is a probability $\mu_N$ on the interior $\Delta_N^o$ with $\mathbb{P}_{\mu_N}[X^N_k = j \mid X^N_k \in \Delta^o_N] = \mu_N(j)$ for all $j$ and $k$.

**Assumptions.** (i) Law of large numbers: the time-interpolated chain $\hat X^N(t)$ converges, uniformly on compact time intervals in probability, to the flow $\varphi_t$ of a Lipschitz ODE $\dot\varphi = G(\varphi)$. (ii) The flow has finitely many closed chain-recurrence classes $K_1,\dots,K_v$ in the interior (for the absorption-preserving pseudo-orbit order), of which $K_1,\dots,K_l$ ($l<v$) are quasi-attractors; each class has a point whose forward orbit is dense in it; near the boundary $G_i(x) > m x_i$ for small $x_i$ and $\sup_{x_i\le\delta}G_i \to 0$ as $\delta\to 0$; and $\langle x, G(x)\rangle \le -\kappa\|x\|^2$ for large $\|x\|$. (iii) The increments have finite exponential moments converging to those of a limit kernel whose support has full convex hull. (iv) The chain is irreducible on $\Delta^o_N$, and from near the boundary absorption by a fixed time has probability at least $e^{-\gamma N}$ for every $\gamma>0$, asymptotically.

**Theorem.**
1. If each $X^N$ has a QSD $\mu_N$ and $\{\mu_N\}$ is relatively compact on $\Delta^o$, then every weak limit point $\mu$ is invariant under $\{\varphi_t\}$ and supported on $K_1 \cup \dots \cup K_l$, the interior attractors.
2. With $\lambda_N = [\mathbb{P}_{\mu_N}(X^N_1 \in \Delta^o)]^N$, there are $c>0$ and $N_0$ with $\lambda_N \ge 1 - e^{-cN}$ for $N \ge N_0$: the extinction time from quasi-stationarity grows exponentially in $N$.
3. (Binomial-Poisson model) If each individual dies with probability $1/N$ per step and type-$i$ births are $\mathrm{Poisson}(F_i(x))$, with $F$ bounded Lipschitz and $G = F - x$ satisfying (ii) without the growth condition, then for each $N$ the conditioned laws $\delta_{x_N}P^N_n / \delta_{x_N}P^N_n(\mathbf{1}_{\Delta^o_N})$ converge in total variation to a QSD $\mu_N$, the family $\{\mu_N\}$ is relatively compact, and conclusions 1 and 2 hold.

## Expansion

Uniform Freidlin-Wentzell large deviation estimates on compacts show that escaping from an attractor to the boundary costs probability $e^{-N\cdot(\text{quasipotential barrier})}$, while being absorbed from near the boundary costs only subexponentially. Mass of the QSD near the boundary, or on non-attracting recurrence classes, would therefore leak to extinction faster than the QSD's survival rate allows. Invariance of limit points follows from the law of large numbers, and the Poincaré recurrence theorem restricts the support to chain-recurrent points, of which only quasi-attractors survive. This extends the discrete-time compact-state results of Faure and Schreiber to unbounded state spaces and continuous-time limits.

## Sources

- Amarjit Budhiraja, Nicolas Fraiman and Adam Waterbury, "Asymptotics of Quasi-Stationary Distributions of Small Noise Stochastic Dynamical Systems in Unbounded Domains", arXiv:1911.06707 (2019), Section 2, Assumptions 1-4, Theorems 2.1 and 2.2, <https://doi.org/10.48550/arXiv.1911.06707>.
