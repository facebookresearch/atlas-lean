# Scaling limits of particle–agent pairing with a fixed number of agents

**Model.** $N$ particles of $J$ types, $C^N_j$ of type $j$ with $C^N_j/N \to c_j \in (0, 1)$, $\sum_j c_j = 1$, interact with $C^N_Z$ agents (e.g. regulatory molecules in a cell). A given free particle of type $j$ and a given free agent pair at rate $\lambda_j$; a pair of type $j$ splits at rate $\eta_j$. With $F^N_j(t)$ the number of free type-$j$ particles, the free-agent count is $C^N_Z - N + \sum_j F^N_j$, and $(F^N_j)$ is a Markov chain with jumps $+e_j$ at rate $\eta_j(C^N_j - x_j)$ and $-e_j$ at rate $\lambda_j x_j (C^N_Z - N + \|x\|)$. Write $\rho_j = \eta_j/\lambda_j$.

**Theorem.**

1. *(Overloaded case, $C^N_Z/N \to r < 1$.)* If $F^N(0)/N \to \bar f_0$ with $\sum_j \bar f_{0,j} = 1 - r$ and the initial number of free agents is fixed, then $F^N(t)/N$ converges to the solution of

    $$\dot f_j = \lambda_j f_j\,\frac{\langle \eta, c - f\rangle}{\langle \lambda, f\rangle} - \eta_j(c_j - f_j),$$

    whose equilibrium is $f_{j,\infty} = \dfrac{\eta_j c_j}{\eta_j + \lambda_j h_\infty}$, where $h_\infty = \phi(1 - r)$ and $\phi(y)$ is the unique solution of $\sum_j \frac{\rho_j c_j}{\rho_j + \phi(y)} = y$. The number of free agents stays of order one, and $h_\infty$ is its effective mean level.

2. *(Critical case, $C^N_Z = N$.)* If $F^N(0)/\sqrt N \to \bar f_0$, then $F^N(t/\sqrt N)/\sqrt N$ converges to the solution of

    $$\dot{\bar f}_j = c_j\eta_j - \lambda_j \bar f_j\,\|\bar f\|, \qquad \bar f_{j,\infty} = \frac{c_j\rho_j}{\sqrt{c_1\rho_1 + \cdots + c_J\rho_J}},$$

    so only $O(\sqrt N)$ particles are free, the relaxation time is of order $1/\sqrt N$, and fluctuations around this limit are of order $N^{1/4}$ (a functional CLT). The chain is reversible with explicit product-form invariant law $\pi_N(x) \propto \frac{1}{\|x\|!}\prod_j \rho_j^{x_j}\binom{C^N_j}{x_j}$.

## Expansion

The pairing rate is quadratic (particles times free agents), which separates time scales. With fewer agents than particles, agents are almost all bound, the free-agent count is a fast process with an $O(1)$ stationary law, and averaging it out yields the slow ODE whose equilibrium matches the conservation $\sum_j f_{j,\infty} = 1 - r$. When agents and particles are equally numerous, free particles and free agents coincide in number; the balance $\eta_j c_j N \approx \lambda_j F_j \|F\|$ forces $\|F\| \sim \sqrt N$, which sets both the size and the speed of the limit. These regimes model how a cell's limited pool of binding agents is shared among competing substrates.

## Sources

- Vincent Fromion, Philippe Robert and Jana Zaherddine, "A stochastic analysis of particle systems with pairing", Stochastic Processes and their Applications 178 (2024), 104480, <https://doi.org/10.1016/j.spa.2024.104480>; numbering as in arXiv:2310.04833: Proposition 5, Corollary 6, Theorems 9–10 and Proposition 11 (Section 3).
