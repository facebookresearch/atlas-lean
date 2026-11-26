# Ribosome flow model and its globally attracting steady state

**Model.** An mRNA is coarse-grained into $n$ consecutive sites; $x_i(t) \in [0,1]$ is the normalized ribosome occupancy of site $i$ ($1$ full, $0$ empty). With initiation rate $\lambda_0 > 0$ and transition rates $\lambda_1, \dots, \lambda_n > 0$ ($\lambda_n$ the exit rate),

$$\begin{aligned}
\dot x_1 &= \lambda_0 (1 - x_1) - \lambda_1 x_1 (1 - x_2),\\
\dot x_i &= \lambda_{i-1} x_{i-1}(1 - x_i) - \lambda_i x_i (1 - x_{i+1}), \qquad 2 \le i \le n-1,\\
\dot x_n &= \lambda_{n-1} x_{n-1}(1 - x_n) - \lambda_n x_n ,
\end{aligned}$$

and the translation (protein production) rate is $R(t) = \lambda_n x_n(t)$. The flow from site $i$ to $i+1$ is proportional to the occupancy of site $i$ and the vacancy of site $i+1$, the mean-field version of the exclusion rule of TASEP. The unit cube $C^n = [0,1]^n$ is invariant.

**Theorem.** The RFM admits a unique equilibrium $e \in \operatorname{int} C^n$, and $\lim_{t\to\infty} x(t, a) = e$ for every initial condition $a \in C^n$. Moreover the flow is non-expanding in the $\ell_1$ norm:

$$|x(t, a) - x(t, b)|_1 \le |a - b|_1 \qquad \text{for all } a, b \in C^n,\ t \ge 0 .$$

Hence the steady-state ribosome profile and translation rate $R = \lambda_n e_n$ are unique and depend only on the rates.

## Expansion

The Jacobian of the RFM is tridiagonal with nonnegative off-diagonal entries on $C^n$ ($\partial \dot x_i/\partial x_{i-1} = \lambda_{i-1}(1 - x_i) \ge 0$, $\partial \dot x_i/\partial x_{i+1} = \lambda_i x_i \ge 0$), so the system is cooperative; Smillie's theorem for strongly cooperative tridiagonal systems states that every bounded trajectory converges to an equilibrium. On the compact invariant cube the trajectories are bounded, and uniqueness of the equilibrium follows by solving the steady-state relations backward from the exit: equal flows $\lambda_n e_n = \lambda_{i} e_i (1 - e_{i+1}) = \lambda_0 (1 - e_1)$ determine $e$ from $R$ as a continued-fraction recursion with exactly one admissible root. The $\ell_1$ non-expansion follows because the column sums of the Jacobian are nonpositive, so its $\ell_1$ matrix measure is at most zero. Mean-field predictions of translation rates from the RFM agree closely with TASEP simulations over endogenous yeast genes.

## Sources

- M. Margaliot, E. D. Sontag, T. Tuller, "Entrainment to periodic initiation and transition rates in a computational model for gene translation", PLoS ONE 9 (2014) e96039, Introduction ("The ribosome flow model", equation (1), Theorem 1 and inequality (2)), <https://doi.org/10.1371/journal.pone.0096039>.
- M. Margaliot, T. Tuller, "Stability analysis of the ribosome flow model", IEEE/ACM Transactions on Computational Biology and Bioinformatics 9 (2012) 1545–1552, <https://doi.org/10.1109/TCBB.2012.88>.
