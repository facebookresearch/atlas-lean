# Bistability of a five-compartment tumour angiogenesis model

Let $C, E, T, P, A \ge 0$ be the concentrations of normal cells, pre-existing vascular (epithelial) cells, cancer cells, pre-angiogenesis (sprout) cells and angiogenesis cells, evolving for $t > 0$ by

$$\begin{aligned}
\dot C &= \alpha_1 C\Bigl(1 - \frac{C}{k_1}\Bigr) - \beta_1 CT - \mu_1 C, &
\dot E &= \alpha_2 E\Bigl(1 - \frac{E}{k_2}\Bigr) - \gamma ET - \mu_2 E,\\
\dot T &= \alpha_3 AT\Bigl(1 - \frac{T}{k_3}\Bigr) - \beta_2 CT - \mu_3 T, &
\dot P &= \gamma ET - (\delta + \mu_4) P,\\
\dot A &= \delta P + \varepsilon TA\Bigl(1 - \frac{A}{k_4}\Bigr) - \mu_5 A,
\end{aligned}$$

with all parameters positive, started from a cancer-free state perturbed at $t = 0$ by mutation of $C_m$ normal cells: $(C, E, T, P, A)(0) = (C_0 - C_m, E_0, C_m, 0, 0)$.

1. If $\alpha_1 > \mu_1$ and $\alpha_2 > \mu_2$, the cancer-free equilibrium $Q_0 = (C_0, E_0, 0, 0, 0)$ with $C_0 = k_1(\alpha_1 - \mu_1)/\alpha_1$ and $E_0 = k_2(\alpha_2 - \mu_2)/\alpha_2$ exists and is always locally asymptotically stable: its Jacobian eigenvalues are $-\mu_5$, $-(\mu_4 + \delta)$, $-(\mu_3 + \beta_2 C_0)$, $-(\alpha_1 - \mu_1)$ and $-(\alpha_2 - \mu_2)$.
2. A coexistence equilibrium has $\bar C = k_1[(\alpha_1 - \mu_1) - \beta_1\bar T]/\alpha_1$, $\bar E = k_2[(\alpha_2 - \mu_2) - \gamma\bar T]/\alpha_2$, $\bar P = \gamma\bar E\bar T/(\mu_4 + \delta)$, and $\bar T$ a root of a polynomial equation $f(T) = g(T)$ of degree four; biological feasibility requires $\bar T < \min\{(\alpha_1 - \mu_1)/\beta_1,\ (\alpha_2 - \mu_2)/\gamma,\ k_3\}$, which leaves at most two feasible roots $T_< < T_>$.

**Numerical observation (not part of the statement).** At the source's parameter values (its Table 2) there are two feasible roots, the small equilibrium $Q_<$ is unstable and the large one $Q_>$ is stable (eigenvalues in its Table 3), and simulations show $Q_<$ acting as a break-point: initial conditions on one side of the hypersurface through it go to the cancer-free state $Q_0$, on the other side to $Q_>$, so cancer establishment depends on the size of the initial perturbation $C_m$. Varying the inhibition $\beta_2$ of cancer cells by normal cells, the two roots $T_<$ and $T_>$ merge at a threshold $\beta_2^{\mathrm{th}}$ (computed there as $\beta_2^{\mathrm{th}}=4.8376\times10^{-2}$, with $T_<=T_>=0.7053$), above which $Q_0$ is the only feasible equilibrium and cancer cannot be maintained.

## Expansion

At $Q_0$ the row of the Jacobian for $T$ has only its diagonal entry, and deleting that row and column leaves a triangular matrix, which gives the five eigenvalues directly; none depends on the angiogenesis parameters, so the cancer-free state can never lose stability and invasion requires a large enough perturbation. Setting the derivatives to zero and eliminating $C, E, P, A$ in favour of $T$ gives the polynomial condition; positivity of $\bar C$, $\bar E$ and $\bar A$ gives the feasibility constraints. The instability of $Q_<$, the stability of $Q_>$, the separatrix and the threshold $\beta_2^{\mathrm{th}}$ are established numerically in the source (eigenvalue table and bifurcation diagrams in $\beta_2$ and the sprouting rate $\gamma$, including a Hopf-type limit cycle for intermediate $\gamma$).

## Sources

- H. M. Yang, "Mathematical modeling of solid cancer growth with angiogenesis", Theoretical Biology and Medical Modelling 9 (2012) 2, <https://doi.org/10.1186/1742-4682-9-2>, PMCID PMC3344686. System (1)–(2), steady states (3)–(9), the stability analysis of $Q_0$, and the numerical results at the Table 2 parameter values (Table 3, Figure 1 and the bifurcation diagram in $\beta_2$, Figure 7).
