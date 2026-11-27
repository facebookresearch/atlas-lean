# Well-posedness and existence of an optimal transmission rate in reaction–diffusion SIRS estimation

**Model.** Let $\Omega \subset \mathbb{R}^2$ be a bounded Lipschitz domain, $Q = (0,T)\times\Omega$, and let $y_1, y_2, y_3$ be the densities of susceptible, infected and recovered hosts with total density $y = y_1 + y_2 + y_3$. With positive diffusion coefficients $d_i$, birth/death rate $\mu$, recovery rate $\gamma$, loss-of-immunity rate $\kappa$ and a time-dependent infection rate $\beta(t)$,

$$\partial_t y_1 - d_1\Delta y_1 = \mu(y - y_1) - \beta\frac{y_1 y_2}{y} + \kappa y_3, \qquad \partial_t y_2 - d_2\Delta y_2 = \beta\frac{y_1 y_2}{y} - (\gamma + \mu) y_2, \qquad \partial_t y_3 - d_3\Delta y_3 = \gamma y_2 - (\kappa + \mu) y_3,$$

with homogeneous Neumann (no-flux) boundary conditions and initial data $y_{i,0}$.

**Estimation problem.** Given observed infected densities $y_2^d$ and $\omega > 0$, minimize

$$J(y,\beta) = \frac12\int_Q (y_2 - y_2^d)^2\, dx\, dt + \frac{\omega}{2}\int_Q \beta^2\, dx\, dt$$

over $\beta \in L^\infty(0,T)$ with $\beta_{\min} \le \beta \le \beta_{\max}$ a.e., $\beta_{\min} \ge 0$, subject to the model.

**Theorem.**

1. *(Existence.)* For every admissible $\beta$ the model has a bounded weak solution.
2. *(Uniqueness and positivity.)* If moreover $y_{i,0} \in L^2(\Omega)$ are nonnegative, the weak solution is unique and nonnegative.
3. *(Threshold.)* For constant $\beta$, solutions remain stable near the disease-free equilibrium when $\beta/(\gamma + \mu) < 1$ and near the endemic equilibrium when $\beta/(\gamma + \mu) > 1$.
4. *(Optimal rate.)* The estimation problem has at least one globally optimal minimizer $\beta \in L^\infty(0,T)$.
5. *(Differentiability.)* The control-to-state maps $\beta \mapsto y_i$ from $L^\infty(0,T)$ to $W(0,T) \cap C(\bar Q)$ are Fréchet differentiable; the derivative in a direction is the solution of the linearized system $\partial_t u_i - d_i\Delta u_i = \sum_j \partial_{y_j} f_i\, u_j + \partial_\beta f_i$ with zero Neumann and initial data, where $f_i$ are the reaction terms.

## Depends on

- [Solution of the Kermack–McKendrick SIR system](../../kermack-mckendrick-sir-model/is-solution.md)

## Expansion

Summing the three equations shows that $y$ solves a linear heat equation and stays bounded, which makes the incidence $y_1 y_2/y$ Lipschitz on the invariant region and gives existence by a Galerkin or fixed-point argument; testing with negative parts gives positivity and Gronwall gives uniqueness. Linearizing the reaction terms at the homogeneous equilibria, the Neumann Laplacian only adds nonpositive eigenvalues $-d_i\lambda_k$, so stability is decided by the spatially constant mode, where the infected equation has growth rate $\beta - (\gamma + \mu)$. For the optimal rate, a minimizing sequence is bounded in $L^\infty$ and has a weak-$*$ convergent subsequence; the states are bounded in $W(0,T)$ and converge strongly in $L^2(Q)$ by Aubin–Lions, which suffices to pass to the limit in the term linear in $\beta$, and $J$ is weakly lower semicontinuous. Differentiability yields the adjoint-based gradient used in projected-gradient fitting to hospitalization data.

## Sources

- Karunia Putra Wijaya, "Estimation of time-space-varying parameters in dengue epidemic models", Communication in Biomathematical Sciences 1 (2017), 13, <https://doi.org/10.5614/cbms.2017.1.1.2>. Published version of arXiv:1711.04341, cited next; locators there refer to the arXiv version.
- Karunia Putra Wijaya, Thomas Goetz, "Estimation of time-space-varying parameters in dengue epidemic models", arXiv (2017). Section 2 (model and estimation problem), Theorems 3.1, 3.2, 4.1, Lemmas 3.3, 3.4, 5.1. <https://doi.org/10.48550/arXiv.1711.04341>
