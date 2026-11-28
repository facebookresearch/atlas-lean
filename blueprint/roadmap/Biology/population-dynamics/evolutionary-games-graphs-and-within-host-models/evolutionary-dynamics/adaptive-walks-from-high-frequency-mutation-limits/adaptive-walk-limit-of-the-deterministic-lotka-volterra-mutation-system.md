# Adaptive-walk limit of the deterministic Lotka–Volterra mutation system

**Model.** Types are vertices of the hypercube $\{0,1\}^n$ (each locus mutant or not), with birth rates $b(x)$, death rates $d(x)$, net growth $r(x) = b(x) - d(x)$, competition kernel $\alpha(x,y) \ge 0$, and mutation probability $\mu$ per birth with mutant law $m(x, \cdot)$. Under assumption (A), $m(x,y) > 0$ iff $x$ and $y$ differ at exactly one locus ($x \sim y$). The large-population limit of the individual-based model is the ODE system

$$
\frac{d}{dt}\xi^\mu_t(x) = \Big[r(x) - \sum_{y} \alpha(x,y)\xi^\mu_t(y)\Big]\xi^\mu_t(x) + \mu \sum_{y \sim x} b(y) m(y,x) \xi^\mu_t(y) - \mu b(x) \xi^\mu_t(x).
$$

For a set $\mathbf{x}$ of types, (B$_{\mathbf{x}}$) asks for weights $\theta_x > 0$ with $\theta_x \alpha(x,y) = \theta_y \alpha(y,x)$ and $\sum_{x,y \in \mathbf{x}} \theta_x \alpha(x,y) u(x)u(y) > 0$ for $u \ne 0$; then (if all $r(x) > 0$) the mutation-free Lotka–Volterra system on $\mathbf{x}$ has a unique globally attracting equilibrium $\bar\xi_{\mathbf{x}}$. The *invasion fitness* of $y$ against residents $\mathbf{x}$ at equilibrium is $f_{y,\mathbf{x}} = r(y) - \sum_{x \in \mathbf{x}} \alpha(y,x)\bar\xi_{\mathbf{x}}(x)$.

**Invasion times.** Start with residents $\mathbf{x}^0$ near $\bar\xi_{\mathbf{x}^0}$ and every other type $y$ of order $\mu^{\lambda_y}$. Set $T_0 = 0$, $\rho^0_y = \min_z [\lambda_z + |z - y|]$, and recursively

$$
T_i = T_{i-1} + \min_{y : f_{y,\mathbf{x}^{i-1}} > 0} \frac{\rho^{i-1}_y}{f_{y,\mathbf{x}^{i-1}}}, \qquad y^i_* = \operatorname*{argmin}_{y : f_{y,\mathbf{x}^{i-1}} > 0} \frac{\rho^{i-1}_y}{f_{y,\mathbf{x}^{i-1}}},
$$

$$
\rho^i_y = \min_z \Big[\rho^{i-1}_z + |z - y| - (T_i - T_{i-1}) f_{z,\mathbf{x}^{i-1}}\Big],
$$

where $\rho^i_y$ is the $\mu$-exponent of the size of type $y$ at the $i$-th invasion and $\mathbf{x}^i$ is the support of the Lotka–Volterra equilibrium of $\mathbf{x}^{i-1} \cup \{y^i_*\}$.

**Theorem.** Assume (A) and (B$_{\mathbf{x}^{i-1} \cup y^i_*}$) for $1 \le i < I$, where $I$ is the first step at which the minimizer $y^i_*$ is not unique or some type in $(\mathbf{x}^{i-1} \cup y^i_*) \setminus \mathbf{x}^i$ has $f_{y,\mathbf{x}^i} \ge 0$ ($I = \infty$ if neither happens). Then for every $t \in [0, T_I)$ other than the $T_i$,

$$
\lim_{\mu \to 0} \xi^\mu_{t \ln(1/\mu)} = \sum_{i=0}^{I-1} \mathbf{1}_{T_i \le t < T_{i+1}} \sum_{x \in \mathbf{x}^i} \bar\xi_{\mathbf{x}^i}(x)\, \delta_x.
$$

On the time scale $\ln(1/\mu)$ the population jumps between Lotka–Volterra equilibria of coexisting types, like an adaptive walk or adaptive flight, but the next resident is chosen by the ratio of its accumulated mutational distance $\rho$ to its invasion fitness, not by a single mutation step; in a variant where mutants can only be produced within a limited radius, the source analyses when fitness valleys can be crossed.

## Expansion

Because $\mu$ is not separated from the population size, all types are present at microscopic sizes $\mu^{\rho}$ at once: mutation from a neighbour $z$ feeds type $y$ at order $\mu^{\rho_z + |z - y|}$, and each type grows or shrinks exponentially at rate $f_{y,\mathbf{x}}$ on the $\ln(1/\mu)$ scale, which gives the piecewise-linear recursion for the exponents. The first type whose exponent reaches $0$ becomes macroscopic and the resident community re-equilibrates in time $O(1)$, negligible on that scale; (B) supplies the weighted norm $\|u\|_{\mathbf{x}}^2 = \sum_x \theta_x u(x)^2/\bar\xi_{\mathbf{x}}(x)$, used to control convergence to the new equilibrium uniformly in $\mu$. The result extends to general finite directed mutation graphs with Hamming distance replaced by directed path length; the source also treats the special case of equal competition.

## Sources

- A. Kraut, A. Bovier, "From Adaptive Dynamics to Adaptive Walks", arXiv:1810.13188 (2018): Section 2 (Definitions 2.1–2.7, assumptions (A) and (B$_{\mathbf{x}}$), Theorem 2.4, invasion times and exponents, Theorem 2.8 and the remark on general graphs), Sections 3–4 (invasion analysis, construction of the jump process), Sections 5–6 (equal competition, limited range of mutation). <https://doi.org/10.48550/arXiv.1810.13188> Published version: J. Math. Biol. 79, 1699-1747 (2019), <https://doi.org/10.1007/s00285-019-01408-6>.
