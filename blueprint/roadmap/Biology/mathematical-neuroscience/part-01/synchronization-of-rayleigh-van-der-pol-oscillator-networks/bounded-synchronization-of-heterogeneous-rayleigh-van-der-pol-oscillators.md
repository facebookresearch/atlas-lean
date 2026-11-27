# Bounded synchronization of heterogeneous Rayleigh–van der Pol oscillators

**Model.** Node $i \in \{1,\dots,N\}$ of a simple undirected connected graph with adjacency $(a_{ij})$ and degree $N_i$ has state $x_i = (x_{i1}, x_{i2}) \in \mathbb{R}^2$ (position, velocity) and parameters $\vartheta_i = (\alpha_i,\beta_i,\gamma_i,\omega_i)$:

$$\dot x_{i1} = x_{i2}, \qquad \dot x_{i2} = -\bigl(\alpha_i x_{i1}^2 + \beta_i x_{i2}^2 - \gamma_i\bigr)x_{i2} - \omega_i^2 x_{i1} + u_{i},$$

the hybrid Rayleigh–van der Pol (HKB) oscillator. Under **full-state diffusive coupling** the whole state is driven,

$$\dot x_i = f_i(x_i) - \frac{c}{N_i}\sum_{j=1}^N a_{ij}\,(x_i - x_j), \qquad c > 0,$$

with $f_i$ the uncoupled vector field. Let $\bar x = \frac1N\sum_j x_j$, $e_i = x_i - \bar x$ and $\eta(t) = \|(e_1,\dots,e_N)\|_2$. The network achieves **bounded synchronization** if for every initial condition there are $\epsilon > 0$ and $\hat t$, both depending on it, with $\eta(t) \le \epsilon$ for all $t > \hat t$; the theorems below give $\epsilon$ explicitly.

**Theorem (Lyapunov, QUAD-affine form).** Assume $\gamma_i = \tilde\gamma > 0$ for all $i$ (the oscillatory regime), and let $L_N$ be the degree-normalized Laplacian ($l_{ii} = 1$, $l_{ij} = -a_{ij}/N_i$ for neighbours) with algebraic connectivity $\lambda_2(L_N) > 0$. For $P = \mathrm{diag}(P_{11},P_{22}) \succ 0$ and $W_{11} > 0$ set

$$d_\epsilon = c\,\lambda_2(L_N)\min\{P_{11},P_{22}\} - \max\{W_{11},\,\tilde\gamma P_{22}\}.$$

If

$$c > \bar c = \min_{W_{11},P_{11},P_{22}>0}\ \frac{\max\{W_{11},\,\tilde\gamma P_{22}\}}{\lambda_2(L_N)\,\min\{P_{11},P_{22}\}} = \frac{\tilde\gamma}{\lambda_2(L_N)},$$

then the network achieves bounded synchronization: along every trajectory, for every diagonal $P \succ 0$ and $W_{11} > 0$ with $d_\epsilon > 0$, $\limsup_{t\to\infty}\eta(t) \le \sqrt N\,\bar M \max\{P_{11},P_{22}\}/d_\epsilon$, so any $\epsilon$ above the minimum $\epsilon(c)$ of this bound over such choices works for that trajectory. The bound depends on the trajectory through $\bar M$, and is not uniform over initial conditions. Here $\bar M = (1+\alpha_M p_M^2+\beta_M v_M^2)v_M + \omega_M^2 p_M$ bounds the heterogeneous part of the dynamics along the network trajectory, in terms of the maximal parameter magnitudes $\alpha_M,\beta_M,\omega_M$ and $p_M = \max_i \sup_{t \ge 0}|x_{i1}(t)|$, $v_M = \max_i \sup_{t \ge 0}|x_{i2}(t)|$, the suprema taken along the network trajectory (finite since the trajectories are bounded). The bound decreases as $c$ grows.

**Theorem (contraction, all-to-all).** On the unweighted complete graph ($a_{ij} = 1$ for $i \ne j$), assuming $\tilde\alpha, \tilde\beta > 0$, if the virtual system's trajectories satisfy $|z_1| \le z_1^{\max}$, $|z_2| \le z_2^{\max}$ and, with $\tilde\alpha,\tilde\beta,\tilde\omega,\tilde\gamma$ the parameter averages,

$$\frac{N-1}{N}\bigl(2\tilde\alpha z_1^{\max}z_2^{\max} + \tilde\omega^2 + \tilde\gamma\bigr) < c < \frac{N-1}{N},$$

then bounded synchronization is achieved.

## Expansion

Lyapunov route: split $f_i = h + g_i$ with common part $h(z) = (0, \tilde\gamma z_2)$ and bounded heterogeneous part $g_i(x_i) = \bigl(x_{i2},\ -(\alpha_i x_{i1}^2 + \beta_i x_{i2}^2)x_{i2} - \omega_i^2 x_{i1}\bigr)$. The common part satisfies the QUAD inequality $(z-w)^\top P(h(z)-h(w)) \le (z-w)^\top W (z-w)$ with $W = \mathrm{diag}(W_{11}, \tilde\gamma P_{22})$ for any $W_{11} > 0$, and $\|g_i\|_2 \le \bar M$ along the network trajectory, whose boundedness the source takes from Zhai et al. (2015). The general bounded-synchronization theorem for QUAD-affine networks with positive diagonal coupling matrix (here the identity) then yields the threshold and an error bound inversely proportional to the excess $d_\epsilon$ of coupling over the QUAD constant. A Rayleigh–van der Pol field cannot be QUAD with negative definite $W$, so the common part must carry the destabilizing $\tilde\gamma$ term and be dominated by coupling.

Contraction route: build a virtual system whose particular solutions are the node trajectories, with averaged parameters, and verify that its Jacobian has a negative matrix measure using sign and magnitude conditions on the Jacobian entries; contraction of the virtual system yields complete synchronization for identical nodes and bounded synchronization under parameter mismatch. Numerically, all three couplings (full-state, partial-state and HKB) reproduce the mean group-synchronization level of the rocking-chair experiments; only partial-state and HKB coupling preserve its steady-state fluctuations, HKB matching the data most closely (Sect. 5.1).

## Sources

- F. Alderisio, B. G. Bardy, M. di Bernardo, "Entrainment and synchronization in networks of Rayleigh–van der Pol oscillators with diffusive and Haken–Kelso–Bunz couplings", Biological Cybernetics 110 (2016) 151–169, Definitions 1–6, Theorems 1–2, Corollary 1 (Equations 8, 25, 36–46), <https://doi.org/10.1007/s00422-016-0685-7>, PMCID PMC4903116.
- H. Haken, J. A. S. Kelso, H. Bunz, "A theoretical model of phase transitions in human hand movements", Biological Cybernetics 51 (1985) 347–356, <https://doi.org/10.1007/BF00336922>.
