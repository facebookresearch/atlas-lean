# Law of large numbers for multistage Michaelis–Menten kinetics

**Model.** A substrate $S$ binds an enzyme $E$ and is converted to a product $P$ through a cascade of $r$ intermediate complexes,

$$S+E \rightleftharpoons C_1 \rightleftharpoons C_2 \rightleftharpoons\cdots\rightleftharpoons C_r \to E + P,$$

with forward rates $\kappa_i$, backward rates $\kappa_{-i}$ and catalytic rate $\kappa_P$. The copy numbers form a continuous-time Markov chain (written as jump SDEs driven by Poisson random measures) with mass-action propensities; the total enzyme $M = X_E+\sum_iX_{C,i}$ is conserved and of order one. Under a multiscale scaling with parameter $n$, substrate and product are abundant (rescaled as $Z_S^{(n)}, Z_P^{(n)}$) while enzyme and complexes are rare and fast; $\Gamma_n$ denotes the occupation measure of the fast enzyme states.

**Theorem.** If $Z_V^{(n)}(0) = (Z_S^{(n)}(0), Z_P^{(n)}(0)) \to Z_V(0)\in\mathbb{R}^2_{>0}$ deterministically, then $(\Gamma_n, Z_V^{(n)})$ converges in probability to $(\pi_{Z_S}\otimes\mathrm{Leb},\, Z_V)$, where $\pi_{z}$ is the stationary distribution of the fast enzyme subsystem when the substrate level is frozen at $z$, and $Z_V=(Z_S,Z_P)$ solves

$$\dot Z_S = -h(Z_S), \qquad \dot Z_P = h(Z_S), \qquad h(y) = \frac{M\,c_3\,y}{c_1y + c_2},$$

for positive constants $c_1, c_2, c_3$ determined by the rate constants of the cascade (for $r=1$ this is the classical Michaelis–Menten rate $M\kappa_P y/(y + (\kappa_{-1}+\kappa_P)/\kappa_1)$).

## Expansion

Because the enzyme states are few and switch fast, between substrate changes they equilibrate to a stationary law $\pi_{Z_S}$ that depends on the current substrate level; the slow propensities averaged against $\pi_{Z_S}$ give the effective rate $h$, whose form follows from solving the linear recursions for the stationary complex probabilities $p_i(y)$. Tightness of the occupation measures and of the slow components, followed by identification of the limit through its martingale problem, yields the averaged ODE. The limit identifies only the effective constants $c_1,c_2,c_3$, which is the starting point for inference of reaction rates from substrate and product trajectories.

## Sources

- A. Ganguly, W. R. KhudaBukhsh, "Statistical inference for a multiscale stochastic model of enzyme kinetics via propagation of chaos", *Stochastic Processes and their Applications* 203 (2027), 105122, Section 2 (stochastic model) and the functional law of large numbers in Section 3, <https://doi.org/10.1016/j.spa.2026.105122> (preprint arXiv:2409.06565).
