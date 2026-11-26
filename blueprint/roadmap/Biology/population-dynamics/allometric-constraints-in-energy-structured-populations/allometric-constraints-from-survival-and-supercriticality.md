# Allometric constraints from survival and supercriticality

In the [energy-structured individual-based model](energy-structured-individual-based-model-and-its-generation-process.md), take allometric (power-law) rates
$$\tilde b(x) = C_\beta x^\beta,\quad d(x) = C_\delta x^\delta,\quad \ell(x) = C_\alpha x^\alpha,\quad \psi(x) = C_\gamma x^\gamma,$$
with $\beta, \delta \in \mathbb R$ and $C_\beta, C_\delta, C_\alpha, C_\gamma, \alpha, \gamma > 0$. Require Assumptions 1 and 2 (biologically relevant paths for every $x_0$) and Assumption 3 (supercriticality for every $x_0$).

**Theorem (case $0 < \alpha \le 1$).** Then necessarily $\gamma = \alpha$, $\delta = \alpha - 1$, $C_\gamma > C_\alpha$, and either

- $\beta = \alpha - 1$ and $C_\beta > C_\delta$ (the classical exponents of metabolic theory, case $I_1$), or
- $\beta \ge \alpha - 1 + \dfrac{C_\delta}{C_\gamma - C_\alpha}$ and $C_\delta \le C_\gamma - C_\alpha$ (case $I_2$).

In particular, if $C_\delta > C_\gamma - C_\alpha$, only $(\gamma,\delta,\beta) = (\alpha, \alpha-1, \alpha-1)$ with $C_\beta > C_\delta$ is possible. Conversely, if $(\gamma,\delta,\beta) = (\alpha,\alpha-1,\alpha-1)$, $C_\gamma > C_\alpha$, $C_\beta > (e-1)C_\delta$ and $C_\beta + C_\delta < C_\gamma - C_\alpha$, then Assumptions 1 to 3 hold.

**Theorem (case $\alpha > 1$).** Then $\gamma = \alpha$ and $C_\gamma > C_\alpha$; $\delta \le \alpha - 1 \le \beta$; if $\beta = \delta = \alpha - 1$ then $C_\beta > C_\delta$; if $\delta = \alpha - 1 < \beta$ then $\beta \ge \alpha - 1 + C_\delta/(C_\gamma - C_\alpha)$; and if $\beta > \alpha$ then $\delta \ge \alpha - 1$, with $C_\delta \le C_\gamma - C_\alpha$ when moreover $\delta = \alpha - 1$.

The authors conjecture that for $0 < \alpha \le 1$ the case $I_2$ conditions are also sufficient and give infinite mean offspring numbers.

## Depends on

- [Energy-structured individual-based model and its generation process](energy-structured-individual-based-model-and-its-generation-process.md)

## Expansion

Supercriticality for every $x_0$ forces individuals to gain energy at large resource levels, which compares $\psi$ and $\ell$ for all body sizes and fixes $\gamma = \alpha$ with $C_\gamma > C_\alpha$. Assumption 1 near zero energy compares death with metabolism, giving $\delta \le \alpha - 1$, while survival to reproduce at all scales prevents death from being too weak relative to birth and growth; the scaling exponent $\alpha - 1$ is the natural rate of an energy flow of order $x^\alpha$ acting on a state of order $x$. The proofs use couplings of individual paths, a Galton-Watson embedding and asymptotic pseudotrajectories for the rescaled energy. The constraints follow from survival and branching alone, without imposing metabolic theory.

## Sources

- S. Billiard, V. Brodu, N. Champagnat and C. Fritsch, "An individual-based stochastic model reveals strong constraints on allometric relationships with minimal metabolic and ecological assumptions", arXiv preprint (2025), Theorems 2 and 3, Corollary 5, Proposition 6 and Conjectures 1 and 2. <https://doi.org/10.48550/arXiv.2501.12257>