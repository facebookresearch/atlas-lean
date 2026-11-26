# Exact first-passage time of a bimolecular reaction via Poisson-product representation

Consider a stochastic reaction network on species $S_1,\dots,S_N$ with $M$ reactions of order at most one, $y_m \cdot S \xrightarrow{a_m(t)} y'_m \cdot S$ with $\|y_m\|_1, \|y'_m\|_1 \le 1$ and possibly time-dependent rate constants, plus one bimolecular reaction $S_1 + S_2 \xrightarrow{a_0(t)} S_0$, where the counter species $S_0$ records how many times it has fired. Let $X = (x_0, x)$ be the copy-number vector and $P(X,t)$ the solution of the chemical master equation (CME) with mass-action propensities ($c_0 = a_0 x_1 x_2$, the others linear in $x$). The *first-passage time* (FPT) of the bimolecular reaction is its first firing time, so $P(\mathrm{FPT} > t) = P(x_0(t) = 0)$.

Let $\lambda(t) \in \mathbb{C}^N$, $\lambda_S(t), \lambda_0(t) \in \mathbb{C}$ solve the linear stochastic differential equations driven by independent Brownian motions $W^1, W^2$:

$$d\lambda = (\mathcal{M}_1 \lambda + \mathcal{M}_2)\,dt + \mathcal{N}_1 \lambda\, dW^1_t + \mathcal{N}_2 \lambda\, dW^2_t,$$
$$d\lambda_S = a_S(\lambda_1 - \lambda_2)\, dW^1_t + \mathrm{i}\, a_S (\lambda_1 + \lambda_2)\, dW^2_t, \qquad d\lambda_0 = a_0 \lambda_1 \lambda_2\, dt,$$

with $\lambda_S(0) = \lambda_0(0) = 0$, where $a_S = \sqrt{2a_0}/2$, $(\mathcal{M}_1)_{ij} = \sum_{m : y_m = e_i} a_m (y'_{m,j} - y_{m,j})$ and $(\mathcal{M}_2)_i = \sum_{m : y_m = 0} a_m (y'_{m,i} - y_{m,i})$ encode the first- and zero-order reactions (mean-field linear dynamics), and $\mathcal{N}_1 = \operatorname{diag}(a_S, -a_S, 0,\dots)$, $\mathcal{N}_2 = \operatorname{diag}(\mathrm{i} a_S, \mathrm{i} a_S, 0, \dots)$ act only on the two reactants.

**Theorem.** If the initial distribution is Poisson-product, $P(X,0) = \prod_{i=0}^N \lambda_i(0)^{x_i} e^{-\lambda_i(0)}/x_i!$, then for all $t \ge 0$

$$P(X,t) = \Big\langle \frac{\Lambda(t)^{X}}{X!}\, e^{-\Lambda(t)}\, e^{\lambda_0(t) + \lambda_S(t)} \Big\rangle, \qquad \Lambda = (\lambda_0, \lambda),$$

with $\langle \cdot \rangle$ the expectation over the Brownian paths (the Poisson weights are understood componentwise). Consequently the FPT survival function is

$$P(\mathrm{FPT} > t) = \sum_{x : x_0 = 0} P(X,t) = \big\langle e^{\lambda_S(t)} \big\rangle.$$

## Expansion

For networks of order at most one, Poisson-product distributions are preserved by the CME with deterministic means (Jahnke-Huisinga). A bimolecular reaction breaks this, but the factorization $x_1 x_2$ can be produced by complex noise: Ito's formula applied to a Poisson-product ansatz with stochastic parameters reproduces the bimolecular term because the noise $\mathcal{N}_1 \lambda\, dW^1 + \mathcal{N}_2 \lambda\, dW^2$ has zero quadratic variation in each reactant coordinate and cross-variation $d\langle \lambda_1, \lambda_2 \rangle = -2a_S^2 \lambda_1 \lambda_2\,dt = -a_0 \lambda_1\lambda_2\,dt$. The martingale terms vanish in expectation (localization by stopping times plus moment bounds for linear SDEs), giving the exact CME solution. Summing over $x_0 = 0$ kills every factor except $e^{\lambda_S}$. Because $\lambda$ and $\lambda_S$ satisfy linear SDEs, all moments $\langle \lambda_S^n \rangle$ obey finite closed ODE systems, which makes Pade approximation of $s \mapsto \langle e^{s\lambda_S(t)} \rangle$ at $s = 1$ a practical way to evaluate the FPT distribution.

## Sources

- Changqian Rao, David Waxman, Wei Lin, Zhuoyi Song, "Exact first passage time distribution for second-order reactions in chemical networks", arXiv:2409.02698 (2024), Theorem 1, Corollary 1 and Proposition 1, <https://doi.org/10.48550/arXiv.2409.02698>
