# Quasi-steady-state manifolds as sliding modes of the tropicalized dynamics

Consider a biochemical network with rational rate functions, $\dot x_i=P_i(x)/Q_i(x)$, where $P_i=\sum_{\alpha\in A_i}a_{i,\alpha}x^\alpha$ and $Q_i=\sum_{\beta\in B_i}b_{i,\beta}x^\beta$, on $x\in\mathbb R^n_+$. With $u=\log x$, the **tropicalization** replaces each sum by its dominant monomial:

$$
\dot x_i=s_i\exp\Big[\max_{\alpha\in A_i}\{\log|a_{i,\alpha}|+\langle u,\alpha\rangle\}-\max_{\beta\in B_i}\{\log|b_{i,\beta}|+\langle u,\beta\rangle\}\Big],
$$

where $s_i$ is the product of the signs of the maximizing coefficients. This piecewise-smooth system switches whenever the dominant monomial changes. The tropical variety of a polynomial $P$ is the non-smoothness locus of its max-plus tropicalization $P^\tau(x)=\max_\alpha\{\log|a_\alpha|+\langle\alpha,\log x\rangle\}$; it is dual to the Newton polytope $\mathrm{conv}(A)$. A monomial $M_1$ dominates $M_2$ at level $\rho>0$ on a domain $D$ if $\log|M_1|>\log|M_2|+\rho$ throughout $D$. A species is slaved if its trace stays within $\delta$, in log scale, of an imposed trace.

**Theorem.** Suppose the smooth dynamics satisfies quasi-equilibrium (QE) or quasi-steady-state (QSS) conditions, and the pruned polynomial $\tilde P$ governing the fast dynamics, after removing dominated monomials, is a binomial. Then the QE/QSS equation defines a hyperplane of the tropical variety of $\tilde P$. If the QE/QSS manifold is stable, the tropicalized dynamics has a sliding mode along this hyperplane. The converse can fail: a smooth trajectory may leave the hyperplane before the sliding mode ends.

Dominance and separation of monomials therefore give a systematic way to reduce large networks to hybrid piecewise-smooth models. The paper applies this to a cell-cycle model.

## Proof sketch

For a binomial $\tilde P=M_1-M_2$, the QE/QSS condition $M_1=M_2$ is a hyperplane in log coordinates, namely where the two monomials tie, which is exactly the tropical variety. On each side one monomial dominates, so the tropicalized vector field points in the direction set by that monomial. Stability of the smooth slow manifold means the fields on both sides point toward it. The normal components then have opposite signs, which is Filippov's condition for a sliding mode.

## Sources

- Vincent Noel, Dima Grigoriev, Sergei Vakulenko and Ovidiu Radulescu, "Tropical Geometries and Dynamics of Biochemical Networks Application to Hybrid Cell Cycle Models", *Electronic Notes in Theoretical Computer Science* 284 (2012), 75–91, <https://doi.org/10.1016/j.entcs.2012.05.016>. Preprint version: arXiv:1109.4085 (2011), Sections 2–6 (Definitions 1–7, Theorem 1), <https://doi.org/10.48550/arXiv.1109.4085>.
