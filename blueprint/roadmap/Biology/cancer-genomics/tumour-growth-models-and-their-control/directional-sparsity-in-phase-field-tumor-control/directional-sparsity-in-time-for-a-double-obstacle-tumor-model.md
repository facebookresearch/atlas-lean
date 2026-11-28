# Directional sparsity in time of optimal therapies for a double-obstacle phase-field tumor model

Let $\Omega \subset \mathbb{R}^3$ be a bounded smooth domain, $T > 0$, $Q = \Omega \times (0,T)$, and let $\alpha, \beta, \chi > 0$. The state $(\mu, \varphi, \xi, \sigma)$ (chemical potential, tumor fraction, selection of the subdifferential, nutrient) solves, with homogeneous Neumann boundary conditions and given initial data,

$$ \alpha \partial_t \mu + \partial_t \varphi - \Delta \mu = P(\varphi)(\sigma + \chi(1-\varphi) - \mu) - h(\varphi) u_1, \qquad \beta \partial_t \varphi - \Delta \varphi + \xi + F_2'(\varphi) = \mu + \chi \sigma, \quad \xi \in \partial I_{[-1,1]}(\varphi), $$

$$ \partial_t \sigma - \Delta \sigma = -\chi \Delta \varphi - P(\varphi)(\sigma + \chi(1-\varphi) - \mu) + u_2, $$

where $I_{[-1,1]}$ is the indicator function of $[-1,1]$ (so $I_{[-1,1]} + F_2$ is a double-obstacle potential), $P$ is a proliferation function, $h$ is a truncation function localizing the cytotoxic drug $u_1$ to the tumor region, and $u_2$ is a nutrient or medication supply. The controls range over the box set $\mathcal{U}_{ad} = \{ (u_1,u_2) \in L^\infty(Q)^2 : \underline u_i \le u_i \le \hat u_i \}$. Minimize

$$ \mathcal{J} = \frac{b_1}{2} \iint_Q |\varphi - \widehat\varphi_Q|^2 + \frac{b_2}{2} \int_\Omega |\varphi(T) - \widehat\varphi_\Omega|^2 + \frac{b_0}{2} \iint_Q |\mathbf{u}|^2 + \kappa\, g(\mathbf{u}), \qquad g(\mathbf u) = \sum_{i=1}^{2} \int_0^T \| u_i(\cdot,t) \|_{L^2(\Omega)} \, dt, $$

with $b_1, b_2 \ge 0$, $b_0 > 0$, and sparsity weight $\kappa > 0$.

**Theorem (directional sparsity in time).** Assume the standing hypotheses on $P$, $h$, $F_2$ and the data, and $\underline u_i < 0 < \hat u_i$ for $i = 1,2$. Let $\bar{\mathbf u} = (\bar u_1, \bar u_2)$ be an optimal control with state $(\bar\mu, \bar\varphi, \bar\xi, \bar\sigma)$, and let $(p, q, r)$ be the adjoint state obtained through the deep quench limit. Then for almost every $t \in (0,T)$:

$$ \| \bar u_1(\cdot,t) \|_{L^2(\Omega)} = 0 \iff \| h(\bar\varphi(\cdot,t))\, p(\cdot,t) \|_{L^2(\Omega)} \le \kappa, \qquad \| \bar u_2(\cdot,t) \|_{L^2(\Omega)} = 0 \iff \| r(\cdot,t) \|_{L^2(\Omega)} \le \kappa. $$

So at any time where the relevant adjoint quantity is at most $\kappa$ in $L^2(\Omega)$, the optimal therapy is switched off on the whole domain.

The key auxiliary fact is scalar: if $C = \{ v \in L^\infty(Q) : \underline w \le v \le \hat w \}$ with $\underline w < 0 < \hat w$, $d \in L^2(Q)$, and $u \in C$ satisfies $\iint_Q (d + \kappa \lambda + b_0 u)(v - u) \ge 0$ for all $v \in C$ with some $\lambda \in \partial g_T(u)$, $g_T(u) = \int_0^T \|u(\cdot,t)\|_{L^2(\Omega)} dt$, then $\|u(\cdot,t)\|_{L^2(\Omega)} = 0 \iff \|d(\cdot,t)\|_{L^2(\Omega)} \le \kappa$ for almost every $t$, and $\lambda(\cdot,t) = u(\cdot,t) / \|u(\cdot,t)\|_{L^2(\Omega)}$ whenever $u(\cdot,t) \neq 0$, while $\|\lambda(\cdot,t)\|_{L^2(\Omega)} \le 1$ otherwise.

## Expansion

The double-obstacle potential is not differentiable, so standard constraint qualifications for Lagrange multipliers fail. The proof first replaces $I_{[-1,1]}$ by the logarithmic potential $\gamma F_{1,\log}$, $F_{1,\log}(r) = (1+r)\ln(1+r) + (1-r)\ln(1-r)$, for which first-order conditions are known, and shows that optimal controls of the approximating problems converge as $\gamma \searrow 0$ (deep quench approximation); the adjoint states converge weakly and yield a variational inequality for $\bar{\mathbf u}$ of the form above with $d = -h(\bar\varphi) p$ for $u_1$ and $d = r$ for $u_2$. Because $g$ splits into the two components, the subdifferential splits and the scalar sparsity lemma applies to each control separately. The lemma itself follows by testing the variational inequality with controls that differ from $u$ only on a time slab and using the explicit subdifferential of the $L^1(0,T;L^2(\Omega))$ norm.

## Sources

- Pierluigi Colli, Andrea Signori, Jürgen Sprekels, "Optimal Control Problems with Sparsity for Tumor Growth Models Involving Variational Inequalities", Journal of Optimization Theory and Applications 194 (2022), 25–58, <https://doi.org/10.1007/s10957-022-02000-7>. Published version of arXiv:2104.09814, cited next; locators there refer to the arXiv version.
- Pierluigi Colli, Andrea Signori, Jürgen Sprekels, "Optimal control problems with sparsity for phase field tumor growth models involving variational inequalities", arXiv (2021). Theorem 2.2 (well-posedness), Theorem 5.1 (first-order conditions), Lemma 6.1, Theorem 6.2. <https://doi.org/10.48550/arXiv.2104.09814>
