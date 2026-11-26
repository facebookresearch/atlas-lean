# Global solutions of the degenerate Keller–Segel system for small Lorentz data

**Setting.** On $(0,\infty) \times \mathbb{R}^3$ consider the chemotaxis system for a cell density $u$ and a chemoattractant $\varphi$ produced by the cells,

$$\partial_t u = \Delta u - \operatorname{div}(u \nabla\varphi), \qquad \partial_t\varphi = \epsilon\Delta\varphi + u, \qquad u(0,\cdot) = u_0, \quad \varphi(0,\cdot) = 0,$$

with $\epsilon \ge 0$. For $\epsilon > 0$ this is the parabolic–parabolic Keller–Segel system; $\epsilon = 0$ is its degenerate limit, in which the signal does not diffuse and $\varphi(t) = \int_0^t u(s)\,ds$. By Duhamel's formula, mild solutions are fixed points of

$$u = e^{t\Delta}u_0 - B_\epsilon(u,u), \qquad B_\epsilon(u,v) = \int_0^t e^{(t-s)\Delta} \operatorname{div}\Big(u \int_0^s e^{\epsilon(s-\sigma)\Delta}\nabla v \, d\sigma\Big) ds.$$

The system is invariant under $u_\lambda(t,x) = \lambda^2 u(\lambda^2 t, \lambda x)$, and $L^{3/2}$, $L^{3/2,q}$ and $\dot B^{-1/2}_{2,\infty}$ are critical spaces for this scaling.

**Theorem.** There is a constant $C_0 > 0$, independent of $\epsilon$, such that for every $\epsilon \ge 0$ and every $u_0$ in the Lorentz space $L^{3/2,1}(\mathbb{R}^3)$ with $\|u_0\|_{L^{3/2,1}} < C_0$, the equation has a global mild solution

$$u \in L^\infty\big((0,\infty); L^{3/2,\infty}\big) \cap L^1\big((0,\infty); \dot B^{3/2}_{2,1}\big).$$

By contrast, the classical small-data results for $\epsilon > 0$ (in $L^{3/2}$, $L^{3/2,\infty}$ or $\dot B^{-1/2}_{2,\infty}$) require $\|u_0\| < C_\alpha\sqrt{\epsilon}$, which degenerates as $\epsilon \to 0$.

## Expansion

The key estimate is the bilinear bound

$$\|B_\epsilon(u,v)\|_{L^1((0,\infty); \dot B^{3/2}_{2,1})} \le C\, \|u\|_{L^1((0,\infty); \dot B^{3/2}_{2,1})}\, \|v\|_{L^1((0,\infty); \dot B^{3/2}_{2,1})}$$

with $C$ independent of $\epsilon \ge 0$, proved with $L^1$-in-time maximal regularity estimates for the heat kernel in homogeneous Besov spaces $\dot B^0_{q,1}$ (Lemma 1). On the linear side, the dyadic bound $\|\Delta_j e^{t\Delta}u_0\|_2 \le C\min(1, t^{-2}2^{-4j})\|\Delta_j u_0\|_2$ shows that $e^{t\Delta}$ maps $\dot B^{-1/2}_{2,1}$ into $\mathbb{Y} = L^1((0,\infty); \dot B^{3/2}_{2,1})$, and data in $L^{3/2,1}$ have $e^{t\Delta}u_0 \in \mathbb{Y} \cap L^\infty((0,\infty); L^{3/2,\infty})$. With a bilinear constant uniform in $\epsilon$, the Picard iterates $w_{n+1} = e^{t\Delta}u_0 - B_\epsilon(w_n, w_n)$ converge for small data, uniformly in $\epsilon$; this is what removes the $\sqrt\epsilon$ smallness condition of the classical results.

## Sources

- P. G. Lemarié-Rieusset, "A short note on maximal regularity for the heat kernel in Besov spaces and a degenerate 3D Keller–Segel system", arXiv:2607.01847 (2026), Section 1 (system and mild formulation), Proposition 1, Lemma 1 (maximal regularity), Proposition 2 and Theorem 1, <https://doi.org/10.48550/arXiv.2607.01847>.
