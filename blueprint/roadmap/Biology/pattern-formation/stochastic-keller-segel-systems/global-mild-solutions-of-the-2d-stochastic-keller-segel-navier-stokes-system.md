# Global mild solutions of the 2D stochastic Keller-Segel-Navier-Stokes system with subcritical mass

**Model.** Chemotactic cells of density $n$, attracted by a chemical $c$ they produce and transported by a fluid with velocity $\mathbf{u}$, in a randomly forced fluid on $\mathbb{R}^2$:

$$\begin{aligned}
&dn = \big(\Delta n - \nabla\cdot(n\nabla c) - \mathbf{u}\cdot\nabla n\big)\,dt, \qquad 0 = \Delta c + n,\\
&d\mathbf{u} + \big((\mathbf{u}\cdot\nabla)\mathbf{u} + \nabla P\big)\,dt = \big(\Delta\mathbf{u} + n\nabla c\big)\,dt + \mathbf{f}(\mathbf{u})\,dW_t, \qquad \nabla\cdot\mathbf{u} = 0,
\end{aligned}$$

where $W$ is a Wiener process with values in a separable Hilbert space and the force $n\nabla c$ couples cells back to the fluid. The noise coefficient $\mathbf{f} = (\mathbf{f}_j)_j$ satisfies linear growth (H1) and Lipschitz (H2) bounds in the fractional Stokes-power norms $\|A^\beta\cdot\|_{L^p}$.

**Theorem.** Let $n_0 \in L^1 \cap W^{2,\hat p}\cap C^2(\mathbb{R}^2)$ with $n_0 > 0$ and $n_0\ln(1+|x|) \in L^1$, and $\mathbf{u}_0 \in W^{2,\hat p}$ divergence-free, for every $\hat p > 1$. If the initial mass is subcritical,
$$M = \int_{\mathbb{R}^2}n_0\,dx < 8\pi,$$
then there is a unique global-in-time mild solution with $n \in L^2(\Omega; C^1([0,\infty); C^2(\mathbb{R}^2)))$ and $\mathbf{u} \in L^2(\Omega; L^\infty(0,\infty; W^{2,2+\epsilon}(\mathbb{R}^2)))$ for small $\epsilon > 0$, and $n > 0$. It is a stochastic free-energy solution: for every $k \ge 1$ and $T > 0$,
$$\mathbb{E}\Big[\sup_{t\le T}|\mathcal{J}[n,\mathbf{u}]\,(t)|^k\Big] + \Big[\int_0^T\!\!\int_{\mathbb{R}^2}\Big(2n|\nabla(\ln n - c)|^2 + \tfrac12|\nabla\mathbf{u}|^2\Big)dx\,ds\Big]^k \le C_{k,T},$$
where $\mathcal{J}[n,\mathbf{u}] = \int_{\mathbb{R}^2}\big(n\ln n - \frac12nc + \frac12|\mathbf{u}|^2\big)\,dx$ is the free energy (entropy, potential energy and kinetic energy).

## Expansion

Local existence and pathwise uniqueness up to a positive stopping time follow from a fixed point for the mild formulation in $L^p\times L^{pq/(p-q)}$ spaces with $p = 2-\epsilon$, together with positivity of $n$. Globality uses the deterministic mechanism for the 2D Keller-Segel system: the logarithmic Hardy-Littlewood-Sobolev inequality makes the free energy bounded below exactly when $M < 8\pi$, which controls $\int n\ln n$; the transport by a divergence-free $\mathbf{u}$ does not change the cell entropy balance, and the coupling term $n\nabla c$ in the fluid is absorbed using Itô's formula for $\frac12\|\mathbf{u}\|^2_{L^2}$ and the growth bound on the noise. On the whole plane the classical free energy alone does not give almost-sure bounds (the entropy can be negative at large $|x|$), which is why the logarithmic moment $n_0\ln(1+|x|) \in L^1$ is assumed; uniform moment bounds on stopping-time-localized solutions then rule out explosion.

## Sources

- Fanze Kong, Chen-Chih Lai and Krutika Tawri, "Global Well-posedness of the 2D Stochastic Self-consistent Keller-Segel-Navier-Stokes System with Subcritical Mass", arXiv:2605.17114 (2026), Section 1, Theorem 1, Section 3, Theorems 2-4, and Section 4, Proposition 1, <https://doi.org/10.48550/arXiv.2605.17114>.
