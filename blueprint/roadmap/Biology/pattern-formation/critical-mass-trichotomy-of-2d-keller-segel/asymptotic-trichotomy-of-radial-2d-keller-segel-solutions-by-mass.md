# Asymptotic trichotomy of radial 2D Keller–Segel solutions by mass

**Model.** The parabolic–elliptic Keller–Segel system on $\mathbb{R}^2$,

$$\partial_tu=\Delta u-\nabla\cdot(u\nabla\Phi_u),\qquad -\Delta\Phi_u=u,$$

conserves the mass $M=\int u_0$. Its stationary states are, up to scaling and translation, $U(x)=8/(1+|x|^2)^2$, of mass exactly $8\pi$; for each $0<M<8\pi$ there is a unique self-similar expander $u=(1+t)^{-1}\Psi_M\big(x/\sqrt{1+t}\big)$ of mass $M$.

**Theorem.** Let $u$ be a radially symmetric solution with $u_0\in L^1(\langle x\rangle^2dx)$, maximal existence time $T$ and second moment $\mu=\int|x|^2u_0$.
1. *(Subcritical, $M<8\pi$.)* $T=\infty$ and $u=(1+t)^{-1}\Psi_M\big(x/\sqrt{1+t}\big)+\tilde u$ with

$$\|\tilde u(t)\|_{L^1}+(1+t)\|\tilde u(t)\|_{L^\infty}\le C(1+t)^{-\alpha}$$

for a universal $\alpha>0$. (Without radial symmetry, for any finite nonnegative measure of mass $M<8\pi$, the same convergence holds without a rate.)
2. *(Critical, $M=8\pi$.)* $T=\infty$, the second moment is conserved, and $u$ concentrates in infinite time as a rescaled stationary state, $u=\lambda^{-2}U(x/\lambda)+\tilde u$, at the universal logarithmic rate

$$\lambda(t)=\sqrt{\frac{\mu}{8\pi}}\;\frac{1+o(1)}{\sqrt{\ln t}},\qquad \|\tilde u(t)\|_{L^1}+\lambda^2(t)\|\tilde u(t)\|_{L^\infty}\le \frac{C}{(1+t)^{1-\epsilon}} .$$

3. *(Supercritical, $M>8\pi$.)* $T<\infty$ and the solution undergoes type II blow-up, $u=\lambda^{-2}U(x/\lambda)+\tilde u$, with

$$\lambda(t)=2e^{-1-\gamma/2}\sqrt{T-t}\,\exp\!\Big(-\sqrt{\tfrac{|\log(T-t)|}{2}}\Big)(1+o(1)),$$

$\gamma$ the Euler–Mascheroni constant, $\lambda^2\|\tilde u(t)\|_{L^\infty}\to0$, and $\sup_{[0,T)}\|\tilde u(t)\|_{L^1(|x|<R)}\to0$ as $R\to0$.

## Expansion

The virial identity $\frac{d}{dt}\int|x|^2u=4M\big(1-\tfrac{M}{8\pi}\big)$ sets the trichotomy: the second moment grows linearly below $8\pi$ (diffusion wins), is constant at $8\pi$, and decreases linearly above $8\pi$, forcing finite-time collapse. For radial data the partial mass $W(\xi,t)=\xi^{-2}\,\frac1{2\pi}\int_{|x|<\xi}u$ turns the nonlocal system into the local equation $W_t=W_{\xi\xi}+\tfrac3\xi W_\xi+W(\xi W_\xi+2W)$, the tool behind the supercritical blow-up rate. At the critical mass the bubble $U$ has infinite second moment ($\int|x|^2U=\infty$), so a finite conserved $\mu$ can only be matched by a slowly shrinking core with a logarithmically spreading tail; matching the two is the heuristic behind the $1/\sqrt{\ln t}$ law, proved without radial symmetry in a companion paper.

## Sources

- Federico Buseghin and Charles Collot, "Classification of the dynamics of radial solutions to the 2D parabolic-elliptic Keller-Segel System", arXiv:2606.20870 (2026), Theorem 1.1 (asymptotic trichotomy), Theorems 1.3, 1.5 and 1.7, and the partial-mass formulation remark, <https://doi.org/10.48550/arXiv.2606.20870>.
