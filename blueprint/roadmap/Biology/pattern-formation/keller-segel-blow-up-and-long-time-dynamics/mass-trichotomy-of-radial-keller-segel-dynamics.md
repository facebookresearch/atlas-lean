# Mass trichotomy of radial Keller–Segel dynamics

For the planar parabolic–elliptic Keller–Segel equation $\partial_t u=\Delta u-\nabla\cdot(u\nabla\Phi_u)$, $-\Delta\Phi_u=u$ on $\mathbb R^2$, let $u$ be a radially symmetric solution with $u_0\in L^1((1+|x|^2)dx)$, mass $M=\int u_0$ and maximal existence time $T$. Let $U(x)=8/(1+|x|^2)^2$ and $\mu=\int|x|^2u_0\,dx$.

**Theorem (complete radial classification).**

1. *Subcritical, $M<8\pi$.* The solution is global and converges to the unique radial self-similar expander $\Psi_M$ of mass $M$: $u(t,x)=\frac{1}{t+1}\Psi_M\big(\frac{x}{\sqrt{t+1}}\big)+\tilde u$ with $(1+t)^{\alpha}\big(\|\tilde u\|_{L^1}+t\|\tilde u\|_{L^\infty}\big)\to0$ for some $\alpha>0$.
2. *Critical, $M=8\pi$.* The solution is global and $u=\lambda^{-2}U((x-x(t))/\lambda)+\tilde u$ with $\lambda(t)=\sqrt{\mu/(8\pi)}\,(1+o(1))/\sqrt{\ln t}$ and $(1+t)^{1-\epsilon}\big(\|\tilde u\|_{L^1}+\lambda^2\|\tilde u\|_{L^\infty}\big)\to0$ for every $\epsilon>0$ (infinite-time concentration).
3. *Supercritical, $M>8\pi$.* The solution blows up in finite time $T<\infty$ by concentrating one bubble at the origin, $u=\lambda^{-2}U(x/\lambda)+\tilde u$, at the universal type II rate

$$\lambda(t)=2e^{-1-\gamma/2}\sqrt{T-t}\,\exp\!\Big(-\sqrt{\tfrac{|\log(T-t)|}{2}}\Big)(1+o(1)),$$

where $\gamma$ is the Euler–Mascheroni constant, with $\lim_{R\to0}\sup_{[0,T)}\|\tilde u\|_{L^1(|x|<R)}=0$ and $\lambda^2\|\tilde u\|_{L^\infty}\to0$.

## Depends on

- [Universal large-time asymptotics of the critical-mass Keller–Segel equation](universal-large-time-asymptotics-of-critical-mass-keller-segel.md)

## Expansion

The threshold $8\pi$ separates regimes because the virial identity $\frac{d}{dt}\int|x|^2u=4M(1-M/8\pi)$ is positive below, zero at, and negative above it. Below threshold diffusion wins and the solution relaxes to a self-similar expander; above it the second moment would become negative in finite time, forcing collapse, and the radial blow-up is known to be stable and of type II with a $\sqrt{T-t}$ law corrected by an $\exp(-\sqrt{|\log(T-t)|/2})$ factor. The critical case, settled by the universal critical-mass asymptotics, completes the picture: for radial finite-second-moment data every solution follows exactly one of three universal behaviors, determined by the mass alone. Without radial symmetry the sub- and critical statements survive, but supercritical solutions may form several collapsing spikes that collide.

## Sources

- F. Buseghin, C. Collot, *Determination of the long-time dynamics for the 2D Keller-Segel equation at critical mass* (2026), Theorem 1.3 (classification of radial dynamics) and Remark 1.4. <https://doi.org/10.48550/arXiv.2606.20866>
