# Universal large-time asymptotics of the critical-mass Keller–Segel equation

Consider the parabolic–elliptic Keller–Segel model of chemotactic aggregation on the plane,
$$\partial_t u=\Delta u-\nabla\cdot(u\nabla\Phi_u),\qquad -\Delta\Phi_u=u,\qquad x\in\mathbb R^2,\ t>0,$$
with $u(0)=u_0\ge 0$ and $\nabla\Phi_u=-\frac{1}{2\pi}\frac{x}{|x|^2}*u$. Let $U(x)=\frac{8}{(1+|x|^2)^2}$ be the stationary state of mass $\int U=8\pi$.

**Theorem.** Assume $\int_{\mathbb R^2}u_0(x)(1+|x|^2)\,dx<\infty$ and critical mass $\int u_0=8\pi$. Let $x^*$ be the center of mass and $\mu=\int|x-x^*|^2u_0\,dx$ the second moment. Then the solution is global, its second moment stays equal to $\mu$, and for large times
$$u(x,t)=\frac{1}{\lambda(t)^2}U\!\left(\frac{x-x(t)}{\lambda(t)}\right)+\tilde u(x,t),\qquad \lambda(t)=\sqrt{\frac{\mu}{8\pi}}\,\frac{1+o(1)}{\sqrt{\ln t}},$$
with, for every $\epsilon>0$ and some $C=C(u,\epsilon)$,
$$\|\tilde u(t)\|_{L^1}+\lambda(t)^2\|\tilde u(t)\|_{L^\infty}\le Ct^{-1+\epsilon},\qquad |x(t)-x^*|\le Ct^{-1/2+\epsilon}\quad(t\ge1).$$

So every finite-second-moment threshold solution concentrates the same bubble at the same logarithmic rate: infinite-time blow-up at critical mass is universal, and the conserved second moment alone selects the scale.

## Expansion

The total mass $8\pi$ is exactly the mass for which the free energy $\int u\log u-\frac12\int u\Phi_u$ is bounded below (sharp logarithmic Hardy–Littlewood–Sobolev inequality), its minimizers being the rescaled bubbles $U_\lambda$. The virial identity $\frac{d}{dt}\int|x-x^*|^2u=4M(1-M/8\pi)$ vanishes at $M=8\pi$, so the second moment is conserved, while a single bubble $U_\lambda$ has infinite second moment. The proof first shows soliton resolution (the solution approaches the family $U_{\lambda}(\cdot-x)$ with $\lambda\to0$), then performs a modulation analysis in parabolic self-similar variables with coercivity estimates in inner, near-outer and far-outer zones. Matching the outer self-similar tail, which must carry the conserved second moment, with the inner bubble fixes the scale $\lambda^2\ln t\to\mu/(8\pi)$. The rates are close to sharp: the far-field analysis rules out $t^{-\alpha}$ for $\alpha>1$. The finite-second-moment hypothesis matters; for data failing it logarithmically, solutions instead converge to a fixed $U_\lambda$ or may oscillate.

## Sources

- F. Buseghin, C. Collot, *Determination of the long-time dynamics for the 2D Keller-Segel equation at critical mass* (2026), Theorem 1.1 (with the soliton resolution of Section 4 and the linearized analysis in parabolic self-similar variables of Section 6). <https://doi.org/10.48550/arXiv.2606.20866>
