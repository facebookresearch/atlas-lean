# Critical level of the canard explosion in the singular Hopf normal form

Consider the planar fast subsystem of the singular Hopf normal form with the slow variable frozen at $\lambda$,

$$u'=\delta(\alpha+F_{13}\lambda)u+v+\tfrac12u^2+\tfrac{\delta}{6}F_{111}u^3,\qquad v'=-u,$$

with $F_{13}>0$, $F_{111}<0$ and $0<\delta\ll1$. Its equilibrium at the origin has eigenvalues $\sigma_{1,2}=\tfrac12\big(\delta(\alpha+F_{13}\lambda)\pm\sqrt{\delta^2(\alpha+F_{13}\lambda)^2-4}\big)+O(\delta^2)$, so a supercritical Hopf bifurcation occurs at $\lambda_H(\alpha)=-\alpha/F_{13}+O(\delta)$. The $u$-nullcline $v=-\big(\delta(\alpha+F_{13}\lambda)+u/2+\tfrac{\delta}{6}F_{111}u^2\big)u$ is S-shaped, with fold points at $u_f^\pm=\big(-1\pm\sqrt{1-2\delta^2F_{111}(\alpha+F_{13}\lambda)}\big)/(\delta F_{111})$.

For $\alpha$ above the threshold $\alpha_c$, the Hopf limit cycle $\Gamma^\lambda_\alpha$ grows with $\lambda$ while the separatrix threshold $v^\star_\alpha(\lambda)$ between small (Type I) and large (Type II) oscillations decreases, so there is a unique level $\lambda_c(\alpha)$ at which the separatrix closes: cycles are small for $\lambda<\lambda_c(\alpha)$ and large for $\lambda>\lambda_c(\alpha)$ (a canard explosion). This splits the $(\alpha,\lambda)$ plane into three regimes: no large oscillations ($\alpha\le\alpha_c$), small cycles ($\lambda_H<\lambda\le\lambda_c$) and large cycles ($\lambda_c<\lambda\le0$).

**Proposition.** Assume $F_{13}>0$, $F_{111}<0$ and $\delta>0$ small. For $\alpha>\alpha_c$,

$$\lambda_c(\alpha)=\tilde\lambda_\delta(\alpha)+O(\delta^2),\qquad \tilde\lambda_\delta(\alpha)=\frac{1}{F_{13}}\left(\frac{2-\sqrt{4+2\delta^2F_{111}^2}}{\delta^2F_{111}}-\alpha\right).$$

## Expansion

Parametrize the separatrix by time from $(0,v^\star_\alpha(\lambda))$ and differentiate the vector field repeatedly at $\tau=0^+$. With $\mu=\alpha+F_{13}\lambda$ and $v^\star=v^\star_\alpha(\lambda)$, the fourth derivative is

$$u_*^{(iv)}(0)=\delta v^\star\big[F_{111}(v^\star)^2+4\mu v^\star+\mu(\delta^2\mu^2-2)\big].$$

Comparing the separatrix with the level set $u^{(iv)}=0$ near $(0,v^\star)$ and requiring the quadratic in $v^\star$ to have roots of size $1\pm O(\delta)$, which matches the closed separatrix at the canard level, forces $\mu\ge\big(2-\sqrt{4+2\delta^2F_{111}^2}\big)/(\delta^2F_{111})$ up to $O(\delta^2)$. Solving for $\lambda$ gives $\tilde\lambda_\delta(\alpha)$. The formula gives an explicit parameter value past which a slowly drifting predator level triggers large-amplitude population oscillations.

## Depends on

- [Separatrix criterion for large-amplitude oscillations near a singular Hopf bifurcation](separatrix-criterion-for-large-amplitude-oscillations-near-a-singular-hopf-bifurcation.md)

## Sources

- S. Sadhu, *Analysis of long-term transients and detection of early warning signs of major population changes in a two-timescale ecosystem*, arXiv:2105.09411 (2021), Sections 3.2–3.3 and Proposition 3.1. <https://doi.org/10.48550/arXiv.2105.09411>
