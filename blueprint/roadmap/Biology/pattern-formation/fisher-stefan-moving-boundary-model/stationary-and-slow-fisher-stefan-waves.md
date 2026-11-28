# Stationary and slow Fisher–Stefan waves

**Setting.** Consider [Fisher–Stefan travelling waves](fisher-stefan-travelling-waves.md) $U(z)$ on $z < 0$ with $U'' + cU' + U(1-U) = 0$, $U(-\infty) = 1$, $U(0) = 0$ and $c = -\kappa U'(0)$.

**Proposition (exact stationary wave).** For $c = 0$ the phase-plane trajectory through $(1,0)$ with $V < 0$ is

$$V(U) = -\sqrt{\tfrac{2U^3}{3} - U^2 + \tfrac13} = -\frac{(1-U)\sqrt{3(2U+1)}}{3},$$

and the stationary wave is

$$U(z) = \frac32\tanh^2\!\Big(\frac z2 - \operatorname{arctanh}\frac{1}{\sqrt3}\Big) - \frac12,\qquad z \le 0,$$

with edge slope $U'(0) = -1/\sqrt3$. The full level set $V^2 = \tfrac{2U^3}{3} - U^2 + \tfrac13$ is a teardrop-shaped orbit homoclinic to the saddle $(1,0)$, enclosing the linear centre $(0,0)$ and crossing $V = 0$ again at $U = -\tfrac12$; the stationary wave is its arc in $U > 0$, $V < 0$. This is an exact solution of the half-line problem only: on a finite domain with $\kappa = 0$ the boundary stays at its initial position $L_0$, and the profile violates the Neumann condition at $z = -L_0$ because $U'(-L_0) \ne 0$.

This corrects Eq. (15) of arXiv:2008.00662v3 as printed, $U(z) = \frac32\big[\tanh\big(\frac z2 - \operatorname{arctanh}\frac{\sqrt3}{3}\big)^2 - 1\big]$, which has the $-1$ inside the bracket: at $z = 0$, where $\tanh^2 = \frac13$, it gives $U(0) = \frac32\big(\frac13 - 1\big) = -1$ instead of the boundary value $U(0) = 0$, and as $z \to -\infty$ it tends to $0$ instead of $1$. The form above, $\frac32\tanh^2(\cdot) - \frac12$, gives $U(0) = \frac32 \cdot \frac13 - \frac12 = 0$ and $U(-\infty) = 1$.

**Proposition (slow waves).** For $|c| \ll 1$, the expansion $V(U) = V_0(U) + cV_1(U) + c^2V_2(U) + O(c^3)$ with $V_k(1) = 0$ gives $V(0) = -1/\sqrt3 + O(c)$, hence

$$\kappa(c) = \sqrt3\,c + O(c^2),\qquad c \sim \frac{\kappa}{\sqrt3}\quad(\kappa \to 0),$$

for both slowly invading ($\kappa > 0$) and slowly receding ($\kappa < 0$) waves; the paper carries the expansion to $O(c^3)$, which is accurate for $|c| \lesssim 0.5$.

## Depends on

- [Invading and receding Fisher–Stefan travelling waves](fisher-stefan-travelling-waves.md)

## Proof depends on

- [Invading and receding Fisher–Stefan travelling waves](fisher-stefan-travelling-waves.md)

## Expansion

With $c = 0$, $V\,dV/dU = -U(1-U)$ integrates to $V^2/2 + U^2/2 - U^3/3 = 1/6$, the constant fixed by $V = 0$ at $U = 1$; at $U = 0$ this gives $V^2 = 1/3$. For the profile write $T = \tanh(z/2 + \delta)$ and $U = \tfrac32T^2 - \tfrac12$: then $U' = \tfrac32T(1-T^2)$ and $U'' = \tfrac34(1-T^2)(1-3T^2) = U(U-1)$, so the ODE holds; $U(0) = 0$ needs $T(0)^2 = 1/3$, and $U'(0) < 0$ selects $T(0) = -1/\sqrt3$, i.e. $\delta = -\operatorname{arctanh}(1/\sqrt3)$. In the slow-wave expansion the $O(1)$ problem is the stationary one, and $\kappa = -c/V(0) = -c/(V_0(0) + O(c)) = \sqrt3\,c + O(c^2)$. In the source's finite-domain simulation with $\kappa = 0$ (Figure 5), the late-time solution near the edge is visually indistinguishable from this profile, and its phase-plane trace from the $V < 0$ arc.

## Sources

- M. El-Hachem, S. W. McCue and M. J. Simpson, "Invading and receding sharp-fronted travelling waves", Bulletin of Mathematical Biology (2021), <https://doi.org/10.1007/s11538-021-00862-y>. Numbering as in the preprint arXiv:2008.00662v3 (<https://arxiv.org/abs/2008.00662>): Sections 3.3.1–3.3.2, Equations (13)–(19) and (26)–(28), Figure 5.
