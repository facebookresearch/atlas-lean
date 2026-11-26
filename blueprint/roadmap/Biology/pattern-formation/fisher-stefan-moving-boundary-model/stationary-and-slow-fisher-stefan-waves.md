# Stationary and slow Fisher–Stefan waves

**Setting.** Consider [Fisher–Stefan travelling waves](fisher-stefan-travelling-waves.md) $U(z)$ on $z < 0$ with $U'' + cU' + U(1-U) = 0$, $U(-\infty) = 1$, $U(0) = 0$ and $c = -\kappa U'(0)$.

**Proposition (exact stationary wave).** For $c = 0$ the phase-plane trajectory through $(1,0)$ with $V < 0$ is

$$V(U) = -\sqrt{\tfrac{2U^3}{3} - U^2 + \tfrac13} = -\frac{(1-U)\sqrt{3(2U+1)}}{3},$$

and the stationary wave is

$$U(z) = \frac32\tanh^2\!\Big(\frac z2 - \operatorname{arctanh}\frac{1}{\sqrt3}\Big) - \frac12,\qquad z \le 0,$$

with edge slope $U'(0) = -1/\sqrt3$. It is the $V < 0$ arc of a teardrop-shaped homoclinic orbit of the centre at the origin, and it is the late-time limit of the moving-boundary PDE when $\kappa = 0$.

**Proposition (slow waves).** For $|c| \ll 1$, the expansion $V(U) = V_0(U) + cV_1(U) + c^2V_2(U) + O(c^3)$ with $V_k(1) = 0$ gives $V(0) = -1/\sqrt3 + O(c)$, hence

$$\kappa(c) = \sqrt3\,c + O(c^2),\qquad c \sim \frac{\kappa}{\sqrt3}\quad(\kappa \to 0),$$

for both slowly invading ($\kappa > 0$) and slowly receding ($\kappa < 0$) waves; the paper carries the expansion to $O(c^3)$, which is accurate for $|c| \lesssim 0.5$.

## Depends on

- [Invading and receding Fisher–Stefan travelling waves](fisher-stefan-travelling-waves.md)

## Expansion

With $c = 0$, $V\,dV/dU = -U(1-U)$ integrates to $V^2/2 + U^2/2 - U^3/3 = 1/6$, the constant fixed by $V = 0$ at $U = 1$; at $U = 0$ this gives $V^2 = 1/3$. For the profile write $T = \tanh(z/2 + \delta)$ and $U = \tfrac32T^2 - \tfrac12$: then $U' = \tfrac32T(1-T^2)$ and $U'' = \tfrac34(1-T^2)(1-3T^2) = U(U-1)$, so the ODE holds; $U(0) = 0$ needs $T(0)^2 = 1/3$, and $U'(0) < 0$ selects $T(0) = -1/\sqrt3$, i.e. $\delta = -\operatorname{arctanh}(1/\sqrt3)$. In the slow-wave expansion the $O(1)$ problem is the stationary one, and $\kappa = -c/V(0) = -c/(V_0(0) + O(c)) = \sqrt3\,c + O(c^2)$.

## Sources

- M. El-Hachem, S. W. McCue and M. J. Simpson, "Invading and receding sharp-fronted travelling waves", Bulletin of Mathematical Biology (2021), Sections 3.3.1–3.3.2, Equations (13)–(19) and (26)–(28), <https://doi.org/10.1007/s11538-021-00862-y>.
