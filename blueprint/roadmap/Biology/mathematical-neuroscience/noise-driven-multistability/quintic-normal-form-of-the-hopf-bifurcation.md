# Quintic normal form of the Hopf bifurcation and its bistable window

**Model.** In polar coordinates $(r, \phi)$, consider the amplitude–phase system

$$\dot r = -r^5 + \lambda r^3 + \beta r, \qquad \dot\phi = \omega_0 + f(r),$$

with shape parameter $\lambda \in \mathbb{R}$, bifurcation parameter $\beta \in \mathbb{R}$, and (here) constant phase velocity $f \equiv 0$. Fixed points of the amplitude equation with $r > 0$ are limit cycles of the planar system; $r = 0$ is always a fixed point (a focus of the planar system).

**Proposition.** Positive amplitude equilibria satisfy $r^4 - \lambda r^2 - \beta = 0$, that is

$$r_\pm^2 = \frac{\lambda \pm \sqrt{\lambda^2 + 4\beta}}{2}.$$

1. *Supercritical case* ($\lambda < 0$). For $\beta < 0$ the origin is the global attractor. At $\beta = 0$ it loses stability and for $\beta > 0$ a unique stable limit cycle of amplitude $r_+$ grows continuously from zero ($r_+^2 \approx \beta/|\lambda|$ for small $\beta$).
2. *Subcritical case* ($\lambda > 0$). For $\beta < -\lambda^2/4$ the origin is the global attractor. For $-\lambda^2/4 < \beta < 0$ the system is **bistable**: the stable origin and a stable limit cycle of amplitude $r_+$ coexist, separated by an unstable limit cycle of amplitude $r_-$ (the separatrix between the two basins). At $\beta = -\lambda^2/4$ the two cycles are born in a saddle-node (fold) of limit cycles; at $\beta = 0$ the unstable cycle collapses onto the origin (subcritical Hopf bifurcation), and for $\beta > 0$ the large cycle is the global attractor.
3. For $\lambda = 4$, bistability occupies exactly $-4 < \beta < 0$; at $\beta = -2$, the unstable and stable cycles have amplitudes $\sqrt{2 - \sqrt 2} \approx 0.77$ and $\sqrt{2 + \sqrt 2} \approx 1.85$.

A cubic amplitude equation $\dot r = \lambda r^3 + \beta r$ can represent either a supercritical ($\lambda < 0$) or a subcritical ($\lambda > 0$) Hopf bifurcation but cannot connect them smoothly and has no bounded large cycle in the subcritical case; the quintic term supplies both the saturation and the continuous transition between the two regimes.

## Expansion

The amplitude field $g(r) = r(-r^4 + \lambda r^2 + \beta)$ is odd, so it suffices to study $r \ge 0$. Its positive zeros are the real positive roots of the quadratic in $r^2$; for $\lambda > 0$ both $r_\pm^2$ are positive exactly when $\lambda^2 + 4\beta > 0$ and $\beta < 0$. Stability follows from the sign of $g$: $g < 0$ for large $r$, $g'(0) = \beta$, and the sign alternates across simple roots, so the outer root $r_+$ is stable and the inner root $r_-$ unstable. The parameter point $(\lambda, \beta) = (0, 0)$, where the cubic coefficient changes sign, is a Bautin (generalized Hopf) point, and the quintic form is its truncated normal form. With additive noise, trajectories in the bistable window switch between the low-amplitude focus and the high-amplitude cycle; this has been proposed as the mechanism of switching between low- and high-power epochs of the human alpha rhythm.

## Sources

- Freyer F, Roberts JA, Ritter P, Breakspear M, "A canonical model of multistability and scale-invariance in biological systems" (2012), Results, "Bifurcations of a normal form model" (Equations (1)–(2) and Figures 2–3), <https://doi.org/10.1371/journal.pcbi.1002634>, PMCID PMC3415415.
