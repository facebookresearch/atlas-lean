# Filament-angle bistability of a planar lamellipodium

In the rigid-filament, planar reduction of the Filament Based Lamellipodium Model, two families of straight actin filaments make angles $\omega$ and $\pi - \omega$ with the leading edge, with $\omega \in [0, \pi/2]$. Their crossing angle is $\varphi = \pi - 2\omega$. The membrane force $f_{mem}$ and stress-fibre force $f_{stress}$ act normal to the edge. The angle then obeys an autonomous ODE whose right-hand side is a positive multiple of

$$
\cos\omega \left( \frac{f_{stress} - f_{mem}}{4} + h(\omega) \right),
\qquad
h(\omega) = \mu_T (\pi - 2\omega - \varphi_0) - 2\omega\, \bar\mu_{TM} (\pi - 2\omega - \bar\varphi)_+ .
$$

Here $\mu_T > 0$ is the cross-link twisting stiffness with equilibrium angle $\varphi_0$. Myosin acts only on sufficiently antiparallel crossings, with twisting stiffness $\mu_{TM}(\varphi) = \bar\mu_{TM} (\varphi - \bar\varphi)_+$, where $\varphi_0 < \bar\varphi < \pi$.

**Lemma 1.** If

$$
\frac{\bar\mu_{TM}}{\mu_T} > \frac{\bar\varphi + \pi - 2\varphi_0 + 2\sqrt{(\pi - \varphi_0)(\bar\varphi - \varphi_0)}}{(\pi - \bar\varphi)^2},
$$

then $h$ has exactly three simple zeros on $(0, \pi/2)$:

$$
\frac{\pi}{2} > \omega_{10} = \frac{\pi - \varphi_0}{2} > \frac{\pi - \bar\varphi}{2} > \omega_{20} > \omega_{30} > 0 .
$$

**Theorem 2.** Under this condition, and for $|f_{stress} - f_{mem}|$ small enough, the angle equation has four stationary solutions:

$$
\omega_0 = \frac{\pi}{2} > \omega_1 = \frac{\pi - \varphi_0}{2} + \frac{f_{stress} - f_{mem}}{8\mu_T} > \frac{\pi - \bar\varphi}{2} > \omega_2 > \omega_3 > 0 .
$$

Of these, $\omega_1$ (cross-link dominated) and $\omega_3$ (collapsed by myosin) are asymptotically stable, while $\omega_0$ and $\omega_2$ are unstable. At a stable state the edge protrudes at the constant speed $\dot y = v \sin\omega_{1,3} - (f_{stress} + f_{mem})/(\mu_A L)$.

## Expansion

For $\omega > (\pi - \bar\varphi)/2$ myosin is inactive and $h$ is linear with zero $\omega_{10}$. Below that threshold, set $x = 2\omega$. Then $h = 0$ becomes the quadratic $\bar\mu_{TM} x (\pi - \bar\varphi - x) = \mu_T (\pi - \varphi_0 - x)$. This quadratic has two roots in $(0, \pi - \bar\varphi)$ exactly when its discriminant is positive, and that is the stated stiffness-ratio condition. Since $h$ changes sign $+,-,+,-$ through the zeros, $h' < 0$ at $\omega_{10}$ and $\omega_{30}$. A small force imbalance perturbs the zeros, and the factor $\cos\omega$ adds the equilibrium $\omega_0 = \pi/2$. So angle-selective myosin contractility alone produces two stable network geometries.

## Sources

- Hirsch S, Manhart A, Schmeiser C. Mathematical modeling of myosin induced bistability of lamellipodial fragments. *Journal of Mathematical Biology* 74 (2017) 1–22. <https://doi.org/10.1007/s00285-016-1008-2>. PMCID: PMC5206284.
