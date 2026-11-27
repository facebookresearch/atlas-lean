# Stability of the two-patch Rosenzweig–MacArthur model with predation-driven dispersal

**Model.** Prey $x_i$ (immobile) and predators $y_i$ live in patches $i=1,2$. Predators leave patch $i$ for patch $j$ at a rate proportional to the predation term in patch $j$:

$$
\begin{aligned}
\frac{dx_1}{dt} &= x_1\Big(1-\frac{x_1}{K_1}\Big) - \frac{a_1x_1y_1}{1+x_1},\\
\frac{dy_1}{dt} &= \frac{a_1x_1y_1}{1+x_1} - d_1y_1 + \rho_1\Big(\frac{a_1x_1y_1}{1+x_1}\,y_2 - \frac{a_2x_2y_2}{1+x_2}\,y_1\Big),\\
\frac{dx_2}{dt} &= r x_2\Big(1-\frac{x_2}{K_2}\Big) - \frac{a_2x_2y_2}{1+x_2},\\
\frac{dy_2}{dt} &= \frac{a_2x_2y_2}{1+x_2} - d_2y_2 + \rho_2\Big(\frac{a_2x_2y_2}{1+x_2}\,y_1 - \frac{a_1x_1y_1}{1+x_1}\,y_2\Big),
\end{aligned}
$$

with $r,a_i,K_i,d_i>0$ and dispersal constants $\rho_i\ge 0$. Write $r_1=1$, $r_2=r$, $\mu_i=\frac{d_i}{a_i-d_i}$ and $\nu_i=\frac{r_i(K_i-\mu_i)(1+\mu_i)}{a_iK_i}$; the isolated patch $i$ has interior equilibrium $(\mu_i,\nu_i)$, which is globally stable for $\frac{K_i-1}{2}<\mu_i<K_i$ and surrounded by a globally stable limit cycle for $0<\mu_i<\frac{K_i-1}{2}$ (Hopf bifurcation at $\mu_i=\frac{K_i-1}{2}$).

**Theorem.**

1. $\mathbb R_+^4$ is positively invariant, solutions are bounded and $\limsup_{t\to\infty}x_i(t)\le K_i$.
2. *(Predator extinction.)* If $\mu_i>K_i$ for $i=1,2$, the boundary equilibrium $(K_1,0,K_2,0)$ is globally asymptotically stable, and there is no interior equilibrium.
3. *(Interior equilibrium with equal death rates.)* Let $d_1=d_2=d$ and $0<\mu_i<K_i$ for $i=1,2$. Then $E^i=(\mu_1,\nu_1,\mu_2,\nu_2)$ is an interior equilibrium for all $\rho_1,\rho_2\ge 0$, and
   - $E^i$ is locally asymptotically stable if $\frac{K_i-1}{2}<\mu_i<K_i$ for both $i$;
   - $E^i$ is unstable if $\frac{\mu_1(K_1a_1-a_1-K_1d-d)}{a_1K_1}+\frac{r\mu_2(K_2a_2-a_2-K_2d-d)}{a_2K_2}>0$;
   - *(stabilization by dispersal)* if $(K_1a_1-a_1-K_1d-d)(K_2a_2-a_2-K_2d-d)<0$, the weighted sum above is negative, and $K_ia_i-a_i-K_id-d>0$ (i.e. $\mu_i<\frac{K_i-1}{2}$, so patch $i$ alone oscillates) for some $i$, then $E^i$ becomes locally asymptotically stable for all sufficiently large dispersal constants $\rho_i$ (an explicit lower bound is available).

## Expansion

With $d_1=d_2$, at $(\mu_1,\nu_1,\mu_2,\nu_2)$ the two attraction strengths satisfy $\frac{a_1\mu_1}{1+\mu_1}=\frac{a_2\mu_2}{1+\mu_2}=d$, so the dispersal terms $\rho_i d(y_jy_i-y_iy_j)$ vanish and the uncoupled equilibria persist under coupling. Dispersal does change the Jacobian: it couples the predator equations through terms proportional to $\rho_i$, which redistribute the destabilizing prey self-feedback $\frac{\mu_i(K_ia_i-a_i-K_id-d)}{a_iK_i}$ (positive exactly when patch $i$ is beyond its Hopf point). When one patch is oscillatory and the other strongly damped, and their weighted sum is negative, strong attraction-driven dispersal lets the stable patch dominate the linearization; the Routh–Hurwitz conditions of the $4\times 4$ Jacobian then hold for large $\rho_i$. Item 2 uses $\limsup x_i\le K_i$ and the fact that predator growth $\frac{a_ix_i}{1+x_i}-d_i$ is negative for $x_i<\mu_i$.

## Sources

- Y. Kang, S. K. Sasmal, K. Messan, *A two-patch prey-predator model with dispersal in predators driven by the strength of predation*, arXiv:1505.03820 (2015). <https://doi.org/10.48550/arXiv.1505.03820> — Theorem 2.1 (basic properties and single-patch dynamics), Theorems 3.2 and 3.5 (global stability of the predator-free state; no interior equilibrium), Theorem 3.6 (interior equilibrium and its stability). Published version: Mathematical Biosciences and Engineering 14(4) (2017), 843–880, <https://doi.org/10.3934/mbe.2017046>; locators above refer to the arXiv version.
