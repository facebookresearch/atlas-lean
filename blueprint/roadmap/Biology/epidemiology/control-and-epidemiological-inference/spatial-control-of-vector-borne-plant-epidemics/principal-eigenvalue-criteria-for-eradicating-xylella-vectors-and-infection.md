# Principal-eigenvalue criteria for eradicating Xylella vectors and infection

**Model.** On a bounded habitat $\Omega \subset \mathbb R^N$ with no-flux boundary, insect vectors (susceptible $s_1$, infective $i_1$, total $C_I = s_1 + i_1$) diffuse with coefficient $d > 0$ and reproduce logistically on host weeds of spatial density $M(x) \ge 0$; olive-tree canopy (healthy $s_2$, infected $i_2$, total $C_T$) does not move. Controls act on a subregion $\omega \subseteq \Omega$ with indicator $I_\omega$: extra vector mortality $\gamma_1 \ge 0$, weed removal $\gamma_{21} \in [0,1]$, and reduced transmission $\gamma_{22}, \gamma_{23}, \gamma_3 \in [0,1]$. The total vector density satisfies

$$\partial_t C_I = d\,\Delta C_I + r\big[M(x)(1 - \gamma_{21}I_\omega(x)) - \chi C_I\big] C_I - \big(n + \gamma_1 I_\omega(x)\big) C_I, \qquad \partial_\nu C_I = 0,$$

Here $r$ is the vector birth rate, $\chi$ the vector intraspecific competition rate and $n$ the vector mortality rate. With the transmission-reducing controls, the four classes obey, with $\partial_\nu s_1 = \partial_\nu i_1 = 0$ on $\partial\Omega$ (source system (21)–(24)),

$$\begin{aligned}
\partial_t s_1 &= d\,\Delta s_1 + r C_I\big[M(x)(1 - \gamma_{21}I_\omega(x)) - \chi s_1\big] - \big(n + \gamma_1 I_\omega(x)\big) s_1 - \beta(1 - \gamma_{23})\, s_1 \int_\Omega k(x, x')\, i_2(x', t)\,dx',\\
\partial_t i_1 &= d\,\Delta i_1 - \big(n + \gamma_1 I_\omega(x)\big) i_1 - r\chi\, i_1 C_I + \beta(1 - \gamma_{23})\, s_1 \int_\Omega k(x, x')\, i_2(x', t)\,dx',\\
\partial_t s_2 &= (q - \ell) s_2 - \frac{s_2 C_T}{C} - \big(\zeta(1 - \gamma_{22})\, i_1 + b(1 - \gamma_3)\ell\, i_2\big) s_2 + \alpha\, i_2,\\
\partial_t i_2 &= -(\mu + \ell + \alpha)\, i_2 - \frac{i_2 C_T}{C} + \big(\zeta(1 - \gamma_{22})\, i_1 + b(1 - \gamma_3)\ell\, i_2\big) s_2,
\end{aligned}$$

where $q$ is the canopy regrowth rate, $C$ the tree carrying-capacity parameter, $\ell$ the elimination rate of trees by pruning or logging, $\mu$ the infected-tree mortality rate, $\alpha$ the infected-tree recovery rate, $\beta$ the vector infection rate by infected trees, $\zeta$ the tree infection rate by infected vectors, $b$ the infection rate of trees by infected tools, and $k \ge 0$ a bounded kernel; all these constants are positive. Summing the first two equations gives the equation for $C_I$ above, and summing the last two gives $\partial_t C_T = (q - \ell) C_T - C_T^2/C - (\mu + q) i_2$, so $\limsup C_T \le C(q - \ell)^+$.

**Vector threshold.** Let $\tilde\lambda_1$ be the principal eigenvalue of

$$-d\,\Delta\varphi - \big[r M(x)(1 - \gamma_{21}I_\omega(x)) - (n + \gamma_1 I_\omega(x))\big]\varphi = \lambda\varphi \ \text{in } \Omega, \qquad \partial_\nu \varphi = 0.$$

$\tilde\lambda_1$ increases with $\gamma_1$, $\gamma_{21}$ and, by inclusion, with $\omega$ (Rayleigh's principle).

**Proposition 1.**
1. If $\tilde\lambda_1 \ge 0$, the stationary problem has only the trivial solution and $C_I(\cdot, t) \to 0$ in $L^\infty(\Omega)$ for every initial condition: the vectors are eradicated.
2. If $\tilde\lambda_1 < 0$, there is a unique positive stationary solution $C_I^\ast$, the maximal nonnegative one, and $C_I(\cdot,t) \to C_I^\ast$ in $L^\infty(\Omega)$ whenever $C_I(\cdot,0) \not\equiv 0$.

**Theorem 2 (eradication of infection with surviving vectors).** When the transmission-reducing controls $\gamma_{22}, \gamma_{23}, \gamma_3$ act on the whole habitat, if $\tilde\lambda_1 < 0$, $q > \ell$, $C_I(\cdot, 0) \not\equiv 0$ and

$$\Big[\beta(1 - \gamma_{23})\|C_I^\ast\|_\infty \|k\|_2 + \zeta(1 - \gamma_{22})\, C(q-\ell)^+\Big]^2 < \lambda_1\Big[\mu + \ell + \alpha - b(1 - \gamma_3)\ell\, C(q - \ell)^+\Big],$$

where $C_I^\ast$ is the stationary solution of Proposition 1(2) and $\lambda_1$ is the principal eigenvalue of

$$-d\,\Delta\varphi + \big(n + \gamma_1 I_\omega(x)\big)\varphi + r\chi\, C_I^\ast(x)\,\varphi = \lambda\varphi \ \text{in } \Omega, \qquad \partial_\nu\varphi = 0$$

(source Eq. (18); so $\lambda_1 \ge n$, and it can be made arbitrarily large by strong culling over a large enough region), then $i_1(\cdot, t) \to 0$ and $i_2(\cdot, t) \to 0$ in $L^1(\Omega)$. Eq. (25) prints $(1-\gamma_{23})\|C_I^\ast\|_\infty\|k\|_2$ for a kernel "normalized to $\beta$"; Eqs. (21)–(22) use $\beta k$, giving the explicit factor $\beta$ for the kernel used here.

## Expansion

Summing the vector equations removes infection and leaves a diffusive logistic equation with spatially varying growth rate, for which the sign of the principal eigenvalue of the linearization at $0$ is the classical persistence criterion: if the linear operator is nonnegative, every solution decays; if it has a negative eigenvalue, the zero state is unstable and sub- and supersolution arguments yield a unique positive steady state attracting all nontrivial data. Since controls enter only through the potential, increasing culling, weed removal or the controlled area raises $\tilde\lambda_1$, so eradication of vectors can be achieved by acting on a sufficiently large subregion. For Theorem 2, once $C_I \to C_I^\ast$ and $C_T$ is bounded by its carrying capacity, the infected classes are dominated by a linear cooperative system whose decay follows from an energy estimate under the stated inequality.

## Sources

- S. Aniţa, V. Capasso, S. Scacchi, "Controlling the Spatial Spread of a Xylella Epidemic", Bulletin of Mathematical Biology 83(4) (2021) 32, Equations (6)-(25), Proposition 1 and Theorem 2, <https://doi.org/10.1007/s11538-021-00861-z>, PMCID PMC7886609.
