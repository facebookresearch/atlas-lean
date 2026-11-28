# Equilibria of the two-patch Allee model with nonlinear dispersal

**Model.** A population occupies two patches with densities $u$ (patch with an Allee effect) and $v$ (logistic patch), coupled by density-dependent (nonlinear) dispersal $\delta u(v-u)$ and $\delta v(u-v)$. After nondimensionalization,

$$\dot u = u\left(\frac{u}{m+u} - e - hu\right) + \delta u(v - u), \qquad \dot v = s v(1-v) + \delta v(u - v),$$

with $0 < e < 1$ and $m, h, \delta, s > 0$; $m$ measures the strength of the Allee effect and $e$ the mortality in the Allee patch. Set

$$B = \frac{s\delta}{s+\delta}.$$

The equilibria $E_0 = (0,0)$ and $E_v = \big(0, \tfrac{s}{s+\delta}\big)$ always exist.

**Theorem.** Positive equilibria $(u,v)$ satisfy $v = (s + \delta u)/(s+\delta)$ and

$$(h+B)u^2 + \big[m(h+B) + e - 1 - B\big]u + m(e - B) = 0.$$

1. If $e < B$, there is a unique positive equilibrium.
2. If $e = B$, there is a unique positive equilibrium when $m < 1/(h+B)$ and none when $m \ge 1/(h+B)$.
3. If $B < e < 1$, there is a critical Allee strength $m^*$ (where the two positive roots of the quadratic collide) such that there are two positive equilibria for $m < m^*$, exactly one for $m = m^*$, and none for $m > m^*$; the transition at $m = m^*$ is a saddle-node bifurcation.

Moreover $E_0$ is always a saddle, and $E_v$ is locally stable when $B < e < 1$ and a saddle when $e < B$.

## Expansion

At $E_v$ the Allee patch is empty and the invasion rate of $u$ is $-e + \delta v^* = -e + B$, since $u/(m+u)$ vanishes to first order at $u = 0$; so $B$ is the net immigration-driven growth that the Allee patch receives from the logistic patch. When $B > e$ the Allee patch is always rescued and the coexistence state is unique. When $B < e$ the Allee patch cannot be colonized from low density, a strong Allee threshold appears, and a large Allee constant $m$ eliminates the upper equilibrium through a saddle-node, leaving only the state with the Allee patch empty. Comparisons with linear dispersal show nonlinear dispersal favors persistence when the Allee effect is strong.

## Sources

- Yue Xia, Lijuan Chen, Vaibhava Srivastava and Rana D. Parshad, "Stability and bifurcation analysis of a two-patch model with the Allee effect and dispersal", Mathematical Biosciences and Engineering 20 (2023), 19781–19807, <https://doi.org/10.3934/mbe.2023876>; numbering as in arXiv:2310.10558: Theorems 2.2 and 2.3.
