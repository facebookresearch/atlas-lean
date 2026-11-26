# Global dynamics of Lotka-Volterra competition on time scales

**Model.** Let $\mathbb{T}$ be a time scale (a closed unbounded subset of $\mathbb{R}$) with forward jump $\sigma(t)$, graininess $\mu(t) = \sigma(t) - t$, delta derivative $x^\Delta$ and $x^\sigma = x\circ\sigma$. With $(\ominus r)(t) = -r/(1+\mu(t)r)$, the two-species competition model is

$$x^\Delta = -(\ominus r)\,x^\sigma\Big(1 - \frac{x}{K} - \alpha y\Big), \qquad y^\Delta = -(\ominus s)\,y^\sigma\Big(1 - \frac{y}{L} - \beta x\Big),$$

with $r,s,\alpha,\beta,K,L > 0$ and nonnegative initial data. For $\mathbb{T} = \mathbb{R}$ it is the classical Lotka-Volterra competition system; for $\mathbb{T} = \mathbb{Z}$ it is the Leslie-Gower competition map. The equilibria are $E_0^* = (0,0)$, $E_K^* = (K,0)$, $E_L^* = (0,L)$ and

$$E^* = (x^*,y^*) = \Big(\frac{K(\alpha L - 1)}{\alpha\beta KL - 1},\ \frac{L(\beta K - 1)}{\alpha\beta KL - 1}\Big),$$

which is positive iff $(\alpha L - 1)(\beta K - 1) > 0$.

**Theorem.** On any time scale $\mathbb{T}$:
1. The open first quadrant and the nonnegative axes are positively invariant, and solutions with nonnegative data are bounded.
2. (Competitive exclusion) If $\alpha L > 1$ and $\beta K < 1$, all solutions with positive initial data converge to $E_L^* = (0,L)$ (and symmetrically $E_K^*$ wins if $\beta K > 1 > \alpha L$).
3. (Coexistence) If $\alpha L < 1$ and $\beta K < 1$, the interior equilibrium $E^*$ is unique, asymptotically stable, and attracts all solutions with positive initial data.
4. (Bistability) If $\alpha L > 1$ and $\beta K > 1$, every solution with positive initial data converges to $E^*$, $E_K^*$ or $E_L^*$; none converges to $E_0^*$.
5. (Degenerate case) If $\alpha L = \beta K = 1$, every point of the common nullcline segment $y = L(1 - x/K)$, $x\in[0,K]$, is a stable equilibrium.

The outcomes are the same as for the continuous and discrete models, independently of the graininess.

## Expansion

The proof is a *dynamic phase plane* argument. For a nullcline $y = \ell(x)$ one tracks the sign of a root-operator $\mathcal{L}_\ell(t,x,y)$: if it is positive at $t = T$, the solution lies above the nullcline on $[T, T+\varepsilon)$, and on all of $[T,\sigma(T)]$ when $T$ is right-scattered. Because the step depends on $\mu(t)$, the regions where each component increases move with time, unlike in the classical phase plane. Still, time-independent invariant regions (boxes around $E^*$, and the region between the nullclines) can be identified; within them each component is eventually monotone, and a monotone bounded solution converges to an equilibrium. On $\mathbb{T} = \mathbb{Z}$ this reduces to the augmented phase portrait for planar maps.

## Sources

- Sabrina Streipert and Gail S. K. Wolkowicz, "Phase Plane Analysis on Time Scales for a Lotka-Volterra Competition Model", arXiv:2605.27806 (2026), Section 2 and Section 3, Theorem 3.3, Proposition 3.4, Theorems 3.5, 3.8, 3.15, 3.20 and 3.23, <https://doi.org/10.48550/arXiv.2605.27806>.
