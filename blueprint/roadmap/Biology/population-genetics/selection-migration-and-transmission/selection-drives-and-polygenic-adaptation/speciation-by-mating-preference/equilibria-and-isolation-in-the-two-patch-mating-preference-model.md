# Equilibria and reproductive isolation in the two-patch mating-preference model

**Model.** Individuals carry one of two types $\alpha \in \{A, a\}$ and live in two patches $i \in \{1,2\}$; types are ecologically and demographically equivalent and differ only in mating preference. With $z_{\alpha,i}$ the rescaled density of type $\alpha$ in patch $i$ and $\bar\alpha$ the other type, the large-population limit is

$$
\frac{d z_{\alpha,i}}{dt} = z_{\alpha,i}\left[ b\,\frac{\beta z_{\alpha,i} + z_{\bar\alpha,i}}{z_{\alpha,i} + z_{\bar\alpha,i}} - d - c\,(z_{\alpha,i} + z_{\bar\alpha,i}) - p\,\frac{z_{\bar\alpha,i}}{z_{\alpha,i} + z_{\bar\alpha,i}} \right] + p\,\frac{z_{A,\bar i}\, z_{a,\bar i}}{z_{A,\bar i} + z_{a,\bar i}},
$$

where $b > 0$ is the birth rate between unlike mates, $\beta \ge 1$ the mating-preference factor (like mates are $\beta$ times more likely to produce viable offspring), $0 \le d < b$ the intrinsic death rate, $c > 0$ the competition intensity, and $p \ge 0$ the migration rate (an individual migrates at a rate proportional to the frequency of the other type in its patch). Coordinates are ordered $(z_{A,1}, z_{a,1}, z_{A,2}, z_{a,2})$. Set $\zeta = (\beta b - d)/c$.

**Theorem (equilibria).**

1. For $\beta \ge 1$, the points with a single type in a single patch, $(\zeta,0,0,0)$, $(0,\zeta,0,0)$, $(0,0,\zeta,0)$, $(0,0,0,\zeta)$, are equilibria.
2. For $\beta > 1$ the other nonzero nonnegative equilibria are: each type alone in its own patch, $(\zeta,0,0,\zeta)$ and $(0,\zeta,\zeta,0)$; one type in both patches, $(\zeta,0,\zeta,0)$ and $(0,\zeta,0,\zeta)$; the symmetric mixed state with all coordinates $(b(\beta+1) - 2d)/(4c)$; and four further mixed states built from explicit constants $\tilde\zeta$ and $\Delta > 0$. The only stable equilibria are the four in which there is no gene flow: $(\zeta,0,0,\zeta)$, $(0,\zeta,\zeta,0)$, $(\zeta,0,\zeta,0)$, $(0,\zeta,0,\zeta)$.
3. For $\beta = 1$ (no preference) the remaining equilibria form two segments $\{(\zeta - x, x, x, \zeta - x)\}$ and $\{(\zeta - x, x, \zeta - x, x)\}$, $x \in [0,\zeta]$, of non-hyperbolic equilibria with a zero eigenvalue along the segment; a solution started at $(w - x, x, x, w - x)$ converges to $(\zeta - \zeta x/w,\ \zeta x/w,\ \zeta x/w,\ \zeta - \zeta x/w)$, so isolation does not occur and the limit depends on the initial condition.

**Theorem (convergence to isolation).** Let $\beta > 1$ and

$$
p < p_0 = \frac{\sqrt{b(\beta - 1)\,[\,b(3\beta + 1) - 4d\,]} - b(\beta - 1)}{2}.
$$

Every solution starting in $\mathcal{D} = \{z_{A,1} > z_{a,1},\ z_{a,2} > z_{A,2}\}$ (type $A$ in the majority in patch 1, type $a$ in patch 2) converges to the isolated state $(\zeta,0,0,\zeta)$, and exponentially fast, $\|z(t) - (\zeta,0,0,\zeta)\| \le k_1 e^{-k_2 t}$, from the invariant subset $\mathcal{K}_p \subset \mathcal{D}$ on which both patch totals lie in $\left[\frac{b(\beta+1) - 2d - p}{2c}, \frac{2b\beta - 2d + p}{2c}\right]$.

## Proof depends on

- [Lyapunov's direct method and Lyapunov's instability theorem](../../../../../Analysis/ordinary-differential-equations/lyapunov-s-direct-method/lyapunov-s-direct-method-and-lyapunov-s-instability-theorem.md)

## Expansion

Mating preference acts like positive frequency dependence inside each patch: the per-capita birth rate $b(\beta z_\alpha + z_{\bar\alpha})/(z_\alpha + z_{\bar\alpha})$ is larger for the local majority type, so any $\beta > 1$, however small, drives the local minority type to extinction. Migration couples the patches but, because its rate is proportional to the frequency of the other type, it vanishes once each patch is monomorphic. The convergence proof uses a Lyapunov function $V$ that is non-increasing on $\mathcal{K}_p$ with $\dot V \le -C_1 (z_{a,1} + z_{A,2})$ when $p < p_0$, after showing that solutions from $\mathcal{D}$ enter the invariant set $\mathcal{K}_p$ in finite time. Simulations suggest convergence for all $p$, which the paper states as a conjecture.

## Sources

- Camille Coron, Manon Costa, Hélène Leman and Charline Smadi, *A stochastic model for speciation by mating preferences*, J. Math. Biol. 76(6) (2018), 1421–1463. <https://doi.org/10.1007/s00285-017-1175-9> Theorem 1, Proposition 1.1, Theorem 2, Lemma 3.1, Lemma 3.2, Conjecture 1. Locators use the numbering of the preprint arXiv:1603.01027.
