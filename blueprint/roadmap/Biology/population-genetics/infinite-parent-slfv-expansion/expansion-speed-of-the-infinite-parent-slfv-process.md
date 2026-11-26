# Expansion speed of the infinite-parent spatial Lambda-Fleming–Viot process

**Model.** The $\infty$-parent SLFV process models a population expanding into empty space in $\mathbb{R}^2$. Start from the occupied half-plane $S_0 = \{(x,y) : x \le 0\}$. Reproduction events form a Poisson point process on $\mathbb{R} \times \mathbb{R}^2 \times (0,\infty)^2$ with intensity $C\,dt \otimes dz \otimes \mu(dw, dh)$, $\mu$ a probability measure with bounded support; an event $(t, z, w, h)$ affects the rectangle $\mathcal{R}_{w,h}(z)$ of width $w$ and height $h$ centered at $z$. If $\mathcal{R}_{w,h}(z)$ meets the occupied set $S_{t-}$, the whole rectangle becomes occupied, $S_t = S_{t-} \cup \mathcal{R}_{w,h}(z)$; otherwise nothing happens. Let $\tau_x$ be the first time $(x, 0)$ is occupied (front) and $\sigma_x$ the first time the whole segment from $(0,0)$ to $(x,0)$ is occupied (bulk).

**Theorem.**
1. *(Linear growth.)* There is $\nu > 0$ with $\tau_x / x \to \nu$ in probability and in $L^1$, and $\sigma_x / x \to \nu$ in expectation, as $x \to \infty$; the front and the bulk advance at the same asymptotic speed $1/\nu$.
2. *(Stochasticity can make expansion arbitrarily fast.)* For every $A > 0$ there is a probability measure $\mu^{(A)}$ with bounded support, normalized so that $\int w\,d\mu \cdot \int wh\,d\mu = 1$ (fixed mean reproductive output), for which the expansion speed is at least $A$.
3. *(Two-columns toy model.)* The two-columns growth process $(m_t, M_t)$ on $\{(i,j) \in \mathbb{N}^2 : i \le j\}$, started at $(0,0)$, jumps $(i,i) \to (i, i+1)$ at rate $2$, and from $j \ge i+1$ jumps $(i,j) \to (i, j+1)$ at rate $1$, $(i,j) \to (i+1, j)$ at rate $2$, and $(i,j) \to (i+k, j)$ at rate $1$ for each $k \in \{2, \dots, j - i\}$. With $T_\square$ the time to leave and return to the diagonal,

$$\lim_{t \to \infty} \frac{M_t}{t} = \lim_{t\to\infty}\frac{m_t}{t} = 1 + \frac{1}{2\,\mathbb{E}_{(0,0)}[T_\square]} \in \Big[\frac43, 2\Big] \quad \text{a.s.},$$

so the interaction of two piles raises the growth speed above the speed $1$ of an isolated pile; a recursive scheme computes this speed numerically (about $1.46$).

## Expansion

An occupied region grows whenever a reproduction event straddles its boundary, so growth at the front is driven by protrusions: a site ahead of the bulk lets later events reach further. Variability in event shapes creates protrusions that the bulk then fills, which is why making $\mu$ more heterogeneous at fixed mean output can push the speed past any bound. The two-columns process isolates this effect: a lagging pile catches up in jumps when the leading pile lets it grow sideways, and renewal at returns to the diagonal gives the speed. Such effects of demographic stochasticity on expansion speed bear on range expansions and the genetic diversity left at expanding fronts.

## Sources

- J. L. Igelbrink, A. Louvet, "Effect of stochasticity on the growth of the $\infty$-parent SLFV process", arXiv:2507.22484 (2025), Section 2.1 (model), Theorem 1, Proposition 2 (Section 2.2), Definition 1, Theorem 3, Theorem 4 and Proposition 5, <https://doi.org/10.48550/arXiv.2507.22484>.
