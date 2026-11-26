# Exclusion model and polynuclear growth

**Flat polynuclear growth (PNG).** Start from a flat interface $h(x,0) = 0$ and nucleation events from a unit-intensity Poisson process on $\mathbb R \times \mathbb R_+$. Each nucleation creates a unit-height island that spreads laterally at unit speed in both directions; islands on the same level merge, and later nucleations on top of an island start the next layer. The *PNG droplet* uses nucleations only inside the forward light cone $|x| \le t$ of the origin. A *directed polymer* on Poisson points is a path through points that is increasing in both coordinates (after rotating the light cone to the quadrant).

**Lemma 3.2 (correspondence).** For a common realization of the Poisson process, a point is active in the [light-cone exclusion model](nearest-neighbor-spacing-of-replication-origins-in-the-exclusion-model.md) if and only if it is a nucleation point on the bottom layer of flat PNG, the boundary between heights $0$ and $1$.

**Theorem 3.3.** Hence the bottom-layer nucleation points of flat PNG have the same nearest-neighbor spacing density $P(s)$ as replication origins in the exclusion model, with $P(s) = 2s + O(s^2)$ at small $s$, a tail $P(s) \sim \frac{8}{\sqrt\pi s^2}e^{-s^2/4}$ at large $s$, and mean density $\sqrt\pi/2$.

**Theorem 3.7 (active points on a triangle).** Scatter a unit-intensity Poisson process in the triangle $T$ with vertices $(0,0)$, $(0,t)$, $(t,t)$ and call a point active if no other point of $T$ lies in its backward light cone, here the quadrant to its lower right. The expected number of active points is

$$N_t = t\sqrt{\frac\pi2}\,\mathrm{erf}\Big(\frac{t}{\sqrt2}\Big) + e^{-t^2/2} - 1.$$

**Lemma 3.6.** In the square $[0,t]^2$, the number of active points on the triangle $\{y \ge x\}$ is at most the number of points on the longest directed polymer in the square, and at most the height at $x = 0$ of the PNG droplet at time $\sqrt2\,t$.

So $N_t$ grows linearly, $N_t \sim t\sqrt{\pi/2}$, strictly below the growth rate $2t$ of the longest directed polymer in a square of side $t$.

## Expansion

In flat PNG an island born at $(x,t)$ occupies, at later times, exactly the forward light cone of its nucleation point within the first layer, so a nucleation event lands on height $0$ (and thus belongs to the bottom layer) precisely when no earlier bottom-layer island has reached it, which is the exclusion rule of the replication model. For the triangle, a point at $(x,y)$ is active with probability $e^{-\text{area}}$ of the part of its quadrant inside $T$, an isosceles right triangle of area $(y - x)^2/2$, and integrating $e^{-(y-x)^2/2}$ over $T$ gives the error-function formula. If $a$ and $b$ are active with $a$ to the left of $b$, then $b$ is not in the lower-right quadrant of $a$, so $b$ is also above $a$: the active points are increasing in both coordinates and themselves form a directed polymer, which yields the comparison with the longest polymer and, through the polymer-PNG correspondence, with the droplet height.

## Depends on

- [Nearest-neighbor spacing of replication origins in the exclusion model](nearest-neighbor-spacing-of-replication-origins-in-the-exclusion-model.md)

## Sources

- H. Day, N. C. Snaith, "Stochastic Models for Replication Origin Spacings in Eukaryotic DNA Replication" (2022), Section 3 (Definitions 3.1, 3.4 and 3.5, Lemmas 3.2 and 3.6, Theorems 3.3 and 3.7), <https://doi.org/10.48550/arXiv.2209.09680>.
