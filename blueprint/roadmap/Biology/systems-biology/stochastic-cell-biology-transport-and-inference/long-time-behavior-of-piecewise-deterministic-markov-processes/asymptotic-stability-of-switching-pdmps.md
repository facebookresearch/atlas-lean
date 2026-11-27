# Asymptotic stability of switching PDMPs via partially integral stochastic semigroups

**Stochastic semigroups.** Let $(E,\Sigma,m)$ be a $\sigma$-finite measure space and $D$ the set of densities ($f \ge 0$, $\|f\|_{L^1} = 1$). A stochastic semigroup $\{P(t)\}_{t\ge0}$ on $L^1(E,\Sigma,m)$ maps $D$ to $D$. It is

- **asymptotically stable** if there is a density $f_*$ with $\lim_{t\to\infty}\|P(t)f - f_*\| = 0$ for all $f \in D$ (then $f_*$ is invariant);
- **sweeping** from a set $B$ if $\lim_{t\to\infty}\int_B P(t)f\,dm = 0$ for all $f \in D$;
- **partially integral** if there is a measurable kernel $k(t,x,y) \ge 0$ with $P(t)f(x) \ge \int_E k(t,x,y)f(y)\,m(dy)$ for all densities and $\iint k(t,x,y)\,m(dy)\,m(dx) > 0$ for some $t > 0$.

**Theorem 1.** A partially integral stochastic semigroup with a unique invariant density $f_* > 0$ a.e. is asymptotically stable.

**Theorem 2.** Let $E$ be a metric space with Borel $\sigma$-algebra, and let $\{P(t)\}$ be partially integral with kernel $k$ such that

- (a) $\int_0^\infty P(t)f\,dt > 0$ a.e. for every $f \in D$, and
- (b) every $y_0 \in E$ has $\varepsilon > 0$, $t > 0$ and $\eta \ge 0$ with $\int\eta\,dm > 0$ and $k(t,x,y) \ge \eta(x)$ for all $x \in E$, $y \in B(y_0,\varepsilon)$.

Then $\{P(t)\}$ is asymptotically stable if it has an invariant density, and sweeping from compact sets otherwise. In particular it is asymptotically stable whenever $E$ is compact.

**Switching flows.** For a PDMP on $G \times \{1,\dots,k\}$ that follows $x' = g_i(x)$ in state $i$ and switches $i \to j$ at rates $q_{ji}(x)$, restrict to a stochastic attractor $S \times \{1,\dots,k\}$. Condition (a) holds if almost every two states can be joined by a concatenation of flow pieces; condition (b) holds at $y_0$ if, at some point reachable from $y_0$, all $q_{ij} > 0$ and the vectors

$$g_2 - g_1, \dots, g_k - g_1,\ [g_i,g_j],\ [g_i,[g_j,g_l]],\ \dots$$

span $\mathbb R^d$ (Hörmander's condition).

**Example (gene expression).** Two smooth one-dimensional flows $x' = g_i(x)$, $i = 1,2$, with points $x_1 < x_2$ such that $g_i > 0$ for $x < x_i$ and $g_i < 0$ for $x > x_i$ (protein level under a gene switching between inactive and active states). All trajectories enter $S = [x_1,x_2]$, states in $(x_1,x_2)$ are mutually reachable, and $g_2 - g_1 > 0$ on $S$, so Theorem 2 applies on the compact set $S \times \{1,2\}$: there is a density $f_*$ supported in $[x_1,x_2]\times\{1,2\}$ with $\|P(t)f - f_*\| \to 0$ for every initial density.

## Expansion

Partial integrality supplies a nontrivial absolutely continuous lower part of the transition kernel; combined with irreducibility (a), a Foguel-type alternative for stochastic semigroups shows that the semigroup either converges to a unique invariant density or mass escapes every set on which the kernel has a uniform lower bound, which by (b) and a covering argument includes every compact set. For switching dynamics, the lower bound in (b) comes from the fact that, under Hörmander's condition, the map from switching times to positions is a submersion, so the law of the position after several switches has a density bounded below near the target point.

## Sources

- Ryszard Rudnicki, Marta Tyran-Kamińska, "Piecewise Deterministic Markov Processes in Biological Models", in Springer Proceedings in Mathematics & Statistics (2015), 235–255, <https://doi.org/10.1007/978-3-319-12145-1_15>. Published version of arXiv:1512.02093, cited next; locators there refer to the arXiv version.
- Ryszard Rudnicki, Marta Tyran-Kamińska, "Piecewise deterministic Markov processes in biological models", arXiv (2015). Section "Long time behavior" (definitions, the two theorems on partially integral semigroups, Hörmander's condition), Example "Gene expression". <https://doi.org/10.48550/arXiv.1512.02093>
