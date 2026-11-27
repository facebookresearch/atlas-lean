# Local minimum-variance roots are balance points

**Setting.** Let $G$ be an unrooted tree with positive edge lengths and leaf set $L = \{1, \dots, n\}$.
Every point $p$ of $G$ (a vertex, or a point at distance $x$ along an edge) defines a rooting of $G$.
Write $d_i(p)$ for the path length from leaf $i$ to $p$ and

$$\operatorname{mean}(p) = \frac{1}{n} \sum_{i \in L} d_i(p), \qquad \operatorname{var}(p) = \frac{1}{n} \sum_{i \in L} \bigl(d_i(p) - \operatorname{mean}(p)\bigr)^2 .$$

A point $p_0$ is a **local MV** (local minimum-variance root) if the directional derivative of
$\operatorname{var}$ at $p_0$ vanishes in every direction and its second derivative is non-negative; a
**global MV** minimizes $\operatorname{var}$ over all points of $G$. A point $p$ is a **balance point** if
for every edge $(p(u), u)$ containing $p$ (endpoints included), the leaves descending from $u$ and the
remaining leaves have equal mean distance to $p$:

$$\frac{1}{|u|} \sum_{i \in \mathrm{Cld}(u)} d_i(p) = \frac{1}{n - |u|} \sum_{i \notin \mathrm{Cld}(u)} d_i(p).$$

**Proposition.**

1. A point is a local MV if and only if it is a balance point.
2. Every tree has at least one local MV, and the global MV is one of the local MVs.
3. If $G$ is ultrametric when rooted at its true root, that root is its unique balance point, hence its
   unique local MV and global MV.

**Quadratic variance on an edge.** Root $G$ arbitrarily and let $p$ lie on edge $(u, v)$, $u = p(v)$, at
distance $x \in [0, e_v]$ from $u$. With $|v|$ the number of leaves below $v$,
$S_I(v) = \sum_{i \in \mathrm{Cld}(v)} d_i(v)$ and $S_T(u) = \sum_{i \in L} d_i(u)$,

$$\operatorname{var}(p) = (1 - \beta^2)\, x^2 + \Bigl(\alpha - \frac{2 S_T(u) \beta}{n}\Bigr) x + \operatorname{var}(u),
\qquad \alpha = \frac{2 S_T(u) - 4 (S_I(v) + |v| e_v)}{n}, \quad \beta = 1 - \frac{2|v|}{n}.$$

Since $|\beta| < 1$ the parabola is strictly convex, so each edge holds at most one interior local MV,
at the vertex of the parabola when it falls in $[0, e_v]$.

**Theorem (linear-time MinVar rooting).** Computing $\operatorname{mean}$ and $\operatorname{var}$ at the
arbitrary root, then $|v|$ and $S_I(v)$ bottom-up, then $S_T(v) = S_T(p(v)) + (n - 2|v|) e_v$ top-down,
and minimizing the quadratic on each edge, finds the global MV in $O(n)$ time.

## Depends on

- [Ultrametric on taxa](../../splits-compatibility-ultrametrics-and-upgma/is-ultrametric.md)

## Expansion

Moving $p$ a distance $x$ toward $v$ shortens the distances of the $|v|$ leaves below $v$ by $x$ and
lengthens the other $n - |v|$ by $x$. Differentiating $\operatorname{var}$ along the edge gives a
quantity proportional to the difference of the two group means, so a stationary point is exactly a
balance point; convexity on each edge makes stationary points minima. Existence follows from
continuity of $\operatorname{var}$ on the compact tree, and a global minimum is in particular local.
Under a strict clock every leaf is equidistant from the true root, giving zero variance there and
positive variance elsewhere. The algorithm is three traversals; the edge formula updates sums of
distances in constant time per edge, mirroring the linear-time midpoint rooting algorithm, which
minimizes the maximum instead of the variance of root-to-tip distances.

## Sources

- U. Mai, E. Sayyari, S. Mirarab, "Minimum variance rooting of phylogenetic trees and implications for
  species tree reconstruction", PLoS ONE 12 (2017) e0182238, Materials and methods, Propositions 1-3
  and 6, Eqs. 1-7, Algorithm 1 and Theorem 1, <https://doi.org/10.1371/journal.pone.0182238>
  (PMC5553649).
