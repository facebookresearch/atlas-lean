# Thin geodesic triangles

Every geodesic triangle in $X$ is $\delta$-thin in Gromov's sense: for every vertex $x$, all geodesic segments $\gamma$ from $x$ to $y$ and $\gamma'$ from $x$ to $z$, and every $t$ with $0 \le t \le (y \cdot z)_x$, one has $d(\gamma t, \gamma' t) \le \delta$.

Gromov defines thinness through the comparison tripod $T$ of a triangle $\Delta$ with vertices $x_0, x_1, x_2$: the legs of $T$ have lengths $(x_j \cdot x_k)_{x_i}$, the map $f_\Delta : \Delta \to T$ is isometric on each side, and $\Delta$ is $\delta$-thin if $f_\Delta(u) = f_\Delta(v)$ implies $d(u, v) \le \delta$. Two points of different sides have the same image exactly when they lie on the two sides from a common vertex, at the same distance $t \le (y \cdot z)_x$ from it; so in a geodesic space this definition, quantified over every vertex and every choice of sides, says that all geodesic triangles are $\delta$-thin. In a space that is not geodesic it also constrains pairs of segments from a common vertex with no third side, so it is then slightly stronger than Gromov's condition. In a space with no geodesic segments it holds vacuously.

## Background

- [Geodesic segment](../geodesics-in-metric-spaces/is-geodesic-segment.md): the sides of the triangles.

## Sources

- M. Gromov, *Hyperbolic groups*, in *Essays in Group Theory* (S. M. Gersten, ed.), Math. Sci. Res. Inst. Publ. 8, Springer, 1987, 75–263, §6.3.
