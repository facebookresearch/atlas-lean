# Extension complexity of convex $n$-gons: is it $\Omega(n)$?

Conjecture: there is $\varepsilon > 0$ such that for infinitely many $n$ some convex polygon with $n$ vertices has extension complexity at least $\varepsilon n$. Precisely, for every $N \in \mathbb{N}$ there are $n \ge N$ and points $v_1, \dots, v_n \in \mathbb{R}^2$ in convex position with

$$\varepsilon\, n \le \operatorname{xc}\bigl(\operatorname{conv}\{v_1, \dots, v_n\}\bigr).$$

Here a set $P \subseteq \mathbb{R}^2$ has an extended formulation of size $r$ when there are $m \in \mathbb{N}$, vectors $a_1, \dots, a_r \in \mathbb{R}^m$, reals $b_1, \dots, b_r$ and a linear map $\pi : \mathbb{R}^m \to \mathbb{R}^2$ such that $Q = \{y \in \mathbb{R}^m : a_i \cdot y \le b_i \text{ for all } i\}$ is bounded and $\pi(Q) = P$, and the extension complexity $\operatorname{xc}(P)$ is the least such $r$ ($0$ if there is none). This is the bounded, linear, inequality-only convention; for a convex polygon with nonempty interior, as every polygon with at least three vertices in convex position is, it equals the usual extension complexity, the least number of facets of a polytope mapped affinely onto the polygon. A convex polygon with $n$ vertices is the convex hull of points $v_1, \dots, v_n \in \mathbb{R}^2$ in convex position: the $v_i$ are pairwise distinct and none lies in the convex hull of the others. It is false; the refutation is [Convex polygons have sublinear extension complexity](linear-extension-complexity-polygons-ref.md).

## Sources

- Open Problem Garden, Extension complexity of (convex) polygons, http://www.openproblemgarden.org/op/extension_complexity_of_convex_polygons
