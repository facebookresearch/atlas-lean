# Edge-function test for points in a triangle

Let $a, b, c$ be the vertices of a nondegenerate triangle in counterclockwise order, and for points $u, v, x$ of the plane let $E_{uv}(x) = (v - u) \times (x - u)$ be twice the signed area of the triangle $(u, v, x)$. A point $x$ lies in the closed triangle $abc$ if and only if $E_{ab}(x) \ge 0$, $E_{bc}(x) \ge 0$ and $E_{ca}(x) \ge 0$, and in its interior if and only if all three are positive.

Here the closed triangle is the convex hull of the three vertices in the real plane, and the interior is its ordinary topological interior. Counterclockwise nondegeneracy means $E_{ab}(c)>0$.

## Sources

- J. Pineda, "A parallel algorithm for polygon rasterization", *SIGGRAPH 1988*
- M. de Berg, O. Cheong, M. van Kreveld and M. Overmars, *Computational Geometry: Algorithms and Applications*, 3rd ed., Springer, 2008
