# Self-convolution need not preserve discrete log-concavity

Call a probability mass function $p$ on $\mathbb Z^d$ log-concave if it is the restriction to $\mathbb Z^d$ of a function $f : \mathbb R^d \to [0, \infty)$ with $f((1-t)x + ty) \ge f(x)^{1-t}f(y)^t$ for all $x, y$ and $t \in [0, 1]$; its self-convolution is $(p * p)(z) = \sum_x p(x)p(z - x)$. Self-convolution does not preserve this property: in some dimension $d$ there is a log-concave probability mass function on $\mathbb Z^d$ whose self-convolution is not the restriction to $\mathbb Z^d$ of any such function (Fradelizi, Gavalakis and Rapaport).

The counterexample is the uniform mass function on the four vertices of the Reeve tetrahedron:
$(0,0,0)$, $(1,0,0)$, $(0,1,0)$ and $(1,1,2)$. These are the only lattice points of the
tetrahedron, so the function equal to $1/4$ on the tetrahedron and $0$ off it is a log-concave
extension. The self-convolution is positive at $(1,1,0)$ and $(1,1,2)$, each a sum of two
vertices, but zero at their midpoint $(1,1,1)$: the sum of two vertex heights cannot be odd.
A log-concave extension would have to be positive at this midpoint.

## Sources

- Problem: M. Fradelizi (with L. Gavalakis and M. Rapaport), On the monotonicity of discrete entropy for log-concave random vectors in Z^d, in Convex Geometry and its Applications, Oberwolfach Reports 21 (2024), no. 58, p. 3360, DOI 10.4171/OWR/2024/58.
- Resolution: M. Fradelizi, L. Gavalakis and M. Rapaport, On the monotonicity of discrete entropy for log-concave random vectors on Z^d, Discrete Comput. Geom. (2026), DOI 10.1007/s00454-025-00813-7, arXiv:2401.15462, https://doi.org/10.1007/s00454-025-00813-7.
