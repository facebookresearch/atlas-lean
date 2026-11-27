# Ellipsoids have bounded Gaussian surface area

The Gaussian surface area of $A \subseteq \mathbb R^n$ is $\Gamma(A) = \liminf_{\delta \to 0^+}\gamma_n(A_\delta \setminus A)/\delta \in [0, \infty]$, where $\gamma_n$ is the standard Gaussian measure and $A_\delta$ the closed $\delta$-neighbourhood of $A$. An ellipsoid is a set $\{x : \|T(x - c)\| \le 1\}$ with $T$ invertible linear and $c \in \mathbb R^n$. There is a constant $C$ with $\Gamma(A) \le C$ for every ellipsoid $A$ in every dimension. This follows from Kane's bound on the Gaussian surface area of polynomial threshold functions (2011).

## Sources

- Problem: AIM workshop Algorithmic convex geometry, problem list, https://aimath.org/WWN/convexgeometry/convexgeometry.pdf, Problem 11 (R. O'Donnell).
- Resolution: D. M. Kane, The Gaussian surface area and noise sensitivity of degree-d polynomial threshold functions, Comput. Complexity 20 (2011), 389-412, https://doi.org/10.1007/s00037-011-0012-6.
