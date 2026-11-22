# HWI inequality

Let $V$ be a smooth ($C^\infty$) convex function on $\mathbb{R}^n$ (or any finite-dimensional real inner product
space) such that $\mu = e^{-V} dx$ is a probability measure. For every smooth ($C^\infty$) positive $f$ with
$\int f \, d\mu = 1$, writing $\nu = f \mu$,

$$\int f \log f \, d\mu \le W_2(\nu, \mu) \left( \int \frac{|\nabla f|^2}{f} \, d\mu \right)^{1/2},$$

that is $H \le W \sqrt{I}$ for the relative entropy $H = \operatorname{KL}(\nu \,\|\, \mu)$, the
[Wasserstein distance](../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein.md) $W$ and the relative Fisher information $I$. Ledoux states it on
weighted Riemannian manifolds $e^{-V} dx$ with a smooth potential $V$, under the curvature
condition $CD(0, \infty)$, which on
$\mathbb{R}^n$ with $e^{-V} dx$ means that $V$ is convex. Ledoux notes that the same argument
under $CD(K, \infty)$ for any real $K$ gives the full form of Otto and Villani's HWI inequality,
which carries a curvature term in $K W^2$.

The inequality expresses the convexity of the relative entropy along Wasserstein geodesics, the
Bakry–Émery condition read in Otto's calculus.

## Sources

- M. Ledoux, *Heat flows, geometric and functional inequalities*, Proceedings of the International Congress of Mathematicians, Seoul 2014, Theorem 4.1.
- F. Otto, C. Villani, *Generalization of an inequality by Talagrand and links with the logarithmic Sobolev inequality*, J. Funct. Anal. 173 (2000), 361–400.
