# Random simplex volume is monotone up to an exponential factor

This result proves the proposition stated as [Meckes's question on monotonicity of random simplex volume](meckes-random-simplex-question.md). Precisely, there are constants $c(d) > 0$, $d \in \mathbb{N}$, such that $c(d)^{1/d}$ converges to a real number as $d \to \infty$ and, for every $d$ and all convex bodies $K \subseteq L \subseteq \mathbb{R}^d$,

$$\mathbb{E} V_d(P^K_{d+1}) \le c(d)\, \mathbb{E} V_d(P^L_{d+1}).$$

Here $\mathbb{E} V_d(P^K_{d+1})$ is the expected volume of the convex hull of $d + 1$ independent points uniform in $K$:

$$\mathbb{E} V_d(P^K_{d+1}) = \frac{1}{|K|^{d+1}} \int_{K^{d+1}} \bigl|\operatorname{conv}\{x_0, \dots, x_d\}\bigr| \, dx_0 \cdots dx_d,$$

with $|\cdot|$ Lebesgue measure on $\mathbb{R}^d$, and a convex body is a compact convex set with nonempty interior.

The source states that this is equivalent to a positive solution of Bourgain's slicing problem.

## Sources

- M. Reitzner, High-dimensional random polytopes, in Mini-Workshop: Perspectives in High-Dimensional Probability and Convexity, Oberwolfach Reports 14 (2017), no. 10, p. 519, https://doi.org/10.4171/OWR/2017/10
- B. Klartag and J. Lehec, Affirmative resolution of Bourgain's slicing problem using Guan's bound, Geom. Funct. Anal. (2025), https://doi.org/10.1007/s00039-025-00718-w, arXiv:2412.15044
