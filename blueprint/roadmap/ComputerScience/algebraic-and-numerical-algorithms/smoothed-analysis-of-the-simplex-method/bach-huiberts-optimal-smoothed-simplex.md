# Bach-Huiberts optimal noise dependence for the smoothed simplex method

For base data $\bar A, \bar b$ whose rows $(\bar a_i, \bar b_i)$ have norm at most $1$ and a unit objective $c$, let the semi-random shadow size $R(n, d, \sigma)$ be the maximum over $\bar A, \bar b, c$ of the expected number of vertices of the projection of $\{x : (\bar A + \hat A)x \le \bar b + \hat b\}$ onto $\mathrm{span}(c, Z)$, where $\hat A, \hat b$ have independent $\mathcal{N}(0, \sigma^2)$ entries and $Z \ne 0$ is independent and spherically symmetric. Then

$$
R(n, d, \sigma) = O\!\left(\sigma^{-1/2} d^{11/4} \log(n)^{7/4} + d^3 \log(n)^2\right),
$$

and there is a simplex method (a three-phase semi-random shadow vertex method) whose expected number of pivot steps on smoothed programs is $O\big(R(n + d, d, \sigma')\big)$ with the clipped noise level $\sigma' = \min\{\sigma, 1/\sqrt{d\ln n}, 1/(d^{3/2}\ln d)\}$. The additive $d^3\log(n)^2$ term and the clipping are part of the bound: for noise levels up to $\sigma = 1$ they cannot be absorbed into the $\sigma^{-1/2}$ term uniformly in $d$ and $n$.

Conversely, let $d \ge 2$ and let $\sigma > 0$ satisfy the small-noise condition $\sigma\sqrt{\ln(4/\sigma)} \le 1/(2600\,d)$, and take $n = \lfloor (4/\sigma)^d \rfloor$. There are $\bar A, \bar b$ with rows of $(\bar A, \bar b)$ of norm at most $1$ such that, when $A, b$ have independent Gaussian entries with means $\bar A, \bar b$ and variance $\sigma^2$, with probability at least $1 - n^{-d}$ the polyhedron $\{x : Ax \le b\}$ has combinatorial diameter at least

$$
\frac{(d-1)^{1/2}}{24\sqrt{\sigma\sqrt{\ln(4/\sigma)}}} = \Omega\!\left(\sigma^{-1/2} d^{1/2} \ln(4/\sigma)^{-1/4}\right),
$$

and for every nonzero objective its maximizing and minimizing vertices are at least this far apart. In particular $R(\lfloor (4/\sigma)^d \rfloor, d, \sigma) \ge \sqrt{d-1}\,/\big(96\sqrt{\sigma\sqrt{\ln(4/\sigma)}}\big)$, so any bound on shadow path lengths of the form $\mathrm{poly}(d, \sigma^{-1}, \log n)$ has a term of order at least $\sigma^{-1/2}$: up to polylogarithmic factors, the noise dependence $\sigma^{-1/2}$ is optimal.

## Proof sketch

The upper bound uses a random second objective $Z$: the shadow plane $\mathrm{span}(c, Z)$ is random, which removes the near-degenerate projections that fixed-plane analyses control only through the constraint noise at a cost of $\sigma^{-1/2}$ each. The path from $Z$ to $c$ is split into pieces between $Z + 2^{i-1}c$ and $Z + 2^i c$, and a separation measure on the primal shadow polygon bounds the expected length of each piece; for $\sigma > 1/(4\sqrt{d\log n})$ a direct bound of $O(d^3\log(n)^2)$ applies. The lower bound, for the normalized instance and with the stated constants, is Bach–Huiberts Theorem 57. Its geometric core is a ball-sandwich and diameter argument, described here for unscaled data: take the rows of $\bar A$ to be a $\sigma$-dense set of $\lfloor (4/\sigma)^d \rfloor$ unit vectors and $\bar b = \mathbf{1}$. These combined rows $(\bar a_i, 1)$ have norm $\sqrt2$, so this unscaled data does not itself satisfy the row normalization. Dividing $(A, b)$ by a positive factor leaves $\{x : Ax \le b\}$ unchanged and divides the noise level by the same factor, so the normalized statement corresponds to this argument at a noise level changed by a constant factor; the resulting constants are not tracked here. With probability at least $1 - n^{-d}$ every perturbation has norm at most $4\sigma\sqrt{d\ln n}$, so the smoothed polyhedron lies between the balls of radii $1 - 2\eta$ and $1 + 4\eta$ with $\eta = 4d\sigma\sqrt{\ln(4/\sigma)} \le 1/8$. Every facet of its polar then has diameter at most $8\sqrt\eta$, so any edge path from a maximizer to a minimizer of an objective has at least $(d-1)\big(2/((1+4\eta)\,8\sqrt\eta) - 3\big)$ edges.

## Depends on

- [Gaussian-smoothed linear programs and smoothed pivot complexity](gaussian-smoothed-linear-programs.md)

## Proof depends on

- [Huiberts-Lee-Zhang smoothed shadow bound O(sigma^{-3/2} d^{13/4} log^{5/4} n)](huiberts-lee-zhang-upper-bound.md)
- [Shadow vertices are bounded by edges of the polar section](shadow-vertices-and-polar-section.md)
- [The shadow vertex pivot rule and the smoothed shadow bound](shadow-vertex-rule-and-shadow-bound.md)

## Sources

- E. Bach, S. Huiberts, "Optimal Smoothed Analysis of the Simplex Method", FOCS (2025), arXiv:2504.04197v2 (May 2026), Section 1.1, Theorem 52 and Theorem 57.
- S. Huiberts, Y. T. Lee, X. Zhang, "Upper and Lower Bounds on the Smoothed Complexity of the Simplex Method", STOC (2023), TheoretiCS 4 (2025), arXiv:2211.11860.
