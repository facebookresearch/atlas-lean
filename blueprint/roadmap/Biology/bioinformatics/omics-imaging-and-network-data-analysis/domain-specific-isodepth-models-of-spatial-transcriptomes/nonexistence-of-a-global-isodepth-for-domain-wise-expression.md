# Nonexistence of a global isodepth for domain-wise expression

In spatially resolved transcriptomics, a tissue slice $T \subseteq \mathbb{R}^2$ carries a gene expression function $f = (f_1, \dots, f_G) : T \to \mathbb{R}^G$. A **global isodepth model** assumes $f(x, y) = h(d(x, y))$ for a single continuously differentiable scalar field $d : \mathbb{R}^2 \to \mathbb{R}$ (the isodepth, a topographic coordinate for the whole tissue) and a piecewise continuously differentiable $h : \mathbb{R} \to \mathbb{R}^G$; then all spatial gradients are parallel to $\nabla d$ and spatial domains are unions of level sets of $d$.

**Theorem.** Let $T$ be a rectangle containing two adjacent closed squares $R_1$, $R_2$ (spatial domains sharing an edge), with disjoint interiors $R_1^\circ$, $R_2^\circ$. Suppose the expression is given domain-wise by separate domain functions, $f = f_1$ on $R_1^\circ$ and $f = f_2$ on $R_2^\circ$ (values on the shared edge are assigned to either domain and play no role), and that some gene $g$ satisfies

$$f_{1,g}(x, y) = x \ \text{ on } R_1^\circ, \qquad f_{2,g}(x, y) = y \ \text{ on } R_2^\circ.$$

Then there is no continuously differentiable $d$ and piecewise continuously differentiable $h$ with $f(x, y) = h(d(x, y))$ on $R_1^\circ \cup R_2^\circ$.

## Expansion

A short argument needs only continuity of $d$. On $R_1^\circ$, $x = h_g(d(x,y))$, so different open vertical segments of $R_1^\circ$ are mapped by $d$ into disjoint sets; each image is an interval because $d$ is continuous, and only countably many disjoint intervals can have positive length. Hence $d$ is constant on all but countably many vertical segments of $R_1^\circ$, and by continuity on all of them: $d = \alpha(x)$ on $R_1^\circ$. In the same way $d = \beta(y)$ on $R_2^\circ$. Say the shared edge is vertical, $\{x_0\} \times [y_0, y_1]$, with $R_1$ to its left. Since $d$ is continuous on $\mathbb R^2$, for $y_0 < y < y_1$ the limits of $d$ from the two sides agree: $\lim_{x \uparrow x_0} \alpha(x) = d(x_0, y) = \lim_{x \downarrow x_0} d(x, y) = \beta(y)$. The left-hand limit does not depend on $y$, so $\beta$ is constant on $(y_0, y_1)$, $d$ is constant on $R_2^\circ$, and $f_{2,g} = h_g \circ d$ would be constant there, contradicting $f_{2,g} = y$; a horizontal shared edge is symmetric. Only the continuous isodepth is matched across the interface; no common expression value on the edge is assumed. Biologically, the example is two neighboring domains whose expression gradients point in perpendicular directions (for example, gradients running along different anatomical axes), which a single tissue-wide topography cannot represent. This motivates domain-specific isodepths.

## Sources

- U. Chitra, S. Dan, F. Krienen, B. J. Raphael, "GASTON-Mix: a unified model of spatial gradients and domains using spatial mixture-of-experts", Bioinformatics (2025), Section 2.1 (Eqs. 1-2), Section 2.2 (Eq. 3, Theorem 1), Section 2.3 (Eqs. 4-8, domain-specific spatial topography problem), Section 2.4 (spatial mixture-of-experts, Eq. 9). <https://doi.org/10.1093/bioinformatics/btaf254> (PMC12261403)
