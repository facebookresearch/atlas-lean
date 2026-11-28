# Projected subgradient descent for tropical principal polytopes

**Tree space.** Ultrametric trees on $m$ leaves are encoded by their distance vectors in $\mathbb{R}^e/\mathbb{R}\mathbf{1}$, $e = \binom{m}{2}$. A tree metric $D$ of a tree $T$ is an ultrametric iff $T$ is equidistant, and then $T$ is recoverable from $D$; the image of the space $\mathcal{U}_m$ of ultrametrics in $\mathbb{R}^e/\mathbb{R}\mathbf{1}$ is the tropical linear space $\operatorname{Trop}(L_m)$, and is generated in max-plus algebra by the extreme clade ultrametrics. The tropical metric is

$$d_{\mathrm{tr}}(x,y) = \max_i(x_i - y_i) - \min_i(x_i - y_i).$$

**Tropical projection.** For a tropical polytope $\mathcal{P} = \operatorname{tconv}(D^{(1)},\dots,D^{(s)})$,

$$\pi_{\mathcal{P}}(x) = \bigoplus_{l=1}^s \lambda_l \odot D^{(l)}, \qquad \lambda_l = \min_i\bigl(x_i - D^{(l)}_i\bigr),$$

with $\oplus = \max$ and $\odot = +$, is a nearest point of $\mathcal{P}$ to $x$ in $d_{\mathrm{tr}}$. The projection $\pi_{\mathcal{U}_m}$ onto ultrametrics is also a nearest-point map, $d_{\mathrm{tr}}(x,\pi_{\mathcal{U}_m}(x)) \le d_{\mathrm{tr}}(x,y)$ for all $y \in \mathcal{U}_m$, and it is non-expansive: $d_{\mathrm{tr}}(\pi_{\mathcal{U}_m}(u),\pi_{\mathcal{U}_m}(v)) \le d_{\mathrm{tr}}(u,v)$.

**Tropical PCA.** Given gene trees $u_1,\dots,u_n \in \mathcal{U}_m$, the $(s-1)$-th order tropical principal polytope minimizes

$$\sum_{i=1}^n d_{\mathrm{tr}}\bigl(u_i, \pi_{\mathcal{P}}(u_i)\bigr) \quad \text{over } D^{(1)},\dots,D^{(s)} \in \mathcal{U}_m .$$

**Theorem.** A subgradient of this objective over $\mathcal{U}_m$ with respect to vertex $D^{(k)}$ is the projection onto the extreme clade ultrametrics of the coordinatewise subgradients $\sum_i \partial d_{\mathrm{tr}}(u_i,w_i)/\partial D^{(k)}(l)$, $w_i = \pi_{\mathcal{P}}(u_i)$; iterating subgradient steps followed by $\pi_{\mathcal{U}_m}$ gives a projected descent method whose iterates stay in tree space.

## Expansion

The objective is piecewise linear: each $d_{\mathrm{tr}}(u_i, w_i)$ is a difference of a max and a min of affine functions of the vertex coordinates, so subgradients are $\pm1$ indicators at the arg-max and arg-min coordinates, routed through whichever vertex attains $\lambda_l$. A plain step leaves tree space, and non-expansiveness of the ultrametric projection guarantees that projecting back does not increase distances, which keeps the method stable. The source applies the method to an apicomplexa gene-tree dataset.

## Sources

- R. Yoshida, "Projected Gradient Descent Method for Tropical Principal Component Analysis over Tree Space", *Mathematics* 13(11) (2025), 1776, Theorem 10 (cited), Theorem 11 (cited), Propositions 15, 17-18 (cited) and Theorem 20, <https://doi.org/10.3390/math13111776> (preprint arXiv:2504.11201).
