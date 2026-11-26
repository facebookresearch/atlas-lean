# Conditional mutual inclusive information and its decomposition

Let $X, Y$ be scalar random variables (expression levels of two genes) and $Z$ a random vector (expression of $d \ge 1$ other genes) with joint density $p(x, y, z) > 0$. Write $\mathrm{CMI}(X; Y \mid Z) = \mathbb{E} \log \frac{p(X, Y \mid Z)}{p(X \mid Z)\, p(Y \mid Z)}$ for conditional mutual information.

**Edge-deletion distributions.** In a graph where $Y$ is regulated by $X$ directly and through $Z$, deleting the edge $X \to Y$ while keeping everything else replaces $X$ in the mechanism of $Y$ by an independent copy $X'$ drawn from its marginal:

$$p_{X \to Y}(x, y, z) = p(x, z) \int p(y \mid x', z)\, p(x')\, dx' .$$

The distribution $p_{Y \to X}$ is defined symmetrically.

**Definition.** The conditional mutual inclusive information is

$$\mathrm{CMI2}(X; Y \mid Z) = \tfrac12 \Bigl( D_{\mathrm{KL}}(p \,\|\, p_{X \to Y}) + D_{\mathrm{KL}}(p \,\|\, p_{Y \to X}) \Bigr),$$

and its order is the dimension $d$ of $Z$; with $Z$ absent it reduces to mutual information.

**Decomposition.** With $q(y \mid z) := \int p(y \mid x', z)\, p(x')\, dx'$ and $r(x \mid z) := \int p(x \mid y', z)\, p(y')\, dy'$,

$$\mathrm{CMI2}(X; Y \mid Z) = \mathrm{CMI}(X; Y \mid Z) + \tfrac12\, \mathbb{E}_Z\, D_{\mathrm{KL}}\bigl(p(\cdot \mid Z) \,\|\, q(\cdot \mid Z)\bigr)_Y + \tfrac12\, \mathbb{E}_Z\, D_{\mathrm{KL}}\bigl(p(\cdot \mid Z) \,\|\, r(\cdot \mid Z)\bigr)_X ,$$

where the subscript names the variable of the conditional densities. Consequently:

- $\mathrm{CMI2}(X; Y \mid Z) \ge \mathrm{CMI}(X; Y \mid Z) \ge 0$;
- if $X \perp Z$ and $Y \perp Z$ then $q(y \mid z) = p(y \mid z)$ and $r(x \mid z) = p(x \mid z)$, so $\mathrm{CMI2} = \mathrm{CMI}$;
- when $Z$ is nearly a copy of $X$, $\mathrm{CMI}(X; Y \mid Z) \approx 0$ even for a direct regulation $X \to Y$, while the correction terms stay positive, which is the false-negative case the measure is designed to repair.

## Expansion

Since $p(x, y, z) / p_{X \to Y}(x, y, z) = p(y \mid x, z) / q(y \mid z)$,

$$D_{\mathrm{KL}}(p \,\|\, p_{X \to Y}) = \mathbb{E} \log \frac{p(Y \mid X, Z)}{p(Y \mid Z)} + \mathbb{E} \log \frac{p(Y \mid Z)}{q(Y \mid Z)} = \mathrm{CMI}(X; Y \mid Z) + \mathbb{E}_Z D_{\mathrm{KL}}\bigl(p(\cdot \mid Z) \,\|\, q(\cdot \mid Z)\bigr),$$

and averaging with the symmetric identity for $p_{Y \to X}$ gives the decomposition; non-negativity of each divergence gives the inequality. Under a joint Gaussian model for log expression the divergences have closed forms in the covariance blocks of $(X, Y, Z)$ (the paper's Theorem 1), so CMI2 can replace CMI as the edge statistic in a path-consistency algorithm: starting from the complete graph, an edge is removed when its order-$L$ CMI2 falls below a threshold for some conditioning set of $L$ current neighbours, with $L$ increased until the graph stops changing.

## Sources

- X. Zhang, J. Zhao, J.-K. Hao, X.-M. Zhao, L. Chen, "Conditional mutual inclusive information enables accurate quantification of associations in gene regulatory networks", Nucleic Acids Research 43 (2015) e31, Materials and Methods, Equations (5)–(10) and Theorem 1, <https://doi.org/10.1093/nar/gku1315> (PMC4357691).
