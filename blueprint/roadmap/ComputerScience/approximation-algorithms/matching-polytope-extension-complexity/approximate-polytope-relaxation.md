# Multiplicatively approximate relaxations of the matching polytope

Let $P_{\mathrm{M}}(n) \subseteq \mathbb{R}_{\ge 0}^{E}$ be the matching polytope of $K_n=(V,E)$ and $\varepsilon \ge 0$. A polytope $K$ is a $(1+\varepsilon)$-approximate relaxation of $P_{\mathrm{M}}(n)$ if

$$
P_{\mathrm{M}}(n) \subseteq K \subseteq (1+\varepsilon)\,P_{\mathrm{M}}(n).
$$

Then for every weight vector $w \in \mathbb{R}_{\ge 0}^{E}$, $\max_{x \in P_{\mathrm{M}}(n)}w^{\top}x \le \max_{x \in K}w^{\top}x \le (1+\varepsilon)\max_{x \in P_{\mathrm{M}}(n)}w^{\top}x$, so solving a linear program over $K$ approximates maximum-weight matching within a factor $1+\varepsilon$. A family with $\mathrm{xc}(K) \le \mathrm{poly}(n,1/\varepsilon)$ for all $\varepsilon$ would be a fully-polynomial size relaxation scheme.

## Depends on

- [Matching polytope](../../../GraphTheory/matchings-and-flows/matching-polytope/matching-polytope.md)
- [Linear extensions of a polytope and their inequality count](linear-extension-size.md)

## Sources

- Gabor Braun, Sebastian Pokutta, "The Matching Polytope Does Not Admit Fully-Polynomial Size Relaxation Schemes", SODA (2015) and IEEE Transactions on Information Theory (2015), arXiv:1403.6710.
- Makrand Sinha, "Lower Bounds for Approximating the Matching Polytope", SODA (2018), ECCC TR17-185.
