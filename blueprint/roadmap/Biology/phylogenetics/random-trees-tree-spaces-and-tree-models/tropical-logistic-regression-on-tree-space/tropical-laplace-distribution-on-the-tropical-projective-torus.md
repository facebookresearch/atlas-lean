# Tropical Laplace distribution on the tropical projective torus

Equidistant (ultrametric) trees on $m$ leaves are encoded by their vectorised pairwise distances in $\mathbb{R}^e$, $e = \binom{m}{2}$, and viewed in the **tropical projective torus** $\mathbb{R}^e/\mathbb{R}\mathbf{1}$, where the space of ultrametrics is a tropical linear space. The **tropical metric** (generalised Hilbert projective metric) is

$$d_{\mathrm{tr}}(v, w) = \max_i (v_i - w_i) - \min_i (v_i - w_i),$$

a well-defined metric on $\mathbb{R}^e/\mathbb{R}\mathbf{1}$. On two trees it measures the spread of the differences in pairwise divergences. The law below is an **ambient** law: its density is taken with respect to Lebesgue measure on the whole torus $\mathbb{R}^e/\mathbb{R}\mathbf{1} \cong \mathbb{R}^{e-1}$, in which the ultrametrics form a lower-dimensional, Lebesgue-null subset, so trees are points at which the density is evaluated, not its support.

**Proposition (normalising constant).** The tropical Laplace density with centre $\omega$ and scale $\sigma > 0$,

$$f(x) = \frac{1}{\Lambda}\exp\!\Big(-\frac{d_{\mathrm{tr}}(x, \omega)}{\sigma}\Big), \qquad x \in \mathbb{R}^e/\mathbb{R}\mathbf{1},$$

has $\Lambda = \int_{\mathbb{R}^e/\mathbb{R}\mathbf{1}} \exp(-d_{\mathrm{tr}}(x, \omega)/\sigma)\,dx = e!\,\sigma^{e-1}$, the integral being over the whole torus.

**Proposition (distance law).** Let $d$ be positively homogeneous on $\mathbb{R}^n$ ($d(\alpha x) = \alpha d(x)$ for $\alpha \ge 0$), and let $X$ have density proportional to $\exp\!\big(-d(x)^i/(i\sigma^i)\big)$ for some $i \in \mathbb{N}$. Then $d(X)^i \sim i\sigma^i\,\mathrm{Gamma}(n/i)$. Consequently, under the tropical Laplace ($i = 1$) or tropical normal ($i = 2$) law on $\mathbb{R}^e/\mathbb{R}\mathbf{1} \cong \mathbb{R}^{e-1}$, $d_{\mathrm{tr}}(X, \omega)^i \sim i\sigma^i\,\mathrm{Gamma}\big((e-1)/i\big)$, whereas the Euclidean analogues in $\mathbb{R}^e$ give $\mathrm{Gamma}(e/i)$. Neither the normaliser nor the Gamma law transfers to a law on the space of ultrametric trees, which is not translation invariant: for three leaves the torus is two-dimensional while the ultrametrics are three rays from a common origin, along which the integral of $\exp(-d_{\mathrm{tr}}/\sigma)$ scales as $\sigma$ rather than $\sigma^2$. An intrinsic tree-space law needs its own reference measure and normaliser.

## Depends on

- [Ultrametrics are dated tree metrics](../../splits-compatibility-ultrametrics-and-upgma/is-ultrametric-iff-is-dated-tree-metric.md)

## Expansion

The tropical unit ball in $\mathbb{R}^e/\mathbb{R}\mathbf{1}$ has volume $e$, so a ball of radius $r$ has volume $e\,r^{e-1}$ and surface area $e(e-1)r^{e-2}$; integrating $e^{-r}$ against this area gives $e(e-1)\Gamma(e-1) = e!$, and scaling by $\sigma$ contributes $\sigma^{e-1}$. For the distance law, homogeneity gives $C_\alpha = C_1\alpha^{-n}$ for the normaliser at precision $\alpha = 1/\sigma$, and the moment generating function of $d(X)^i$ is then $(1 - i\sigma^i z)^{-n/i}$, the Gamma one. The source notes, before its Proposition 4, that this argument does not apply to distributions on the space of ultrametric trees. Comparing empirical distances of gene trees to the species tree with these ambient Gamma laws is how the source checks that tropical rather than Euclidean noise fits multispecies-coalescent samples.

## Sources

- G. Aliatimis, R. Yoshida, B. Boyacı, J. A. Grant, *Tropical logistic regression model on space of phylogenetic trees*, Bull. Math. Biol. 86 (2024), 99 (Definition 1, Proposition 1, Theorem 5 in Appendix B, Eq. (6), Propositions 3–4, Corollary 1, Appendix A). <https://doi.org/10.1007/s11538-024-01327-8> (PMCID: PMC11219468)
