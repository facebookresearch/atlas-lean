# Effect of polarization error on the site-frequency spectrum

Suppose that at each segregating site the ancestral state, inferred from an outgroup, is wrong independently with probability $\varepsilon$, so that a site with $i$ derived copies among $n$ is recorded with $n - i$, and let $\xi_i$ and $\xi^{\mathrm{obs}}_i$ be the true and the recorded unfolded spectra. By linearity of expectation,

$$E\bigl[\xi^{\mathrm{obs}}_i\bigr] = (1 - \varepsilon)\,E[\xi_i] + \varepsilon\,E[\xi_{n-i}], \qquad 1 \le i \le n - 1,$$

while the folded spectrum, $\eta_i = \xi_i + \xi_{n-i}$ for $1 \le i < n/2$ and $\eta_{n/2} = \xi_{n/2}$ for even $n$, which counts the sites at frequencies $i/n$ and $1 - i/n$ together and needs no outgroup (Achaz 2009, Model), is unchanged, the class $i = n/2$ being mapped to itself. Under Kingman's coalescent, where $E[\xi_i] = \theta/i$, this gives $E[\xi^{\mathrm{obs}}_i] = \theta\bigl((1 - \varepsilon)/i + \varepsilon/(n - i)\bigr)$, which for $\varepsilon > 0$ raises the classes $i > n/2$, so that for $\varepsilon > 0$ and $n \ge 3$ statistics weighting high-frequency derived variants, such as Fay and Wu's $H$, acquire a nonzero mean under neutrality (for $n = 2$ the only class $i = 1$ is its own mirror image and nothing changes). This is a direct derivation; Baudry and Depaulis (2003, Abstract) report that empirically derived misorientation rates strongly affect Fay and Wu's $H$, especially for large samples, and Gutenkunst, Hernandez, Williamson and Bustamante (2009, Results) correct observed unfolded spectra for ancestral misidentification before inference.

## Depends on

- [Expected site frequency spectrum](../../expected-site-frequency-spectrum/integral-sfs.md)
- [Folded site frequency spectrum](../../expected-site-frequency-spectrum/folded-count.md)
- [Fay and Wu's H statistic](../../site-frequency-spectrum-under-variable-populatio/fay-wu-h.md)
- [Fay and Wu's H has mean zero at constant size](../../site-frequency-spectrum-under-variable-populatio/integral-fay-wu-h.md)

## Expansion

1. The independent misorientation model with error probability $\varepsilon$.
2. The expected recorded spectrum by linearity, and the invariance of the folded spectrum, with the midpoint class.
3. The neutral expectation $\theta((1 - \varepsilon)/i + \varepsilon/(n - i))$ and the mean of Fay and Wu's $H$ and other weighted statistics under misorientation.
4. Correction by estimating $\varepsilon$ or by context-dependent substitution models, as a separate statement.

## Sources

- G. Achaz, Frequency spectrum neutrality tests: one for all and all for one, Genetics 183 (2009), 249–258, Model. <https://doi.org/10.1534/genetics.109.104042>
- E. Baudry and F. Depaulis, Effect of misoriented sites on neutrality tests with outgroup, Genetics 165 (2003), 1619–1622, Abstract. <https://doi.org/10.1093/genetics/165.3.1619>
- R. N. Gutenkunst, R. D. Hernandez, S. H. Williamson and C. D. Bustamante, Inferring the joint demographic history of multiple populations from multidimensional SNP frequency data, PLoS Genet. 5 (2009), e1000695, Results. <https://doi.org/10.1371/journal.pgen.1000695>
