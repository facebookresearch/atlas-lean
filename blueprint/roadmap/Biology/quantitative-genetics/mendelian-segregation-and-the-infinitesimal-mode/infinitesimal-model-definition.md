# The infinitesimal model of inheritance

In the **infinitesimal model** with base additive variance $V_0$, an offspring of parents with additive genetic values $g_1$ and $g_2$
and inbreeding coefficients $F_1$ and $F_2$ has additive genetic value

$$g = \frac{g_1 + g_2}{2} + R, \qquad R \sim \mathcal N\Bigl(0,\ \frac{V_0}{2}\Bigl(1 - \frac{F_1 + F_2}{2}\Bigr)\Bigr),$$

with the segregation deviation $R$ independent of the parental values and of everything in earlier generations, and the
deviations of different offspring independent given the pedigree. The within-family variance depends only on the
pedigree, not on the parents' trait values; for non-inbred parents it is $V_0/2$. So selection on the parents changes the
distribution of offspring only through the mean of the parental values, consistent with the
[parent–offspring covariance](../fisher-s-decomposition-of-genetic-variance/cov-parent-offspring-eq.md) of half the additive variance. The model arises as a
[limit of many additive loci](infinitesimal-model-as-a-limit-of-many-loci.md).

## Depends on

- [Parent–offspring covariance is half the additive variance](../fisher-s-decomposition-of-genetic-variance/cov-parent-offspring-eq.md)
- [The infinitesimal model as a limit of many loci](infinitesimal-model-as-a-limit-of-many-loci.md)

## Sources

- N. H. Barton, A. M. Etheridge and A. Véber, "The infinitesimal model: definition, derivation, and implications", Theoretical Population Biology 118 (2017), 50–73, <https://doi.org/10.1016/j.tpb.2017.06.001> (the model and its derivation).
- N. H. Barton, A. M. Etheridge and A. Véber, "The infinitesimal model with dominance", Genetics 225 (2023), preprint <https://arxiv.org/abs/2211.03515>, Introduction and Remark 3.2 (in the purely additive case the segregation residual has variance $\bigl(1 - \frac{F_{11} + F_{22}}{2}\bigr)\frac{\sigma_A^2}{2}$, with $F_{11}$ and $F_{22}$ the identity of the two genes within each parent, as shown in the 2017 paper).
