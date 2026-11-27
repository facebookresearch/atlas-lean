# Between- and within-individual decomposition of multi-context expression

Fix a gene. Let $E_{ic}$ be the expression of individual $i\in\{1,\dots,I\}$ in context $c\in\{1,\dots,C\}$, with every individual measured in every context, and assume each context has been centered and scaled over individuals, $\frac1I\sum_i E_{ic}=0$ and $\frac1I\sum_i E_{ic}^2=1$. Put

$$\bar E_{i\cdot}=\frac1C\sum_{c=1}^C E_{ic},\qquad E^{\mathrm{Shared}}_i=\bar E_{i\cdot},\qquad E^{\mathrm{Specific}}_{ic}=E_{ic}-\bar E_{i\cdot}.$$

Then:

1. **Decomposition.** $E_{ic}=E^{\mathrm{Shared}}_i+E^{\mathrm{Specific}}_{ic}$, the grand mean $\frac{1}{IC}\sum_{i,c}E_{ic}$ being $0$.
2. **Orthogonality.** For each individual $\sum_c E^{\mathrm{Specific}}_{ic}=0$, so in $\mathbb R^{I\times C}$ the shared array $(E^{\mathrm{Shared}}_i)_{i,c}$ and the specific array are orthogonal, and

$$\sum_{i,c}E_{ic}^2=C\sum_i\bigl(E^{\mathrm{Shared}}_i\bigr)^2+\sum_{i,c}\bigl(E^{\mathrm{Specific}}_{ic}\bigr)^2 .$$

3. **Genetic content.** Under the generative model $E_{ic}=g_i^\top\beta+g_i^\top\gamma_c+\varepsilon_{ic}$, with cis-genotypes $g_i$, context-shared effects $\beta$, context-specific effects $\gamma_c$ and noise $\varepsilon_{i\cdot}$ independent of $g_i$,

$$E^{\mathrm{Shared}}_i=g_i^\top(\beta+\bar\gamma)+\bar\varepsilon_{i\cdot},\qquad E^{\mathrm{Specific}}_{ic}=g_i^\top(\gamma_c-\bar\gamma)+(\varepsilon_{ic}-\bar\varepsilon_{i\cdot}),$$

with $\bar\gamma=\frac1C\sum_c\gamma_c$. Only the deviation $\gamma_c-\bar\gamma$ is identified as context specific.
4. **Removal of correlated noise.** If the intra-individual noise is exchangeable, $\operatorname{Var}\varepsilon_{ic}=\sigma^2$ and $\operatorname{Corr}(\varepsilon_{ic},\varepsilon_{ic'})=\rho$ for $c\ne c'$, then

$$\operatorname{Var}\bigl(\varepsilon_{ic}-\bar\varepsilon_{i\cdot}\bigr)=\sigma^2(1-\rho)\Bigl(1-\frac1C\Bigr),$$

so the noise in the specific component falls as the cross-context noise correlation $\rho$ rises.

## Depends on

- [Group mean of observations](../../../../../Probability/linear-models-multivariate/cochran-s-theorem/group-mean.md): the individual mean $\bar E_{i\cdot}$, with individuals as groups

## Expansion

Items 1 and 2 are the one-way analysis-of-variance identity with individuals as groups: the specific deviations sum to zero within each individual, which kills the cross term. Item 3 is linearity of the context average. For item 4, $\operatorname{Var}\bar\varepsilon_{i\cdot}=\operatorname{Cov}(\varepsilon_{ic},\bar\varepsilon_{i\cdot})=\sigma^2[1+(C-1)\rho]/C$, so $\operatorname{Var}(\varepsilon_{ic}-\bar\varepsilon_{i\cdot})=\sigma^2-\sigma^2[1+(C-1)\rho]/C$. This is the mechanism behind the source's remark that the power to detect context specificity increases with the correlation of intra-individual noise. Items 2 to 4 are derived here from the stated definitions. With missing contexts the same construction, averaging over the contexts observed for each individual, keeps the within-individual zero-sum property but the scaling constants change.

The source contrasts this with a per-gene linear mixed model (orthogonal tissue decomposition), whose posterior-mean random intercept plays the role of the shared component; the source states that the two decompositions coincide in the infinite-sample limit.

## Sources

- M. Thompson, M. G. Gordon, A. Lu, A. Tandon, E. Halperin, A. Gusev, C. J. Ye, B. Balliu and N. Zaitlen, "Multi-context genetic modeling of transcriptional regulation resolves novel disease loci", Nature Communications 13 (2022), 5704, Methods ("Decomposing multilevel data", Equations (1) to (5)), <https://doi.org/10.1038/s41467-022-33212-0> (PMC9519579).
