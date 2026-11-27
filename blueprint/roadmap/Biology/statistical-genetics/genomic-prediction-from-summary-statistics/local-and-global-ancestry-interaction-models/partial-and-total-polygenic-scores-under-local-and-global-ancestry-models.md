# Partial and total polygenic scores under local and global ancestry models

**Setting.** In a two-way admixed cohort (African and European ancestry), individual $i$ carries phased haplotypes $h=1,2$ at causal variants $j=1,\dots,p$ with local ancestry indicators $a_{ij}^{(h)}\in\{0,1\}$ ($1$ = African) and global African ancestry $\bar a_{i\cdot}$. Haplotype dosages are demeaned with the allele frequency of their local ancestry, $\hat x_{ij}^{(h)}=x_{ij}^{(h)}-f_j^{\mathrm{Afr}}a_{ij}^{(h)}-f_j^{\mathrm{Eur}}(1-a_{ij}^{(h)})$. Ancestry-specific effects are jointly Gaussian,

$$\begin{pmatrix}\beta_j^{\mathrm{Eur}}\\ \beta_j^{\mathrm{Afr}}\end{pmatrix}\sim\mathcal N\!\left(0,\begin{pmatrix}\sigma_{\mathrm{Eur}}^2&\tau\\ \tau&\sigma_{\mathrm{Afr}}^2\end{pmatrix}\right),\quad
\sigma_{\mathrm{A}}^2=\frac{r^2}{2\sum_j f_j^{\mathrm A}(1-f_j^{\mathrm A})},\quad
\tau=\rho\,\sigma_{\mathrm{Eur}}\sigma_{\mathrm{Afr}},$$

so $r^2$ is the variance explained and $\rho$ the cross-ancestry effect correlation. The phenotype is $y_i=\sum_{j,h}\beta_{ij}^{(h)}\hat x_{ij}^{(h)}+\varepsilon_i$ with either

- the **local model** $\beta_{ij}^{(h)}=\beta_j^{\mathrm{Eur}}(1-a_{ij}^{(h)})+\beta_j^{\mathrm{Afr}}a_{ij}^{(h)}$ (cis interactions), or
- the **global model** $\beta_{ij}^{(h)}=\beta_j^{\mathrm{Eur}}(1-\bar a_{i\cdot})+\beta_j^{\mathrm{Afr}}\bar a_{i\cdot}$ (diffuse trans interactions).

The total score uses European effects on every allele, $\mathrm{TotPGS}_i=\sum_j\beta_j^{\mathrm{Eur}}(\hat x_{ij}^{(1)}+\hat x_{ij}^{(2)})$; the partial score uses only European-ancestry alleles, $\mathrm{ParPGS}_i=\sum_j\beta_j^{\mathrm{Eur}}\sum_h(1-a_{ij}^{(h)})\hat x_{ij}^{(h)}$.

**Proposition 2.** Let $\bar a$ be the cohort mean African global ancestry. Assume (A) ancestry-specific allele frequencies are equal across markers, (B) local ancestry is identically distributed across individuals, (C) both haplotypes of an individual share ancestry assignment, (D) ancestry-specific allele-frequency differences are small, and (E) alleles on the two haplotypes are approximately uncorrelated. Then

$$\mathbb E_{\mathrm{Glo}}[\mathrm{Cor}^2(\mathrm{TotPGS},y)]\approx r^2(1-\bar a+\rho\bar a)^2\approx\mathbb E_{\mathrm{Loc}}[\mathrm{Cor}^2(\mathrm{TotPGS},y)],$$

$$\mathbb E_{\mathrm{Glo}}[\mathrm{Cor}^2(\mathrm{ParPGS},y)]\approx r^2(1-\bar a)(1-\bar a+\rho\bar a)^2,\qquad
\mathbb E_{\mathrm{Loc}}[\mathrm{Cor}^2(\mathrm{ParPGS},y)]\approx r^2(1-\bar a).$$

With causal variants known, the partial score thus separates the two models (cubic versus linear dependence on $\bar a$), while the total score does not.

**Proposition 1 (local-ancestry average effects).** Under the local model the average causal effects by local ancestry have the joint law of $(\beta_j^{\mathrm{Afr}},\beta_j^{\mathrm{Eur}})$, so their correlation is $\rho$. Under the global model they are jointly Gaussian with a covariance that is a quadratic form in the effect covariance with weights determined by the haplotype and local-ancestry matrices; empirically their correlation exceeds $0.98$ even for $\rho=0.2$, so near-identical average effects across local ancestries do not rule out gene-ancestry interactions.

## Expansion

Under the local model a European-ancestry allele carries exactly $\beta^{\mathrm{Eur}}$, so the partial score captures a fraction $1-\bar a$ of the genetic variance with no loss of correlation. Under the global model every allele, including European-ancestry ones, carries the blended effect $(1-\bar a)\beta^{\mathrm{Eur}}+\bar a\beta^{\mathrm{Afr}}$, whose correlation with $\beta^{\mathrm{Eur}}$ contributes the extra factor $(1-\bar a+\rho\bar a)^2$ after normalizing variances under (A)-(E). For the total score both models assign African-ancestry alleles effects with correlation $\rho$ to $\beta^{\mathrm{Eur}}$ on average, giving the same leading term. With only tagging variants, ancestry-specific LD rescales effects by ancestry and confounds this contrast.

## Sources

- Aw AJ, Mandla R, Shi Z, Pasaniuc B, Mathieson I, "Hidden structure in polygenic scores and the challenge of disentangling ancestry interactions in admixed populations", Genetics 2025 Oct 4;231(4):iyaf213, Equations (1)-(7), (12)-(13) and Propositions 1-2, <https://doi.org/10.1093/genetics/iyaf213>, PMCID PMC12693580.
