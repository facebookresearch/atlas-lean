# Effect sizes given selection in Fisher's geometric model

In the model of [allelic dynamics under pleiotropic stabilizing selection](allelic-dynamics-under-pleiotropic-stabilizing-selection.md), let mutation directions be isotropic, so that a mutation with selection coefficient $s$ is uniform on the sphere of radius $a=w\sqrt s$ in $\mathbb R^n$, and let $a_1$ be its effect on a focal trait. Then $\mathbb E(a_1\mid s)=0$,

$$\mathbb E(a_1^2\mid s)=\frac{a^2}{n}=\frac{w^2}{n}\,s,$$

for $n=1$, $a_1=\pm a$ with probability $\tfrac12$ each, and for $n>1$ the density of $a_1$ is

$$\varphi_n(a_1\mid a)=\frac{\Gamma(n/2)}{\Gamma((n-1)/2)\sqrt{n\pi}}\,\frac{1}{\sqrt{a^2/n}}\Big(1-\frac1n\,\frac{a_1^2}{a^2/n}\Big)^{\frac{n-3}{2}},\qquad |a_1|<a.$$

As $n\to\infty$, $a_1/\sqrt{a^2/n}\to\mathcal N(0,1)$ in distribution, so for highly pleiotropic mutations

$$a_1\mid s\;\approx\;\mathcal N\!\Big(0,\frac{w^2}{n}\,s\Big),$$

already a good approximation for $n\approx10$. These statements are for isotropic mutation directions; the scale $w^2 s/n$ uses the ordinary trait count $n$ and is not claimed here for anisotropic models.

## Remarks

Simons et al. (after their Equation 11) extend the normal approximation to anisotropic mutation and selection, with $n$ replaced by an effective number of traits defined for the focal coordinate and with pathological cases excluded; that extension has a different scale from the isotropic $w^2 s/n$ and is not part of the statement above.

## Proof sketch

The density of a coordinate of a uniform point on the sphere $S^{n-1}$ of radius $a$ is proportional to $(1-a_1^2/a^2)^{(n-3)/2}$, the volume of the $(n-2)$-dimensional cross-section; normalising gives $\varphi_n$. Writing $a_1^2/a^2=x^2/n$ and using $(1-x^2/n)^{(n-3)/2}\to e^{-x^2/2}$ gives the Gaussian limit (Poincaré's observation). Symmetry among coordinates gives the second moment. The consequence for association studies is that, given its selection coefficient, an allele's effect on any one trait is random and typically much smaller than its total effect, so strongly selected alleles need not have large effects on the trait under study.

## Depends on

- [Allelic dynamics under pleiotropic stabilizing selection](allelic-dynamics-under-pleiotropic-stabilizing-selection.md)

## Sources

- Y. B. Simons, K. Bullaughey, R. R. Hudson, G. Sella, "A population genetic interpretation of GWAS findings for human quantitative traits", PLoS Biol. 16 (2018) e2002985, section "The relationship between selection and effect size", Equations (7)–(11), <https://doi.org/10.1371/journal.pbio.2002985>, PMCID PMC5871013.
