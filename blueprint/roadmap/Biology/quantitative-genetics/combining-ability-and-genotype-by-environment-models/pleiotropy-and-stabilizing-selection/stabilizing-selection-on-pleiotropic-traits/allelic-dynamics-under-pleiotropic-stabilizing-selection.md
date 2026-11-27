# Allelic dynamics under pleiotropic stabilizing selection

Consider a diploid, panmictic Wright–Fisher population of constant size $N$ with free recombination, in which an individual's phenotype $\vec r\in\mathbb R^n$ is the sum of the effects of its alleles over $L\gg1$ sites, $\vec r=\sum_{l=1}^L(\vec a_l+\vec a_l')$, and absolute fitness is

$$W(\vec r)=\exp\!\Big(-\frac{\|\vec r\|^2}{2w^2}\Big),$$

with the optimum at the origin. Assume at most two alleles per site ($\theta=4Nu\ll1$), a per-gamete mutation rate $U=Lu$ with $1\gg U\gg 1/(2N)$, and mutation sizes $a=\|\vec a\|$ with $a^2\ll w^2$. Then at equilibrium the phenotype distribution is approximately $\mathcal N(0,\sigma^2 I_n)$ with $\sigma^2\ll w^2$, and an allele of effect $\vec a$ at frequency $q=1-p$ changes in one generation with

$$\mathbb E(\Delta q)\approx\frac{a^2}{w^2}\,pq\Big(q-\frac12\Big),\qquad \operatorname{Var}(\Delta q)\approx\frac{pq}{2N}.$$

These are the moments of viability selection with underdominance and selection coefficient

$$s=\frac{a^2}{w^2}=\frac1{w^2}\sum_{i=1}^n a_i^2,\qquad S=2Ns,$$

so selection on an allele is proportional to the squared length of its effect in trait space, and acts to remove the allele's contribution $2a^2pq$ to the phenotypic variance by pushing rare alleles to loss.

## Proof sketch

The background contribution $\vec R$ from all other sites is Gaussian, centred at $-2q\vec a$ so that the population mean sits at the optimum. Averaging the fitnesses of the three genotypes at the focal site over this background and expanding to first order in $a^2/w^2$ and $\sigma^2/w^2$ gives the first moment; drift supplies the second. With the mean at the optimum, sites decouple, and only the curvature of the fitness surface at the optimum matters, so the result does not depend on the Gaussian form of $W$. Pleiotropy enters only through the geometry: all mutations with the same $s$ lie on a sphere of radius $w\sqrt s$.

## Sources

- Y. B. Simons, K. Bullaughey, R. R. Hudson, G. Sella, "A population genetic interpretation of GWAS findings for human quantitative traits", PLoS Biol. 16 (2018) e2002985, sections "The model", "The phenotypic distribution" and "Allelic dynamic", Equations (1)–(7), <https://doi.org/10.1371/journal.pbio.2002985>, PMCID PMC5871013.
