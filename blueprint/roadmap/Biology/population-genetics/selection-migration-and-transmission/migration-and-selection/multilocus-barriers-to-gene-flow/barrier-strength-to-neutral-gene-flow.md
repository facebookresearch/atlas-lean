# Barrier strength to neutral gene flow

In the setting of an [introgressing multilocus deleterious block](introgression-of-a-multilocus-deleterious-block.md), place a neutral marker, fixed in the donor and absent from the recipient, at one end of the block (the "rod" configuration), at map distance $\alpha c$ from the nearest selected locus, where $c$ is the map distance between adjacent selected loci. Let $m$ be the raw migration rate and $m_e = \delta u(0)/\Delta u$ the effective migration rate, where $\delta u(0)$ is the rate of increase of the marker on the recipient background and $\Delta u = 1$ the allele-frequency difference between species. The *barrier strength* is $b = m/m_e$.

**Theorem.** For $sL, cL \ll 1$, rare introgression, and coupling $\theta = s/c$,

$$b = \frac{\Gamma\Bigl(L + \frac{\alpha + \theta}{1 + \theta}\Bigr)\,\Gamma\Bigl(\frac{\alpha}{1 + \theta}\Bigr)}{\Gamma\Bigl(L + \frac{\alpha}{1 + \theta}\Bigr)\,\Gamma\Bigl(\frac{\alpha + \theta}{1 + \theta}\Bigr)}.$$

The same formula holds for autosomal markers with $\theta = \theta_A = s_A/c_A$ and for X-linked markers with $\theta = \theta_X = s_X/c_X$, using the sex-averaged parameters of the block model.

**Properties.** $b = 1$ when $\theta = 0$ (no selection); for $L = 1$, $b = 1 + \theta/\alpha$, the classical single-locus barrier $1 + s/(\alpha c)$; $b$ increases with $\theta$ and decreases with $\alpha$. Since $\theta_X = \frac32 \theta_A$ for identical architectures without sex bias, the X chromosome presents the stronger barrier.

## Depends on

- [Introgression of a multilocus deleterious block](introgression-of-a-multilocus-deleterious-block.md)

## Expansion

For $L = 1$, using $\Gamma(z + 1) = z\Gamma(z)$: $b = \frac{(\alpha + \theta)/(1 + \theta)}{\alpha/(1 + \theta)} = 1 + \theta/\alpha$. In general $b = \prod_{j=0}^{L-1} \frac{j + (\alpha + \theta)/(1+\theta)}{j + \alpha/(1+\theta)}$, a product of factors greater than $1$ when $\theta > 0$. The formula is derived by tracking the rate at which the marker moves from backgrounds with $y$ deleterious alleles to $y - 1$, ending on a clean recipient background, which in the rod model happens in single recombination steps (Barton and Bengtsson 1986).

## Sources

- C. Fraïsse and H. Sachdeva, *The rates of introgression and barriers to genetic exchange between hybridizing species: sex chromosomes vs autosomes*, Genetics 217 (2021), iyaa025, <https://doi.org/10.1093/genetics/iyaa025>, PMCID PMC8045713 (equations (5) and (6)).
- N. H. Barton and B. O. Bengtsson, *The barrier to genetic exchange between hybridising populations*, Heredity 57 (1986), 357–376.
