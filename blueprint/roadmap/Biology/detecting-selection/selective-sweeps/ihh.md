# One-sided integrated haplotype homozygosity

For real numbers $r$ and $T$, the one-sided integrated haplotype homozygosity of the star-genealogy model is

$$\mathrm{iHH}(r, T) = \int_0^\infty \mathrm{EHH}^\star(r, T, d) \, dd,$$

where $\mathrm{EHH}^\star$ is the [star-genealogy EHH](sweep-ehh.md), with the convention that the integral of a non-integrable function is $0$. For $r, T > 0$ the integral is finite, equal to $1/(2rT)$, and is the area under the EHH decay curve in one direction from the focal site; when the curve is not integrable, for instance for $r = 0$ where it is constant, the value $0$ is only the convention.
