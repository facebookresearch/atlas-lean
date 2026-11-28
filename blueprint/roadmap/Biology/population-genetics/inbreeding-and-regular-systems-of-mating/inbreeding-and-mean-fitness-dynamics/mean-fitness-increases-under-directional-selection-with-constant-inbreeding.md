# Mean fitness increases under directional selection with constant inbreeding

At a biallelic locus with allele frequency $x$ of $A$, let genotype frequencies be $x^2 + fx(1-x)$, $2x(1-x)(1-f)$ and $(1-x)^2 + fx(1-x)$ for $AA$, $Aa$, $aa$, with constant inbreeding coefficient $f \in [0, 1]$, and let the genotypes have fitnesses $w_{11}, w_{12}, w_{22} > 0$. The mean fitness is

$$\bar w = w_{11}x^2 + 2w_{12}x(1-x) + w_{22}(1-x)^2 + fx(1-x)(w_{11} + w_{22} - 2w_{12}),$$

and with $J = (1-f)(w_{11} + w_{22} - 2w_{12})x + f(w_{11} - w_{12}) + w_{12} - w_{22}$ one generation of selection gives $\Delta x = x(1-x)J/\bar w$ and

$$\Delta\bar w = \frac{x(1-x)J^2}{\bar w^2}\Bigl(w_{11}x + w_{22}(1-x) + \bar w\Bigl(1 - \frac{f(w_{11} - w_{22})}{J}\Bigr)\Bigr) \qquad (J \ne 0).$$

In particular $\Delta\bar w \ge 0$ whenever $f(w_{11} - w_{22})/J \le 1$, which covers random mating ($f = 0$) and symmetric homozygotes ($w_{11} = w_{22}$). For directional selection with fitnesses $w_{11} = 1$, $w_{12} = 1 + hs$, $w_{22} = 1 + s$ and $0 \le h, s \le 1$, the mean fitness increases monotonically from every initial frequency, for every $f \in [0, 1]$. With overdominance it can instead decrease for part of the trajectory, as in the fitnesses $(1, 1.4, 0.8)$ with $f = 0.25$.

## Depends on

- [Viability selection in an inbred population](../selection-under-inbreeding.md)
- [Mean fitness is linear in the inbreeding coefficient](../mean-fitness-under-inbreeding.md)

## Expansion

The recursion for $\Delta x$ is viability selection on Wright's inbred genotype frequencies, and expanding $\bar w(x + \Delta x) - \bar w(x)$ gives the displayed product form. For the directional fitnesses $J = -s\,B$ and $w_{11} - w_{22} = -s$ with $B = (1-f)(2h-1)x + fh + 1 - h$, so the sufficient condition is $f/B \le 1$; for $h \ge 1/2$ this follows from $fh + 1 - h \ge f$, and for $h < 1/2$ from rewriting $B = (1-f)(1-2h)(1-x) + f + h(1-f) \ge f$. Inbreeding thus slows but does not reverse adaptation under directional selection, consistent with the persistence of self-fertilizing plants.

## Sources

- S. Sun, F. Klebaner and T. Tian, "Mathematical modelling for variations of inbreeding populations fitness with single and polygenic traits", BMC Genomics 18 (Suppl. 2) (2017) 196, <https://doi.org/10.1186/s12864-017-3492-1>, PMCID PMC5374587. Equations (1)–(2) and Theorem 1.
