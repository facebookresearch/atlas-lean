# Wright's hierarchical F-statistics identity

Let $H_I$, $H_S$ and $H_T$ be real numbers, read as heterozygosities (probabilities of non-identity) of
two gene copies taken within an individual, within a subpopulation, and in the total population, with
$H_S \ne 0$ and $H_T \ne 0$. Define

$$F_{IS} = 1 - \frac{H_I}{H_S}, \qquad F_{ST} = 1 - \frac{H_S}{H_T}, \qquad F_{IT} = 1 - \frac{H_I}{H_T} .$$

Then

$$1 - F_{IT} = (1 - F_{IS})(1 - F_{ST}).$$

The identity is the factorization $H_I/H_T = (H_I/H_S)(H_S/H_T)$. In Wright's interpretation the three
indices are inbreeding coefficients of individuals relative to their subpopulation, of subpopulations
relative to the total population, and of individuals relative to the total population. The identity is
an algebraic relation between the ratios and does not require a probabilistic sampling model. For
subpopulation allele frequencies, the
[Wahlund identity](../patterson-s-f-statistics/wahlund.md) gives $H_T - H_S$ as twice the variance of the
allele frequencies among subpopulations.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (GENOME 562 course text, University of Washington, version of December 2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section VI.9 "Hierarchical population structure", equations (VI-58), (VI-59), and (VI-61), pp. 275–276.
