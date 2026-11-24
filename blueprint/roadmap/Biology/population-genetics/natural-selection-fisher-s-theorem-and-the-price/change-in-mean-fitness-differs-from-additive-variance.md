# An example where the change in mean fitness differs from the additive variance

The following direct calculation illustrates that the change in mean fitness is not $V_A / \bar w$ in
general. For one diploid locus with alleles $A$ and $a$, let the genotypes $AA$, $Aa$, $aa$ have fitnesses
$w_{AA} = w_{Aa} = 1$ and $w_{aa} = 0$, and let the frequency of $A$ be $p = 1/2$. Then the
[mean fitness](diploid-mean-fitness.md) is $\bar w(p) = 3/4$, one generation of
[viability selection](diploid-select.md) gives $p' = 2/3$, and $\bar w(p') = 8/9$, so

$$\bar w(p') - \bar w(p) = \frac{5}{36} .$$

With fitness as the genotypic value, the
[average effects](../../quantitative-genetics/fisher-s-decomposition-of-genetic-variance/avg-effect.md) are
$\alpha_A = 1/4$ and $\alpha_a = -1/4$, the
[additive genetic variance](../../quantitative-genetics/fisher-s-decomposition-of-genetic-variance/add-var.md)
in fitness is $V_A = 2(p\,\alpha_A^2 + (1 - p)\,\alpha_a^2) = 1/8$, and

$$\frac{V_A}{\bar w(p)} = \frac{1}{6} = \frac{6}{36} \ne \frac{5}{36} .$$

So the one-generation change in mean fitness under diploid viability selection is not equal to
$V_A / \bar w$ in general; here the difference $-1/36$ comes from dominance in fitness.

## Depends on

- [Diploid mean fitness under Hardy–Weinberg proportions](diploid-mean-fitness.md)
- [One generation of diploid viability selection](diploid-select.md)
- [Average effect of an allele](../../quantitative-genetics/fisher-s-decomposition-of-genetic-variance/avg-effect.md)
- [Additive genetic variance](../../quantitative-genetics/fisher-s-decomposition-of-genetic-variance/add-var.md)

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (GENOME 562 course text, University of Washington, version of December 2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section II.8 "Selection and Fitness", subsection "The Fundamental Theorem of Natural Selection",
  p. 94 (Fisher's theorem and the limits of its interpretation; the example is a direct calculation, not
  taken from the source).
