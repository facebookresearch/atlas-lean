# X-chromosomal and autosomal ancestry after a single sex-biased admixture pulse

**Model.** An admixed population is founded in generation $0$ by a single admixture event. Among the founding females a fraction $s_f$ derive from a given source population $S$, and among the founding males a fraction $s_m$; afterwards there is no further input from any source, mating is random, and generations are discrete with no selection or drift in the expected values. Let $H_A(t)$ be the expected autosomal ancestry from $S$ of an individual in generation $t \ge 1$, and $H_X^f(t), H_X^m(t)$ the expected X-chromosomal ancestry from $S$ of a female, respectively male, in generation $t$.

**Proposition.**

1. *Autosomes.* $H_A(t) = \dfrac{s_f + s_m}{2}$ for every $t \ge 1$.
2. *X chromosome.* With $\bar H_X = \dfrac{2s_f + s_m}{3}$, for every $t \ge 0$ (generation $0$ meaning the founders, $H_X^f(0) = s_f$, $H_X^m(0) = s_m$)

$$H_X^f(t) - \bar H_X = \left(-\tfrac12\right)^{t}\,(s_f - \bar H_X),\qquad H_X^m(t+1) = H_X^f(t),$$

so both sexes converge to $\bar H_X$, with damped oscillation.
3. *Inversion.* In the long run, the sex-specific contributions are recovered from the two ancestry levels:

$$s_f = 3\bar H_X - 2H_A,\qquad s_m = 4H_A - 3\bar H_X .$$

In particular $\bar H_X > H_A$ iff $s_f > s_m$: X-chromosomal ancestry exceeding autosomal ancestry signals a female-biased contribution from that source.

Applied to genotyped individuals across the Americas, comparing X and autosomal ancestry under a single pulse $1$ to $15$ generations ago gave African female-to-male contribution ratios $s_f/s_m > 1$ in every region, ranging from about $1.5$–$2$ in British-colonized regions to $4$–$17$ in Latin America, and European male bias in most regions.

## Proof depends on

- [One generation of X-linked transmission](../../../population-genetics/unequal-allele-frequencies-in-the-sexes-and-x-li/step.md)
- [Closed form for the female frequency at an X-linked locus](../../../population-genetics/unequal-allele-frequencies-in-the-sexes-and-x-li/fst-iterate-sub-pbar.md)
- [Weighted mean allele frequency at an X-linked locus](../../../population-genetics/unequal-allele-frequencies-in-the-sexes-and-x-li/pbar.md)

## Expansion

Ancestry from $S$ at a locus behaves as an allele frequency that is transmitted Mendelianly. An autosome of a generation-$1$ child comes from its mother or father with probability $\tfrac12$ each, giving $(s_f + s_m)/2$, and random mating keeps this mean thereafter. For the X chromosome, daughters inherit one X from each parent and sons inherit their X from the mother, so $(H_X^f, H_X^m) \mapsto ((H_X^f + H_X^m)/2,\ H_X^f)$ each generation, which is exactly X-linked transmission of an allele frequency. Its invariant is the weighted mean $(2H_X^f + H_X^m)/3$, equal to $\bar H_X$ at the founders, and the deviation of the female value is multiplied by $-\tfrac12$ each generation. Solving $H_A = (s_f + s_m)/2$ and $\bar H_X = (2s_f + s_m)/3$ gives part 3. With several sources the same relations hold for each source separately; more general models (continuing sex-biased migration, variable numbers of founders) give signatures outside the classical $2/3$ and $1/3$ weights.

## Sources

- S. J. Micheletti, K. Bryc, S. G. Ancona Esselmann et al., "Genetic consequences of the transatlantic slave trade in the Americas", American Journal of Human Genetics (2020), Material and Methods (sex-bias analysis) and Table 1, <https://doi.org/10.1016/j.ajhg.2020.06.012> (PMC7413858).
- A. Goldberg and N. A. Rosenberg, "Beyond 2/3 and 1/3: the complex signatures of sex-biased admixture on the X chromosome", Genetics 201 (2015), 263–279, <https://doi.org/10.1534/genetics.115.178509>.
