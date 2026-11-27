# The infinitesimal model as a limit of many loci

In the
infinitesimal model the genetic component of a trait is distributed within each family as a normal
random variable centred at the average of the parental genetic components, with a variance independent
of the parental traits. Barton, Etheridge and Véber (2017) obtain the model as the limit, as the number
$M$ of underlying loci tends to infinity, of a model with Mendelian inheritance, mutation and
environmental noise in which the genetic component is purely additive: within each family the genetic
components of the current generation are normally distributed with a variance independent of ancestral
traits, up to an error that tends to $0$ as $M \to \infty$, for which they give an explicit rate.

## Proof depends on

- [Berry–Esseen bound for the segregation deviation](abs-segregation-cdf-sub-le.md)

## Expansion

A sound expansion uses the one-generation normal approximation of the
[offspring segregation deviation](segregation-deviation.md) given the parents (the Berry–Esseen bound
above, for unlinked loci with additive effects of order $1/\sqrt M$) as the base step. It then states, as a page of its own, the bridge from that
one-generation statement to the many-generation result, with the source's conditioning on the whole
pedigree and on the trait values of ancestors, its conditions on the allelic effects, mutation and
environmental noise, and the distance in which the error is measured, and finally the multi-generation
result.

## Sources

- N. H. Barton, A. M. Etheridge and A. Véber, "The infinitesimal model: Definition, derivation, and
  implications", Theoretical Population Biology 118 (2017), 50–73,
  <https://doi.org/10.1016/j.tpb.2017.06.001>.
