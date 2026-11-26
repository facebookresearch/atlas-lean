# Diploid two-locus viability selection followed by meiosis

Order gametes as $AB,Ab,aB,ab$, with frequency vector $x$ on the
probability simplex. Random mating forms ordered genotypes with
frequencies $x_ix_j$. Let $w_{ij}=w_{ji}\ge0$ be their viabilities,
with $w_{14}=w_{23}=\gamma$, and let $r\in[0,1/2]$ be the recombination
fraction in meiosis. Write $w_i=\sum_jw_{ij}x_j$,
$\bar w=\sum_ix_iw_i>0$, $D=x_1x_4-x_2x_3$ and
$e=(1,-1,-1,1)$. Viability selection followed by meiosis gives

$$x_i'=\frac{x_iw_i-e_ir\gamma D}{\bar w}.$$

This is a probability vector. Equal **positive** viabilities reduce it
to $x_i'=x_i-e_irD$; at $r=0$ it is the four-allele viability-selection
recursion with the state-dependent marginal fitnesses $w_i(x)$.
The model is not, in general, obtained by applying the haploid
recombination map to the selected gamete marginals $x_iw_i/\bar w$.

## Background

- [Neutral recombination identity](../linkage-disequilibrium-and-haldane-s-map-functio/recombine-eq-sub.md)
- [Selection normalization](select.md)

## Expansion

After viability selection an ordered genotype has probability
$x_ix_jw_{ij}/\bar w$. In a coupling double heterozygote $AB/ab$,
parental gametes each have probability $(1-r)/2$ and recombinant gametes
each have probability $r/2$; the roles reverse in $Ab/aB$.
The other genotypes produce the usual parental gametes.
Summing gives the displayed correction using $w_{14}=w_{23}$.
For example the first numerator is
$w_{11}x_1^2+w_{12}x_1x_2+w_{13}x_1x_3
+(1-r)\gamma x_1x_4+r\gamma x_2x_3$, visibly nonnegative.
The other three numerators have the analogous nonnegative decomposition;
their sum is $\bar w$ because $\sum_i e_i=0$.
This derives both the model and simplex preservation, without treating
a neutral special case as a proof prerequisite.

For a check on life-cycle order, take $x_i=1/4$, $r=1/2$, all viabilities
one except $w_{11}=2$. Then $D=0$ and this map gives $x_1'=5/17$.
Recombining the selected gamete marginals instead gives $83/289$, a
different answer. The [haploid product-fitness result](../haploid-selection-and-multiplicative-fitnesses/recombine-select-eq-mul.md) concerns a different model;
it is not a proof of this diploid map.

## Sources

- R. C. Lewontin and K. Kojima, "The evolutionary dynamics of complex polymorphisms", Evolution 14 (1960), 458–472, <https://doi.org/10.2307/2405995>.
