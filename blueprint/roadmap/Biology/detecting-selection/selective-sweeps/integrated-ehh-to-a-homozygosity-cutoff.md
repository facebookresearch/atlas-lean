# Integrated EHH of an empirical haplotype sample to a homozygosity cutoff

Fix a core site and a core allele, and let $\mathrm{EHH}(x)$ denote the extended haplotype homozygosity of
the haplotypes carrying that allele, evaluated at genetic distance $x$ from the core site, with $x$
measured in units $\theta = 4Nr$ built from an estimated recombination map and signed so that $x < 0$ lies
on one side of the core site and $x > 0$ on the other. The sample provides $\mathrm{EHH}$ at the
genotyped sites only, and the curve between consecutive sites is defined by linear interpolation.

Let

$$x_- = \sup\{x < 0 : \mathrm{EHH}(x) < c\}, \qquad x_+ = \inf\{x > 0 : \mathrm{EHH}(x) < c\}$$

be the nearest points on either side of the core site at which the interpolated curve drops below the
cutoff $c$, with $c = 0.05$ in the source. The integrated EHH of that core allele is the area under the
interpolated curve between those two points,

$$\mathrm{iHH} = \int_{x_-}^{x_+} \mathrm{EHH}(x)\, dx,$$

so it is a two-sided integral, and $\mathrm{iHH}_A$ and $\mathrm{iHH}_D$ denote its values for the
ancestral and the derived core allele. The quantity is defined only when both $x_-$ and $x_+$ exist within
the available data; in the source no value is reported for a core site when the region with
$\mathrm{EHH} > c$ reaches a chromosome end or a gap longer than $200$ kb, and the genetic distance spanned
by a gap of size $g$ between $20$ and $200$ kb is multiplied by $20/g$.

## Depends on

Its statement uses only the notions recalled above.

## Proof depends on

It is a definition; nothing is proved.

## Expansion

A selected allele that rose rapidly in frequency carries haplotype homozygosity much further from the core
site than a neutral allele of the same frequency, so the area under its EHH decay curve is larger. Cutting
the integral off at a positive homozygosity level keeps it finite on real data, where EHH is known only on a
finite marker set and decays to a small positive value rather than to $0$; the trapezoidal interpolation is
what the finite marker spacing permits. The left and right areas are summed as observed: the two decay
curves of a sample need not be mirror images, and the left and right areas can differ by different amounts
for the ancestral and the derived core allele, so the empirical two-sided value is in general not twice a
one-sided area. Only for a pair of curves that are symmetric about the core site and integrated with the
same conventions, as in the [star-genealogy model](sweep-ehh.md), is the two-sided area twice the
[one-sided integral](ihh.md), as for the [two-sided star-genealogy iHH](ihh-two-sided.md).

## Sources

- B. F. Voight, S. Kudaravalli, X. Wen and J. K. Pritchard, "A map of recent positive selection in the human genome", PLoS Biology 4 (2006), e72, <https://doi.org/10.1371/journal.pbio.0040072> (PMC1382018). (Equation 1 and the "Calculation of iHS" section of Materials and Methods.)
