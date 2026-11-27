# Chance expectation of kataegis foci under a uniform Poisson mutation model

Let a cancer genome of length $g$ base pairs carry $n$ somatic substitutions, ordered by chromosomal position, with [intermutation distances](intermutation-distance-and-kataegis.md) measured from each mutation to the next. A putative **kataegis focus** is a segment of $6$ or more consecutive mutations with mean intermutation distance at most $1000$ bp, found in practice by piecewise-constant segmentation of the intermutation-distance profile, and additionally characterized biologically by a preponderance of C>T and C>G substitutions in a TpC context on one strand.

**Model.** Assume the $n$ mutations fall independently and uniformly along the genome, and approximate the number of other mutations in a window of length $w$ by a Poisson variable with mean $wn/g$.

**Anchors.** Call a mutation an *anchor* if the next five mutations lie within $5000$ bp of it, so that it starts a run of six mutations with mean intermutation distance at most $1000$ bp. Under the Poisson approximation, each mutation is an anchor with probability

$$p \;=\; \Pr\bigl(\mathrm{Pois}(\mu) \ge 5\bigr) \;=\; 1 - e^{-\mu}\sum_{j=0}^{4} \frac{\mu^{j}}{j!}, \qquad \mu = \frac{5000\,n}{g},$$

and the expected number of anchors is $np$.

**Proposition.** $np$ is strictly increasing in $n$ and, as $\mu \to 0$, $np \sim n\mu^{5}/120$, which is proportional to $n^{6}$ for fixed $g$: chance anchors are negligible at low burdens and abundant at high ones. For example, with $n = 2 \times 10^{5}$, a haploid length $g = 3 \times 10^{9}$ bp gives $\mu = 1/3$ and $np \approx 5.2$, while $g = 6.2 \times 10^{9}$ bp, about the diploid length, gives $\mu \approx 0.161$ and $np \approx 0.16$.

**Anchors are not foci.** The source uses $np$ as the expected number of chance kataegis events and reports $0.16$ for a burden of $200{,}000$ mutations, without stating $g$; that value is the formula evaluated at about the diploid length, not at $3 \times 10^{9}$. The anchor count also differs from the number of distinct segmented foci in both directions: seven mutations within $5000$ bp contain two anchors in one cluster, and a long segment can have mean intermutation distance at most $1000$ bp without any six consecutive mutations spanning at most $5000$ bp.

## Depends on

- [Intermutation distance and regional hypermutation](intermutation-distance-and-kataegis.md)
- [Poisson distribution function as a function of the mean](../../../Probability/distributions/continuous/poisson-gamma-duality/poisson-gamma-duality-identity/poisson-cdf.md)

## Proof depends on

- [Poisson distribution function is strictly decreasing in the mean](../../../Probability/distributions/continuous/poisson-gamma-duality/poisson-gamma-duality-identity/poisson-cdf-strict-anti-on.md)

## Proof sketch

The window length $5000$ bp is the span of six mutations whose mean intermutation distance is $1000$ bp, since that mean is the span divided by five, so the anchor event is that at least five of the other mutations fall in the $5000$ bp after a given one; the uniform placement makes that count binomial with $n - 1$ trials and success probability $5000/g$, approximated by the Poisson law. Monotonicity in $n$ holds because $\mu$ increases with $n$ and the Poisson upper tail increases with its mean. The small-$\mu$ asymptotics come from the leading term $e^{-\mu}\mu^5/5!$ of the tail.

## Remarks

The sixth-power growth in burden is the practical content: in hypermutated genomes a clustering call carries almost no evidence on its own, and the sequence-context, strand and processivity features, together with the association with rearrangement breakpoints, are what distinguish genuine localized hypermutation from a dense sample of a uniform process. The same calculation, run per copy-number segment with a segment-specific rate, bounds the expected anchors inside focal amplifications, where the local mutation density is raised by the copy number rather than by a clustered process.

## Sources

- L. B. Alexandrov, S. Nik-Zainal, D. C. Wedge et al., "Signatures of mutational processes in human cancer", Nature 500 (2013), 415–421, Online Methods, sections "A PCF-based algorithm for the detection of kataegis", "Variation in number of foci of kataegis and relationship with genome-wide mutation burden" and "Definition of kataegis", <https://doi.org/10.1038/nature12477>, PMCID: PMC3776390.
- S. Nik-Zainal, L. B. Alexandrov, D. C. Wedge et al., "Mutational processes molding the genomes of 21 breast cancers", Cell 149 (2012), 979–993.
