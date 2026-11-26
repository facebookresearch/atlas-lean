# Chance expectation of kataegis foci under a uniform Poisson mutation model

Let a cancer genome of length $g$ base pairs carry $n$ somatic substitutions, and order them by chromosomal position, so that the intermutation distance of a mutation is the number of base pairs to the next one. Call a run of $6$ or more consecutive mutations with mean intermutation distance at most $1000$ bp a **kataegis focus**; such runs are found in practice by piecewise-constant segmentation of the intermutation-distance profile, and are additionally characterized biologically by a preponderance of C>T and C>G substitutions in a TpC context on one strand.

**Model.** Assume the $n$ mutations fall independently and uniformly along the genome, so that the number falling in any window of length $w$ is approximately Poisson with mean $wn/g$.

**Proposition.** Under this model the probability that a given mutation is followed by five further mutations within $5000$ bp, which triggers a call of a focus of six mutations averaging at most $1000$ bp apart, is
$$p \;=\; \Pr\bigl(\mathrm{Pois}(5000\,n/g) \ge 5\bigr) \;=\; 1 - e^{-\mu}\sum_{j=0}^{4} \frac{\mu^{j}}{j!}, \qquad \mu = \frac{5000\,n}{g},$$
and the expected number of chance foci in the genome is $np$. The expectation is strictly increasing and, for small $\mu$, of order $n\mu^{5}/120 \propto n^{6}$, so chance foci are negligible at low burdens and dominate at high ones: with $g \approx 3 \times 10^{9}$ bp, a genome carrying $n = 2 \times 10^{5}$ substitutions is expected to yield about $0.16$ foci by chance, whereas burdens of several hundred thousand substitutions yield many.

## Depends on

## Expansion

The window length $5000$ bp is the largest total span consistent with six mutations whose mean intermutation distance is at most $1000$ bp, since that mean is the span divided by five; requiring five further mutations inside the window is therefore the Poisson event that realizes the calling rule anchored at a given mutation. Multiplying by $n$ counts anchors rather than disjoint foci, so $np$ overcounts slightly and is an upper bound on the expected number of distinct chance foci, which is the conservative direction for declaring an observed focus significant. The sixth-power growth in burden is the practical content: in hypermutated genomes a clustering call carries almost no evidence on its own, and the sequence-context, strand and processivity features, together with the association with rearrangement breakpoints, are what distinguish genuine localized hypermutation from a dense sample of a uniform process. The same calculation, run per copy-number segment with a segment-specific rate, is what bounds false calls inside focal amplifications, where the local mutation density is raised by the copy number rather than by a clustered process.

## Sources

- L. B. Alexandrov, S. Nik-Zainal, D. C. Wedge et al., "Signatures of mutational processes in human cancer", Nature 500 (2013), 415–421, Online Methods, sections "A PCF-based algorithm for the detection of kataegis", "Variation in number of foci of kataegis and relationship with genome-wide mutation burden" and "Definition of kataegis", <https://doi.org/10.1038/nature12477>, PMCID: PMC3776390.
- S. Nik-Zainal, L. B. Alexandrov, D. C. Wedge et al., "Mutational processes molding the genomes of 21 breast cancers", Cell 149 (2012), 979–993.
