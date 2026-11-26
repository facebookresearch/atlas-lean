# Neutral overhang and bounds on indel-purified DNA

**Model.** Idealize a genome as functional segments, which are purged of every indel by selection, separated by neutral DNA that accepts all indels; treat indels as point events occurring in neutral DNA independently with probability $\rho$ per site, so the expected distance between neutral indels is $K = \rho^{-1}$. Each functional segment then lies inside an ungapped segment that also contains neutral sites on either side (the **neutral overhang**).

**Proposition.**

1. *Isolated functional segments.* The expected number of neutral sites in the ungapped segment containing an isolated functional segment is $2K$ ($K$ on each side).
2. *Densely clustered functional segments.* In a region of length $T \gg K$ from which a proportion $q$ of indels has been purified and which consists of $N$ ungapped segments of mean length $L > K$, in expectation $L = K/(1 - q)$, the amount of indel-purified DNA is

$$qT = N(L - K),$$

so each ungapped segment contains on average exactly $K$ neutral sites.
3. Hence the expected number of neutral sites per ungapped segment that contains functional material lies between $K$ and $2K$, depending on clustering. Combining this with the excess $\sigma$ of long ungapped segments over the neutral geometric law gives an upper bound on indel-purified DNA (attribute all excess to selection, assume high clustering, overhang $K$) and a lower bound (subtract the excess seen in neutrally evolving ancestral repeats, assume isolation, overhang $2K$).

## Depends on

- [Geometric intergap lengths under the neutral indel model](geometric-intergap-lengths-under-the-neutral-indel-model.md)

## Expansion

For item 1, by the memorylessness of the geometric law, the distance from either end of a functional segment to the nearest neutral indel outward has mean $K$. For item 2, the region would carry $T/K$ indels without selection and carries $n = (1 - q)T/K$ after purification, so $L = T/n = K/(1 - q)$, i.e. $q = 1 - K/L$; then $qT = qNL = (1 - K/L)NL = N(L - K)$. Applied to human–mouse alignments this yields between about 2.6% and 3.25% of human euchromatin under indel-purifying selection (roughly 79 to 100 Mb), and ungapped-segment length thresholds chosen per G+C stratum identify candidate functional segments at a controlled false discovery rate.

## Sources

- Lunter G, Ponting CP, Hein J, "Genome-wide identification of human functional DNA using a neutral indel model" (2006), Results, "Bounds on Selection", and Materials and Methods, "Contribution of neutral sites to long IGS", <https://doi.org/10.1371/journal.pcbi.0020005>, PMCID PMC1326222.
