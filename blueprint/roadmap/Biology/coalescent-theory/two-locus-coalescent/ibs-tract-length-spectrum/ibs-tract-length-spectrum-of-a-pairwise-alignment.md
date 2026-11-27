# IBS tract length spectrum of a pairwise alignment

**Definition.** In an alignment of two haplotypes of length $L$ base pairs, an **$l$-base IBS tract** ($l \ge 0$) is a run of exactly $l$ consecutive identical sites bracketed by polymorphic sites on both sides; a $0$-base tract is a pair of adjacent polymorphic sites. The *IBS tract spectrum* is the vector $(N_l)_{l \ge 0}$ of counts of $l$-base tracts. Let the tail probability $p_l$ be the probability that a randomly chosen site is polymorphic and is followed by at least $l$ identical sites (the next $l$ sites are all identical), so $p_0$ is the probability that a site is polymorphic. Then $p_l - p_{l+1}$ is the probability that a site is polymorphic, followed by exactly $l$ identical sites and then a polymorphic site, and with uniform mutation and recombination rates, away from the ends of the sequence,

$$\mathbb{E} N_l \approx L\,(p_l - p_{l+1}) \qquad (l \ll L).$$

For a bin $[a, b)$ of tract lengths the expected count is $\sum_{a \le l < b} \mathbb{E} N_l \approx L\,(p_a - p_b)$.

**No-recombination term.** Let the pair have coalescence-time density $f(t)$, per-site per-generation mutation rate $\mu$ and recombination rate $r$, and use the infinite-sites approximation. The probability that a site is polymorphic, the next $l$ sites are identical (a tail event, as for $p_l$), and no ancestral recombination occurs within those $l$ sites is

$$p_l^{(0)} = \int_0^\infty 2\mu t\, e^{-2(\mu + r) l t} f(t)\, dt.$$

For a constant-size population with coalescence density $f(t) = \tfrac{1}{2N} e^{-t/(2N)}$, and $\theta = 4N\mu$, $\rho = 4Nr$,

$$p_l^{(0)} = \frac{\theta}{\bigl(1 + (\theta + \rho)\, l\bigr)^2}.$$

For piecewise-constant population sizes, divergence and admixture pulses the coalescence density is a linear combination of exponentials, so $p_l^{(0)}$ is the corresponding linear combination of constant-size terms. Under the sequentially Markov coalescent, $p_l$ is the sum over the number of ancestral recombinations inside the tract; the terms with one and two internal recombinations involve two and three coalescence times and are computed in closed form, and tracts with more internal recombinations are rare because the chance of $k$ ancestral recombinations before the first mutation decays geometrically in $k$.

**Inference.** Group tract lengths into disjoint bins $B_1 = [a_1, a_2), B_2 = [a_2, a_3), \dots$ (in practice exponentially spaced), with counts $N_{B_m} = \sum_{l \in B_m} N_l$ and means $\mathbb{E}_\Theta N_{B_m} \approx L\,(p_{a_m} - p_{a_{m+1}})$ computed from the tail probabilities $p_l$ under $\Theta$. Treating the bin counts as independent Poisson variables gives the composite log-likelihood

$$\log \mathcal{L}(\Theta) = \sum_{m} \bigl(N_{B_m} \log \mathbb{E}_\Theta N_{B_m} - \mathbb{E}_\Theta N_{B_m}\bigr) + \text{const},$$

maximized over demographic parameters $\Theta$ (population sizes, split times, admixture times and fractions).

## Depends on

- [Pairwise sequentially Markov coalescents SMC and SMC′](../sequentially-markov-coalescent-smc-smc-pairwise.md)

## Proof sketch

The event "polymorphic, then at least $l$ identical sites" is the disjoint union of "polymorphic, then exactly $l$ identical sites, then a polymorphic site" and "polymorphic, then at least $l + 1$ identical sites", which gives the exact-length probability $p_l - p_{l+1}$; summing over the starting site of each tract gives $\mathbb{E} N_l$ up to edge effects at the sequence ends. Without recombination every site of the tract shares the coalescence time $t$; each site differs independently with probability about $2\mu t$, and no recombination in the tract's history over its $2t$ generations of branch length has probability $e^{-2rlt}$, giving the integrand. With the exponential density the integral is $\int_0^\infty \tfrac{2\mu t}{2N} e^{-bt}dt = \tfrac{2\mu}{2N b^2}$ with $b = \tfrac{1}{2N} + 2(\mu + r)l$, which simplifies to the displayed formula. Its $l^{-2}$ tail shows why long tracts carry information about recent times: a tract of length $l$ typically coalesced about $1/(2(\mu + r)l)$ generations ago. Recent gene flow between diverged populations leaves long IBD segments that lengthen the between-population spectrum, so the method dates admixture pulses too old for direct IBD detection. Using Marjoram and Wall's SMC$'$, which allows a recombination to leave the coalescence time unchanged, for the largest term removes a bias of the plain SMC against intermediate-length tracts. Applied to sequenced European and African parents, the fit placed the European–African split near 55 thousand years ago with gene flow until about 13 thousand years ago.

## Sources

- K. Harris and R. Nielsen, "Inferring demographic history from a spectrum of shared haplotype lengths", PLoS Genetics 9 (2013), e1003521, <https://doi.org/10.1371/journal.pgen.1003521>, PMCID PMC3675002. Methods, "A formula that is exact under the SMC", "Adding recombination and population size changes", "Improving accuracy via the SMC'" and "Inference strategy"; Results (Table 2).
