# Qualifications of the neutral substitution rate: generation time, linkage and units

This node collects the qualifications of the statement that the rate of neutral substitution equals the neutral mutation rate $u$ per copy per generation.

- **Units.** A rate per year is the rate per generation divided by the generation time in years, so species with different generation times have different neutral substitution rates per year even when $u$ per generation is the same.
- **Linked selection.** Consider any reproduction model, possibly with selection at sites linked to a neutral site, in which the allele at the neutral site does not affect reproduction. Let $M_t$ be the number of copies of the neutral site in generation $t$, and suppose that with probability $1$ all copies at the neutral site eventually descend from a single copy of generation $t$. If a new mutation is placed on a uniformly chosen one of the $M_t$ copies, independently of the genealogy, then its probability of eventual fixation is exactly $1/M_t$: the events that a given copy is the eventual ancestor partition the probability space into $M_t$ events whose probabilities sum to $1$, and the mutated copy is chosen uniformly and independently of them. With $M_t u$ new neutral mutations per generation, the expected flux of mutations destined to fix is therefore $u$ per generation, whatever the linked selection.
- **Diversity.** Unlike this flux, neutral diversity is affected by linked selection.
- **Selection on the mutation.** When the mutation itself has selection coefficient $s$, the substitution rate is $M u\, \pi_M(s)$, where $\pi_M(s)$ is its fixation probability in a population of $M$ copies.

No claim is made that observed molecular evolution is neutral.

## Expansion

A good expansion states each part of this topic as a page of its own, with hypotheses fixed from a source:

- the units statement;
- the partition argument $\sum_c \mathbb P(\text{copy } c \text{ is the eventual ancestor}) = 1$ and the resulting fixation probability $1/M_t$ under linked selection;
- an explicit statement that the argument does not give universality of neutral diversity.

Prerequisites:

- the expected flux of eventually fixing neutral mutations equals $u$;
- the substitution rate $M u\, \pi_M(s)$ with selection on the mutation.

## Sources

- C. W. Birky and J. B. Walsh, "Effects of linkage on rates of molecular evolution", *Proceedings of the National Academy of Sciences USA*, 1988, <https://pubmed.ncbi.nlm.nih.gov/3413105/>
- R. Lanfear, H. Kokko and A. Eyre-Walker, "Population size and the rate of evolution", *Trends in Ecology and Evolution*, 2014, <https://pubmed.ncbi.nlm.nih.gov/24148292/> (background)
- B. Charlesworth, "Fundamental concepts in genetics: effective population size and patterns of molecular evolution and variation", *Nature Reviews Genetics*, 2009, <https://pubmed.ncbi.nlm.nih.gov/19204717/> (background)
