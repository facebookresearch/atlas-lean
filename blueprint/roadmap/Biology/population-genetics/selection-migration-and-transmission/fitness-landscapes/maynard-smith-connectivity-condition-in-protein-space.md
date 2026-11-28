# Maynard Smith's connectivity condition in protein space

Represent proteins of length $L$ as points of the sequence space $\mathcal A^L$ over the $20$-letter amino-acid alphabet, with two sequences adjacent when they differ by a single substitution, so that each sequence has $N = 19L$ one-step neighbours. Call a sequence *meaningful* (functional) if it is viable under selection, and let $f$ be the fraction of one-step neighbours of a meaningful sequence that are themselves meaningful. Maynard Smith's condition for evolution by natural selection to proceed through protein space by single substitutions, each intermediate retaining function, is

$$f N > 1,$$

that is, a meaningful protein must on average have more than one meaningful neighbour, so that meaningful sequences form extended networks rather than isolated islands.

**Branching-process form.** Suppose that, starting from a meaningful sequence, the numbers of new meaningful one-step neighbours found at successive steps are independent with mean $f N$ (neighbours are treated as new, which is accurate while explored sets are tiny compared with $20^L$). Then the explored set of meaningful sequences is a Galton–Watson process with mean offspring $fN$: if $fN \le 1$ it is finite with probability one (excluding the degenerate case of exactly one offspring always), and if $fN > 1$ it is infinite with positive probability. Thus $fN > 1$ is exactly the threshold at which a mutational walk can reach meaningful sequences many substitutions away.

## Proof sketch

There are $L$ positions and $19$ alternative residues at each, hence $19L$ neighbours, and $fN$ is the expected number of meaningful ones. The Galton–Watson extinction criterion (extinction is certain if and only if the mean offspring number is at most $1$, unless the offspring number is identically $1$) turns Maynard Smith's heuristic into the supercritical condition for an unbounded neutral or adaptive network. Because $N$ grows linearly in $L$, even a tiny $f$ (of order $1/(19L)$) suffices, which is how Maynard Smith answered the argument that functional proteins are too rare in sequence space to be found by mutation and selection. The same picture underlies later work on fitness landscapes, neutral networks, accessible mutational paths in empirical landscapes and directed evolution.

## Depends on

- [Fitness landscapes as mathematical objects](fitness-landscapes-as-explicit-mathematical-obje.md)

## Proof depends on

- [Galton–Watson extinction criterion](../../../../Probability/branching-processes/galton-watson-process/extinction-prob-eq-one-iff.md)

## Sources

- C. B. Ogbunugafor, "A reflection on 50 years of John Maynard Smith's 'Protein Space'", Genetics 214 (2020), 749–754, discussion of the relation $fN > 1$ and its uses, <https://doi.org/10.1534/genetics.119.302764> (PMC7153927).
- J. Maynard Smith, "Natural selection and the concept of a protein space", Nature 225 (1970), 563–564, <https://doi.org/10.1038/225563a0>.
