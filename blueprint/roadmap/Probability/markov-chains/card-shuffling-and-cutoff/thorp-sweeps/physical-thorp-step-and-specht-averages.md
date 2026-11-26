# Physical Thorp pair steps and Specht Fourier averages

On the $d$-cube with $d>0$, independently choose a fair bit for each pair of words with common tail. XOR that bit into the first coordinate, then rotate the coordinates by moving the first bit to the last position. Use the identity in dimension zero. A physical run composes independent copies of this step with the first step acting first; the $d$-step law is a full coordinate sweep in a rotating frame. For a chosen relabelling of the cube into the tabloid Specht model, its Fourier operator is the average of the corresponding group-action matrices. The weighted Schatten moments use the unnormalized real trace of the appropriate real power of the positive square $Q^*Q$. For the full permutation or an injective marked list, push the law forward by applying its permutation to the input. The reference distribution is the uniform law on permutations or on injective lists, respectively. Total variation is half the sum of absolute differences, and for the full-deck law the mixing-time cutoff uses the identity start, equivalent to the worst deterministic start by translation invariance.

## Depends on

- [Tabloid Specht modules and all-copy subgroups on occupied boards](occupied-board-specht-model.md)

## Sources

- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/WeightedSweepMoments.lean#L165-L275)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CoordinateTrace.lean#L9-L180)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ThorpRemaining.lean#L11-L476)
