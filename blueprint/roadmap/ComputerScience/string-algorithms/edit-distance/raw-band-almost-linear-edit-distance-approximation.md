# Almost-linear-work edit approximation in the raw-band bit model

Fix a binary rational accuracy with value $0<\varepsilon<1$ (signed binary numerator, positive binary denominator). On integer lists $x,y$ and cap $N$, use exactly the [branch guard and indexed random law](raw-band-branch-and-randomness-model.md) and the [raw-band answer, work and footprint functions](raw-band-answer-work-and-footprint.md), including the specified recoding of negative symbols, typed rejection-array indices and normalized cost counters. Let $A$ be the natural answer, $W$ the real work counter and $S$ the natural space counter for each outcome of this law. These are three functions of the specified execution, not freely chosen witnesses to bounds.

For all $x,y,N$ with $|x|+|y|\le N$, the probability that $d_E(x,y)\le A\le(1+\varepsilon)d_E(x,y)$ is at least $2/3$. For $x=y$ the answer is zero at **every** outcome for every $N$, even without the length-cap premise. For every natural $C$ and real $\eta>0$, there is a threshold after which, uniformly for $|x|+|y|\le N$ and $|z|\le(N+2)^C$ for each symbol of both input lists, the integral of $W$ against that law is at most $(N+2)^{1+\eta}$. Separately for each natural $C$, for all sufficiently large $N$ and the same bounded lists, every outcome has $S\le(N+2)^{C+65564}$. The accuracy is fixed before these thresholds. No lower-level time equivalence or guarantee about an inaccurate answer is asserted.

## Depends on

- [Physical branch guard and exact product/rejection law](raw-band-branch-and-randomness-model.md)
- [Fixed raw-band answer, real work integral and natural footprint functions](raw-band-answer-work-and-footprint.md)
- [Unit-cost edit distance](edit-distance.md)
- Exact-suffix versus raw-band execution, accepted/rejected seed tables, memoized bit queries, and their output, work and peak-space interpretations.

## Proof depends on

- Accuracy and zero-case correctness for the computed law, integrated binary work bound, and all-outcome footprint bound with the exact exponent.

## Expansion

First realize the branch, key spaces and all three output/cost functions in one fixed execution model. For accuracy, separate exact fallback from accepted-seed memo decoding; for space, retain the terminal allocation and temporary-cell counts. Reuse source equalities to the proved structured pipeline only after establishing them for the same native input and counters. Do not use generic polynomial space to replace the bound at every outcome or interchange the large-$N$ and input quantifiers.

## Sources

- [Comparator statement: `OAI.EditApproximation.almostLinearEditDistanceRawBand`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EditApproximation.lean#L19146-L19167)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/121.md)
- [Raw-band target and bridge to the proved pipeline](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/EditApproximation/Specification/RawBandMain.lean)
