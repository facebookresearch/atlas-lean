# Conditional infimum of deterministic metric k-median factors

Under $\mathsf P\ne\mathsf{NP}$ in the specified binary TM2 model, the infimum of the real factors $\alpha$ for which a deterministic polynomial-time finite-work-alphabet machine always produces a nonempty feasible mask of cost at most $\alpha\,\mathrm{OPT}$ is $1+2/\mathrm e$. Instances, encodings, feasibility and cost are exactly as in the [deterministic approximation theorem](deterministic-metric-k-median-approximation.md). The scope is an infimum, not attainment.

Here $\mathsf P$ consists of binary languages with an exact [finite-alphabet TM2](../../TheoryOfComputation/turing-machines/multi-tape-and-multi-stack/finite-alphabet-tm2-binary-abi.md) polynomial-time function from words to one Boolean, output as the one-bit word and true exactly on members. In $\mathsf{NP}$ use a Boolean verifier on word pairs with this exact output; encode $(x,w)$ by the framed natural $|x|$ followed by $x$ and $w$ with no further delimiter. Membership is equivalent to existence of a verifying witness with length bounded by a single natural-coefficient polynomial in $|x|$. This is the source model; no equality with another presentation of the complexity classes is assumed.

## Depends on

- [Exact binary computation for deciders, verifiers and approximation algorithms](../../TheoryOfComputation/turing-machines/multi-tape-and-multi-stack/finite-alphabet-tm2-binary-abi.md)
- Finite-work-alphabet binary complexity classes and the set of approximation factors in the rational metric input model.

## Proof depends on

- [Approximations above the threshold](deterministic-metric-k-median-approximation.md)

## Expansion

Separate conditional hardness from the order-theoretic infimum argument. In the exact finite-alphabet decision/reduction model, show that a feasible rational-metric approximation factor strictly below the stated constant implies equality of those P and NP classes, preserving the source graph projection parameters. Combine this result with the already linked positive-slack approximation; the infimum argument does not imply attainability.

## Proof outline

State the hardness implication to equality of the specified P and NP classes, prove the approximation factor set is nonempty and bounded below, then take the infimum. Leave attainment undecided.

## Sources

- [Comparator statement: `OAI.MetricKMedian.threshold`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/KMedianThreshold.lean#L101-L104)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/125.md)
- [Exact correction, bit and pair encoders, and complexity classes](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/KMedianThreshold.lean#L51-L105)
- [Proof of the reduction and the prerequisite interfaces](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/KMedian/Threshold.lean)
