# Deterministic metric k-median approximation within arbitrary positive slack of 1 + 2/e

For each real $\varepsilon>0$, there is one [finite-alphabet TM2](../../TheoryOfComputation/turing-machines/multi-tape-and-multi-stack/finite-alphabet-tm2-binary-abi.md) deterministic polynomial-time computation for the following inputs: labelled finite points with a rational distance matrix satisfying the metric axioms including $d(i,j)=0\iff i=j$, specified clients and candidate facilities, and $1\le k\le|\mathrm{candidates}|$. For a natural with $\ell$ low-to-high bits, its framing is $\ell$ ones then zero then its bits. The instance word encodes the order and budget by these framed naturals, then the client and facility masks, then the row-major distance matrix as reduced rationals: a negative-sign bit followed by framed numerator magnitude and denominator. Every result is the full, unframed membership mask of a nonempty subset $S$ of the facilities with at most $k$ elements and total nearest-center cost over all clients at most $(1+2/\mathrm e+\varepsilon)$ times the minimum over such sets.

The algorithm may depend on $\varepsilon$. No algorithm attaining exactly $1+2/\mathrm e$ is asserted.

## Depends on

- [Exact finite-work-alphabet TM2 and binary output](../../TheoryOfComputation/turing-machines/multi-tape-and-multi-stack/finite-alphabet-tm2-binary-abi.md)
- Finite rational metrics, feasible sets and their cost, with finite-work-alphabet binary output semantics.

## Proof outline

Separate the approximation construction and derandomization from finite-alphabet machine bounds. Keep fixed epsilon outside the machine quantifier; no uniform dependence on epsilon or attainment of the factor at epsilon zero is asserted.

- Deterministic near-threshold approximation and its implementability in the supplied encodings.

## Sources

- [Comparator statement: `OAI.MetricKMedian.main_finite_work`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MetricKMedian.lean#L59-L63)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/125.md)
