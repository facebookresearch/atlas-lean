# Logarithmic coefficients for multicolor triangle Ramsey numbers

For every real $\varepsilon>0$ and every sufficiently large integer $k$,

$$ (1/3-\varepsilon)k\log k\le \log R_k(3)\le (1+\varepsilon)k\log k.$$

Both inequalities hold beyond a common cutoff that may depend on $\varepsilon$; all logarithms are natural. This bounds the normalized coefficients from below and above, not their convergence to a single value.

## Depends on

- [Multicolor triangle Ramsey number](multicolor-triangle-ramsey-number.md)

## Proof depends on

- [Explicit lower bound for the multicolor triangle Ramsey number](multicolor-triangle-ramsey-number-explic.md)
- [Finite Ramsey theorem for pairs](../../../Combinatorics/ramsey-theory/structural-ramsey/ramsey-two-uniform.md)

## Proof outline

Use the explicit bound and show that the log-log term and constant are lower order on the lower side. Identify the existing two-uniform Ramsey theorem with the complete-graph coloring model for finiteness, then quantify the multicolor recursion to deduce the factorial-scale upper bound.

## Sources

- [OpenAI, *Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 9](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
- [Pinned source: `triangleRamseyNumber_log_sharp_coefficients`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/I_MulticolorTriangleRamsey.lean#L36-L42)
