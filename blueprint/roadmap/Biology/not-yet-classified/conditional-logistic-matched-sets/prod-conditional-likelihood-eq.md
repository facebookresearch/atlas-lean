# Two forms of the conditional likelihood of independent matched sets

For `n` matched
sets, set `s` having `M_s + 1` subjects with exposures `x_{s,j} ∈ ℝ^K` and its case listed first
(`j = 0`), and every coefficient vector `β`, `∏_s exp(β · x_{s,0}) / ∑_j exp(β · x_{s,j})` equals
`∏_s 1 / (1 + ∑_{j ≥ 1} exp(β · (x_{s,j} - x_{s,0})))` (Breslow and Day 1980, (7.2), (7.3)); for
`M_s = 1` this is (7.3). The identity is algebraic. Each factor of the first product is the
conditional probability that the case of set `s` is subject `0` (`conditionalCaseProb_eq`), and the
product is the joint conditional likelihood of the `n` sets only when the outcomes are independent
across sets as well as within each set: independence within each set does not justify
multiplying probabilities across sets.

## Sources

- Breslow and Day (1980), p. 251, (7.2), and p. 253, (7.3).
