---
article_id: af_8ff232af8080fd8533caab00
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ProbabilityTheory.hoeffding_bernoulli_sum_abs_tail
---

# Hoeffding Bernoulli Sum Abs Tail

Hoeffding's inequality for a sum of independent Bernoulli variables
(concept `jis_grounded_4cd778f9d6394cee44270586`,
`hoeffding_bernoulli_sum_abs_tail`): strict two-sided tail
`Prob(|X_n - n * p| > ε * n) ≤ 2 * exp (-2 * ε ^ 2 * n)`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Probability.HoeffdingBernoulliSumAbsTail](../../../../sources/v2/MathlibExt.md)
- `https://cs.uwaterloo.ca/journals/JIS/VOL28/Jackson/jackson5.tex` (Proposition, Hoeffding's Inequality, Thm. 2 of Hoe63). Proves `Wanted` entry `hoeffding_bernoulli_sum_abs_tail`.
