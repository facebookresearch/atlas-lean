---
article_id: af_753658080be0f039763fa1ee
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Probability.Statistics.GaussMarkov.gaussMarkov_covariance_minimality
---

# Gauss Markov

In the unit-noise model with invertible `Xᵀ * X`, the least-squares matrix `B = (Xᵀ * X)⁻¹ * Xᵀ`
satisfies `B * X = 1` and `A * Aᵀ - B * Bᵀ` is `PosSemidef` for every `A` with `A * X = 1`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Probability.Statistics.GaussMarkov](../../../../../sources/v2/MathlibExt.md)
- C. F. Gauss, *Theoria combinationis observationum erroribus minimis obnoxiae* (1823); A. C. Aitken, “On Least Squares and Linear Combination of Observations,” *Proceedings of the Royal Society of Edinburgh* 55 (1936), 42–48, DOI `10.1017/S0370164600014346`.
