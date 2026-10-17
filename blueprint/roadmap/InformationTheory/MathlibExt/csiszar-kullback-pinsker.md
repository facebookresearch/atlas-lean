---
article_id: af_37dac4853b74aaa5be6d7cc9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.InformationTheory.Pinsker.csiszar_kullback_pinsker
---

# Pinsker

Finite strictly-positive Csiszar-Kullback-Pinsker inequality: for finite nonempty `α` and pmfs `p, q
: α → ℝ` with `p a > 0`, `q a > 0` and sums `1`, `(∑ |p a - q a|)² ≤ 2 * ∑ p a * log (p a / q a)`
with natural log, equivalent to `TV(p,q) ≤ √(D_KL/2)`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Log-sum inequality](sum-mul-log-sum-div-sum-le-sum-mul-log-d.md)

## Sources

- [MathlibExt, MathlibExt.InformationTheory.Pinsker](../../../sources/v2/MathlibExt.md)
- M. S. Pinsker, Information and Information Stability of Random Variables and Processes (1960; English translation 1964), with I. Csiszar, Information-type measures of difference of probability distributions and indirect observations, Studia Sci. Math. Hungar. 2 (1967), 299-318. Proves `Wanted` entry `csiszar_kullback_pinsker`, without its `[DecidableEq α]`, which the statement does not use.
