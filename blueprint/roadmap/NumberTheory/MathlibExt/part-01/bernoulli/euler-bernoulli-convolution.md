---
article_id: af_af6aa3c8008edfc957955e49
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.euler_bernoulli_convolution
---

# Euler Bernoulli Convolution

Euler convolution identity for Bernoulli numbers.

Stable concept id: `jis_grounded_d68f7d9a125a7c1b53cb901e`.
Atomic task id: `jis_rank41_euler_bernoulli_general`.

Uses the source convention `B₁ = -1/2`, matching Mathlib's `bernoulli : ℕ → ℚ`
from `Mathlib.NumberTheory.Bernoulli`. The finite range `Finset.range (n + 1)`
represents the inclusive source sum `i = 0, …, n`.

Scope: this file states only the canonical general identity for `n ≥ 1`. It does
not add the even-index specialization or any `bernoulli'` convention-transformed
equivalent.
Proves `Wanted` entry `euler_bernoulli_convolution`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Bernoulli.EulerBernoulliConvolution](../../../../../sources/v2/MathlibExt.md)
- Ken Kamano, "Sums of Products of Bernoulli Numbers, Including Poly-Bernoulli Numbers," Journal of Integer Sequences 13 (2010), <https://cs.uwaterloo.ca/journals/JIS/VOL13/Kamano/kamano2.tex>. Exact source span: lines 98–104; full-file SHA-256 `79c8704d7903524fdbe7553c7794f6062710b3f2c722eceb2715401659c869d6`; span SHA-256 `c6021b742947f7d2dd79387b89f2f146c19cd8310add80520069b7eaf2103fb5`.
