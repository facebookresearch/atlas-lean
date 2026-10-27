---
article_id: af_d7c57fb7d0c270f648aa0b3a
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.PrimeCounting.UniformPrimeCountingWanted.uniform_prime_counting_arithmetic_progression
---

# Uniform Prime Counting Wanted

Fix `B > 0`. Uniformly over positive moduli `q ≤ (log x) ^ B` and reduced
residue classes `b`, the number of primes `p ≤ x` congruent to `b` modulo `q`
differs from `li(x) / φ(q)` by at most `C * x * exp (-c * sqrt (log x))` for
sufficiently large `x`. The constants may depend on `B`, but not on `x`, `q`, or `b`.

The count uses `Nat.floor x` so its endpoint is inclusive. The logarithmic integral
is written explicitly as in the source, rather than using the principal-value
normalization `Real.logarithmicIntegral`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.PrimeCounting.UniformPrimeCountingWanted](../../../../../../sources/v2/WantedExt.md)
- A. Guo, *Exceptional sets for compositions involving Euler's function, the divisor-sum function and Dedekind's function*, arXiv:2608.19972v1, Lemma `siegel`, `main.tex` lines 289–295. The official arXiv source file has SHA-256 `b4996cf07cc79703901e7313202c5a795b6e5313745490e0224d3589ff2a2d07`.
