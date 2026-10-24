---
article_id: af_8352e2f4773b8fad47ffd6d0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.kaneko_bernoulli_stirling_sum
---

# Kaneko Bernoulli Stirling

Kaneko's explicit formula for poly-Bernoulli numbers in the case `k = 1`:
the `n`-th Bernoulli number equals the Stirling-number sum
`∑_{m=1}^{n+1} (-1)^{m-1} (m-1)! S(n,m-1) / m`.

Kaneko's formula carries a `(-1)^n` prefactor; at `k = 1` it cancels against
`B_n^{(1)} = (-1)^n * B_n` (from the generating series `t/(1-e^{-t})`),
leaving the stated sum for Mathlib's `bernoulli` (`B₁ = -1/2` convention).
Verified computationally for `n = 0..10`.
Proves `Wanted` entry `kaneko_bernoulli_stirling_sum`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Bernoulli.KanekoBernoulliStirling](../../../../../sources/v2/MathlibExt.md)
- Y. Hamahata and H. Masubuchi, "Special Multi-Poly-Bernoulli Numbers," Journal of Integer Sequences 10 (2007), Article 07.4.1, Theorem [Kaneko1] (label 1), lines 144–152, https://cs.uwaterloo.ca/journals/JIS/VOL10/Hamahata/hamahata3.tex citing M. Kaneko, "Poly-Bernoulli numbers," Journal de Théorie des Nombres de Bordeaux 9 (1997), 221–228.
