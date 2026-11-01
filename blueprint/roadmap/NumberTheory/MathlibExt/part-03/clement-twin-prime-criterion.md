---
article_id: af_cfcf72b046dc7bcb23761bce
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.clement_twin_prime_criterion
---

# Clement Twin Primes

Clement's criterion for twin primes (source-faithful statement).

States that for a natural number `p` with `2 ≤ p`, `p` and `p + 2` are both
prime if and only if `4 * ((p - 1)! + 1) + p` is `0` modulo `p * (p + 2)`.

The `2 ≤ p` hypothesis is a required correction: the unqualified JIS
restatement is false at `p = 1`.

Source provenance (grounded ID `jis_grounded_f61a8741bce6c20e6c61e08b`):
* JIS restatement: `https://cs.uwaterloo.ca/journals/JIS/VOL13/Schmidt/multifact.tex`,
  lines 3295-3306, source SHA-256
  `0513d619381669719f263cd6f6d73963cb2ce17ba90a9ad280caff71060775f5`.
* Corrected domain: M. Chaves, `Twin Primes and a Primality Test by Indivisibility`,
  arXiv:math/0211034v3, source lines 110-121, citing P. A. Clement,
  `Congruences for Sets of Primes`, Amer. Math. Monthly 56 (1949), 23.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.ClementTwinPrimes](../../../../sources/v2/MathlibExt.md)
