---
article_id: af_71f7a4d9f26efb5c150c6ffa
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.powerSum_vanishing_mod_prime
---

# Power Sum Vanishing

For a prime `p` and `e ≥ 0` with `¬ (p - 1) ∣ e` when `e ≥ 1`,
the power sum `∑_{t=1}^p t ^ e` is divisible by `p`. The `e = 0` case is
the trivial sum `p`; for `e ≥ 1` the source's proof multiplies through by
a primitive root. Although the source states the lemma for odd primes, its
remaining hypotheses make the `p = 2` case either vacuous or immediate.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.PowerSumVanishing](../../../../sources/v2/MathlibExt.md)
- Christian Ballot, "On a Congruence of Kimball and Webb Involving Lucas Sequences," Journal of Integer Sequences 17 (2014), Article 14.1.3, Lemma (label lem:char), lines 223–225, https://cs.uwaterloo.ca/journals/JIS/VOL17/Ballot/ballot7.tex Proves `Wanted` entry `powerSum_vanishing_mod_prime`.
