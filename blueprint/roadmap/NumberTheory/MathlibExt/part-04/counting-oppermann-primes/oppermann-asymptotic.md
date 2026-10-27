---
article_id: af_19bae4bb8b57e506cce16a15
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.oppermannAsymptotic
---

# Oppermann Asymptotic

Asymptotic main term `n / (2 log n)` for the Oppermann prime counts.

Concept `jis_sem_b1c5531b893b694777f2c1c5` (counting Oppermann primes),
source statement `jis_6984ebbf83b6eb73fb1b156d`: the shared asymptotic for
both Oppermann intervals. `Real.log n = 0` at `n = 0, 1`, so the term is
junk-valued there; this is invisible to the `atTop` asymptotic.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.CountingOppermannPrimes](../../../../../sources/v2/MathlibExt.md)
