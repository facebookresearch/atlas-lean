---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.sylvester_coin_distinct_odd_primes
---

# Sylvester Coin Distinct Odd Primes

Sylvester coin theorem, special case: for distinct odd primes `p` and `q`, the
number of naturals not expressible as `px + qy` is `(p-1)(q-1)/2`.

Provenance: Damanvir Singh Binner, "Generalization of a Result of Sylvester
Related to the Frobenius Coin Problem", Journal of Integer Sequences 24 (2021),
Article 21.8.4, Theorem `Sylvester'` (the Special Case of Sylvester's theorem),
source lines 123–127,
<https://cs.uwaterloo.ca/journals/JIS/VOL24/Binner/binner13.tex>.
The paper attributes the general coprime statement to Sylvester (1882).
Distinct odd primes are coprime, so the count `(p-1)(q-1)/2` applies.
Proves `Wanted` entry `sylvester_coin_distinct_odd_primes`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.SylvesterCoinDistinctOddPrimes](../../../../sources/v2/MathlibExt.md)
