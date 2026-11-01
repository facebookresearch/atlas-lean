---
article_id: af_309737fe48ef8075858be0ee
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.prime_sub_primorial_prime_of_between_consecutive_primes
---

# Prime sub primorial prime of between consecutive primes

If `q < r` are consecutive primes and a prime `p` satisfies
`primorial q + 1 < p < primorial q + r ^ 2`, then `p - primorial q` is prime.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Prime sub primorial prime of between consecutive primes general](prime-sub-primorial-prime-of-between-con.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.PrimeGapsNearPrimorials](../../../../../sources/v2/MathlibExt.md)
- Antonín Čejchan, Michal Křížek, and Lawrence Somer, "On Remarkable Properties of Primes Near Factorials and Primorials," Journal of Integer Sequences 25 (2022), Article 22.1.4, Theorem (label T3), lines 471–477, https://cs.uwaterloo.ca/journals/JIS/VOL25/Krizek/krizek3.tex It follows from `prime_sub_primorial_prime_of_between_consecutive_primes_general`; the hypotheses `hq`, `hr` and `hqr` are unused and keep the source's shape. Proves `Wanted` entry `prime_sub_primorial_prime_of_between_consecutive_primes`.
