---
article_id: af_62133ace502dd45353b9e2db
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.NumberTheory.BreuschWanted.ramanujan_two_primes_between
---

# Ramanujan Two Primes

Ramanujan's two-primes refinement of Bertrand's postulate: for `n ≥ 6`
there are two distinct primes in the open interval `(n, 2 * n)`.

For `n ≥ 48`, this follows by applying `breusch_prime_interval` at `n` and
`9n/8`. The remaining finite range is checked by kernel reduction.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Breusch prime interval](breusch-2/breusch-prime-interval.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.PrimeInterval.RamanujanTwoPrimes](../../../../../sources/v2/MathlibExt.md)
- Nathaniel Benjamin, Grant Fickes, Eugene Fiorini, Edgar Jaramillo Rodriguez, Eric Jovinelly, and Tony W. H. Wong, "Primes and Perfect Powers in the Catalan Triangle", Journal of Integer Sequences 22 (2019), Article 19.7.6, proof sentence at line 153 (inside the proof of the theorem labeled `c_nn not power`), attributed there to Ramanujan, <https://cs.uwaterloo.ca/journals/JIS/VOL22/Fiorini/fiorini3.tex>.
