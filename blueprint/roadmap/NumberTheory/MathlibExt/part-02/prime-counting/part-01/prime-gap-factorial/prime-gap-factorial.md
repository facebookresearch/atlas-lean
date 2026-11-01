---
article_id: af_7c21218206af7e2b3f1c55fb
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.prime_gap_factorial
---

# Prime gap factorial

Prime gaps near `n!`: with `r` the smallest prime above `n`, any prime `p`
with `n! + 1 < p < n! + r^2` has `p - n!` prime as well.

The source's proof: a prime divisor `m` of the difference `p - n!` is
below `r`, hence at most `n`, so it divides `n!` and therefore `p`,
contradicting `p > n! + 1`. Verified computationally for `n = 0..8`.
It follows from `prime_gap_factorial_general`; the hypotheses `hr` and `hrn` are unused and
keep the source's shape.
Proves `Wanted` entry `prime_gap_factorial`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Prime gap factorial general](prime-gap-factorial-general.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.PrimeCounting.PrimeGapFactorial](../../../../../../../sources/v2/MathlibExt.md)
- Antonín Čejchan, Michal Křížek, and Lawrence Somer, "On Remarkable Properties of Primes Near Factorials and Primorials," Journal of Integer Sequences 25 (2022), Article 22.1.4, Theorem (label T1), lines 153–159, https://cs.uwaterloo.ca/journals/JIS/VOL25/Krizek/krizek3.tex
