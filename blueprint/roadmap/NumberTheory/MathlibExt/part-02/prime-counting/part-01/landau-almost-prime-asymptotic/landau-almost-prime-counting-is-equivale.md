---
article_id: af_74351076c9d3afeefe290d83
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.landau_almostPrimeCounting_isEquivalent
---

# Landau almost Prime Counting is Equivalent

Landau's theorem on `k`-almost primes: the counting function
`almostPrimeCounting k x` is asymptotically equivalent to
`x * (log log x) ^ (k - 1) / ((k - 1)! * log x)`.

## Depends on

- [Almost Prime Counting](almost-prime-counting.md)

## Proof depends on

- [Theta is Equivalent of prime Counting is Equivalent](../chebyshev/theta-is-equivalent-of-prime-counting-is.md)
- [Prime Number Theorem](../../../../part-09/prime-number-theorem.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.PrimeCounting.LandauAlmostPrimeAsymptotic](../../../../../../../sources/v2/MathlibExt.md)
- Rafael Jakimczuk, "Functions of Slow Increase and Integer Sequences," Journal of Integer Sequences 13 (2010), `https://cs.uwaterloo.ca/journals/JIS/VOL13/Jakimczuk/jakimczuk8.tex`, lines 451-453, file SHA256 `b4a7154095398fc4a1729bef9ec80c4005190c1d9ad1dd585fbd2fcdd1eae8d7`, text SHA256 `4af87d665e5485d49e794b3927864d50a1162127411c1427d0f1a379b50b2065`, module `WantedExt.NumberTheory.PrimeCounting.LandauAlmostPrimeAsymptoticWanted`.
