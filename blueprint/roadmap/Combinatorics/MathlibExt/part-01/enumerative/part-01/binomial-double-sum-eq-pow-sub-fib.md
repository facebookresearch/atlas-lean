---
article_id: af_938fad5a6ea77f96356b764b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.binomial_double_sum_eq_pow_sub_fib
---

# Binomial Double Sum

The binomial double sum equals a power of two minus a Fibonacci number.

`Finset.range (n / 2 + 1)` encodes the source sum over `k = 0..⌊n/2⌋`; the
inner `Finset.range (n - 2*k + 1)` sums `q = 0..n-2k`; `Nat.fib` is the
source's `F`.
Proves `Wanted` entry `binomial_double_sum_eq_pow_sub_fib`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.BinomialDoubleSum](../../../../../../sources/v2/MathlibExt.md)
- Denis Neiter and Amsha Proag, "Links Between Sums Over Paths in Bernoulli's Triangles and the Fibonacci Numbers," Journal of Integer Sequences 19 (2016), Article 16.8.3, Theorem (label theoremS2), lines 247–252, https://cs.uwaterloo.ca/journals/JIS/VOL19/Proag/proag3.tex
