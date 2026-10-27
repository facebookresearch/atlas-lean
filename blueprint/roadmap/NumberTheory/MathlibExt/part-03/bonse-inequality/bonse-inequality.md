---
article_id: af_1c99b5e10e7c0ae084eb5bf2
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.bonse_inequality
---

# Bonse inequality

Bonse's inequality: for `k > 4`, the square of the `(k+1)`-st prime is
smaller than the product of the first `k` primes.

`Nat.nth Prime` is zero-indexed, so `Nat.nth Prime k` is the source's
one-indexed `p_{k+1}` and the product over `Finset.range k` is
`p_1 * ... * p_k`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Bonse nth five](bonse-nth-five.md)
- [Bonse nth strict Mono](bonse-nth-strict-mono.md)
- [Bonse nth succ lt](bonse-nth-succ-lt.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.BonseInequality](../../../../../sources/v2/MathlibExt.md)
- Robert J. Betts, "Using Bonse's Inequality to Find Upper Bounds on Prime Gaps," Journal of Integer Sequences 10 (2007), Article 07.3.8, Proposition [Bonse's inequality] (label prop1), lines 142–148, <https://cs.uwaterloo.ca/journals/JIS/VOL10/Betts/betts7.tex>. Proves `Wanted` entry `bonse_inequality`.
