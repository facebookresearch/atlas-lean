---
article_id: af_fe704025a87e9a5ba19eaced
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.liouville_divisor_function_identity
---

# Liouville divisor function identity

Liouville's divisor-function identity (source-shaped form): for `0 < n`, the square
of the sum of divisor counts over the divisors of `n` equals the sum of the cubes
of those divisor counts.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Liouville divisor function identity general](liouville-divisor-function-identity-gene.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.ArithmeticFunction.LiouvilleDivisorIdentity](../../../../../../sources/v2/MathlibExt.md)
- Seon-Hong Kim and Kenneth B. Stolarsky, “Translations and Extensions of the Nicomachean Identity,” Journal of Integer Sequences 27 (2024), lines 317–322, `https://cs.uwaterloo.ca/journals/JIS/VOL27/Kim/kim8.tex` (full TeX SHA-256 `787b1d5e48f218f3b44166059063c4be564a15df0ed18d8793b2aed240aecb1f`; exact quoted span SHA-256, including its terminal LF, `5b7c9a7479bb8eb08ba025ed7f94848fd6abef52db394974d3dca55292110351`). Here `d.divisors.card` is the source's divisor-count function. It follows from `liouville_divisor_function_identity_general`; the hypothesis `hn` is unused and keeps the source's shape (at `n = 0` both sides are `0`, since `Nat.divisors 0 = ∅`). Proves `Wanted` entry `liouville_divisor_function_identity`.
