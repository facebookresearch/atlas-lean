---
article_id: af_97b5165ea4fac37c52e54404
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Nat.IsRough.mem_roughNumbersUpTo
---

# Mem rough Numbers Up To

Bridge of nonunit source-rough numbers bounded by `N` into Mathlib's
`Nat.roughNumbersUpTo N (k + 1)`. Note that the latter is only the positive
complement of `(k + 1)`-smoothness (some prime factor is `≥ k + 1`), not the
source predicate (every prime factor exceeds `k`).

## Depends on

- [Is Rough](is-rough.md)

## Proof depends on

- [Eq one of mem smooth Numbers](eq-one-of-mem-smooth-numbers.md)
- [Ne zero](ne-zero.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.RoughNumbers](../../../../../sources/v2/MathlibExt.md)
