---
article_id: af_7f3da3a983bfc356645289e9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Combinatorics.Order.FinitePosets.mirsky_dual
---

# Mirsky dual

In a finite poset max chain size equals min antichain-cover size.

## Depends on

- [Max Chain Size](max-chain-size.md)
- [Min Antichain Cover Size](min-antichain-cover-size.md)

## Proof depends on

- [Mirsky dual general](mirsky-dual-general.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Order.FinitePosets](../../../../../../sources/v2/MathlibExt.md)
- L. Mirsky, Amer. Math. Monthly 78 (1971), 876-877, DOI 10.2307/2316481. It follows from `mirsky_dual_general`; the instance `[DecidableEq α]` is unused and keeps the Wanted entry's shape.
