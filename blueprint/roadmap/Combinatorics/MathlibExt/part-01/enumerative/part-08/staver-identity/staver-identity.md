---
article_id: af_2a29ed2bccb5b7ef2006f2dd
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.staver_identity
---

# Staver identity

Staver's identity: for even `n`, `S¹ = (n/2) * S⁰`, and for odd `n`,
`S⁰ = 0`, where `Sᵐ = ∑_{k=0}^n (-1)^{n-k} k^m C(n,k)⁻¹`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Staver reflect one](staver-reflect-one.md)
- [Staver reflect zero](staver-reflect-zero.md)
- [Staver sign even](staver-sign-even.md)
- [Staver sign odd](staver-sign-odd.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.StaverIdentity](../../../../../../../sources/v2/MathlibExt.md)
- Renzo Sprugnoli, "Alternating Weighted Sums of Inverses of Binomial Coefficients," Journal of Integer Sequences 15 (2012), Article 12.6.3 (Staver's identity), <https://cs.uwaterloo.ca/journals/JIS/VOL15/Sprugnoli/sprugnoli6.tex>. Both parts follow by pairing `k ↔ n - k`: for odd `n` the pairs cancel, for even `n` they average to `n/2`. Proves `Wanted` entry `staver_identity`.
