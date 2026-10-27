---
article_id: af_fe65a83b92c92e7830320e15
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.touchard_catalan_identity
---

# Touchard Catalan Identity

Touchard's Catalan identity: for every `n : Nat`, `catalan (n + 1)` equals
the finite sum over `i = 0, ..., n / 2` of `catalan i * 2 ^ (n - 2 * i) * Nat.choose n (2 * i)`.
Grounded record `jis_grounded_8d6801e19f84ccd671cecd8e`, concept `jis_dep_66a308b917e737cb196c1412`.
Frozen source `https://cs.uwaterloo.ca/journals/JIS/VOL20/Dershowitz/dersh3.tex`, lines 274-277,
file SHA-256 `f34deece6b6101298cf0abee4c3e12577a8a7db55afe76325aef6447839e0646`,
exact span SHA-256 `ba2f60f14652718c971cd41bf7b6a3f069a5e835bad930bd72a403a07d400f25`.
Finite-support normalization: the classical upper bound `floor(n/2)` is rendered in `Nat`
as `n / 2`, encoded by the explicit range `Finset.range (n / 2 + 1)`; a second JIS source
prints the finite upper bound as `floor(n/2)`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.TouchardCatalanIdentity](../../../../../../sources/v2/MathlibExt.md)
