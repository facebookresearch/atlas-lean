---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: CDIS.isUniform_subgraph
---

# Uniform law on the subgraph of a density

CDIS id 97, the basis of the rejection method. If `X` has density `f` and `U` is uniform
 on `]0,1[` and independent of `X`, then `(X, U f(X))` is uniform on
 `A_f = {(x, y) | 0 ≤ y ≤ f(x)}`. Proof: both laws agree on rectangles `s × t`, by
 `f(x) · P(U f(x) ∈ t) = ℓ(t ∩ [0, f(x)])`.

## Depends on

- [Uniform law](uniform-law.md)

## Sources

- [Probabilités V, Loi uniforme sur le sous-graphe d'une densité](../../sources/cdis-probabilites-v.md)
