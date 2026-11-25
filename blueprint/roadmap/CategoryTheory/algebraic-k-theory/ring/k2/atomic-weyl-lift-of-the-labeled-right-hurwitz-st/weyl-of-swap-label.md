# Weyl Of Swap Label

Ordered-label Weyl element `Wₐ(u) = w_{a.1,a.2}(u)` in `St(R)`.

Purpose: coefficient-carrying Weyl meaning of an ordered endpoint label,
preserving the `(a, b)` versus `(b, a)` orientation needed by `weyl_swap`.
The `Fin n` endpoints are coerced by `val` to the `ℕ` indices of
`StableSteinberg.weyl`, with distinctness transported by `Fin.ext`.
Hypotheses: `a.1 ≠ a.2` carried by the label; `[Ring R]` only, no field or
commutativity assumption. Nonclaims: no torus, cocycle, kernel, or Matsumoto
content.
