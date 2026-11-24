# A length change invisible to f4 when edges outnumber population pairs

Let `P` be a finite set of `n` populations, `E` a finite set of edges and `w(X, e)` any real lineage
weights. If there are more edges than pairs of distinct populations,
`n choose 2 = n (n - 1) / 2 < |E|`, then some nonzero vector `v` on the edges satisfies
`∑ e, (w(A, e) - w(B, e)) (w(C, e) - w(D, e)) v(e) = 0` for all populations `A, B, C, D`. In a drift
model with these weights and drift lengths `ℓ`, the
[f4 statistic](../patterson-s-f-statistics/f4-freq.md) is
`f4(A, B; C, D) = ∑ e, (w(A, e) - w(B, e)) (w(C, e) - w(D, e)) ℓ(e)`, so this expression is
unchanged when `ℓ` is replaced by `ℓ + t v` for any real `t`.
