# Nonnegative triples of equal mixed drift are realized with the same f4

Let `M` be a [drift model](../patterson-s-f-statistics/drift-model.md) on any measure space, with
lineage weights `w` and drift lengths `ℓ`. Let `a, b, c` be distinct edges, `α` a real number, and
`Mx, A, B` populations such that `w(Mx, ·) = α (w(A, ·) + 1_a) + (1 - α) (w(B, ·) + 1_b) + 1_c`,
where `1_e` is the indicator of edge `e`, and such that `A`, `B` and every population other than
`Mx` have weight `0` on `a`, `b` and `c` (so only `Mx` can have nonzero weight on these edges). Let
`s, t` be real numbers for which the triple `(ℓ_a + s, ℓ_b + t, ℓ_c - α² s - (1 - α)² t)`, which has
the same [mixed drift](../outgroup-f3-and-admixed-branches/mixed-drift.md) as `(ℓ_a, ℓ_b, ℓ_c)`, has
nonnegative entries. Then there is a drift model on a probability space with the same lineage
weights, with these three lengths on `a`, `b`, `c`, the same length `ℓ(e)` on every other edge `e`,
and the same value of the [f4 statistic](../patterson-s-f-statistics/f4.md) `f4(W, X; Y, Z)` for all
populations `W, X, Y, Z`.

The three lengths are therefore not identifiable whenever such a pair `(s, t) ≠ (0, 0)` exists. The
admissible pairs can reduce to `s = t = 0`: for example, `ℓ_a = ℓ_b = ℓ_c = 0` with `0 < α < 1`
forces `s = t = 0`, and the result then only returns a model with the original lengths.
