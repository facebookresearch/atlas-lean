# Le Cam's bound in KL form

Assume `∀ a, (q a) = 0 → (p a) = 0`.

Le Cam's bound in KL form: for two distributions on a finite
type, any test's two error probabilities sum to at least
`1 - √(KL / 2)` (Pinsker applied to Le Cam's two-point bound).
The decision `δ a = true` chooses `q`, and `δ a = false` chooses `p`,
so the error sum is `p[δ = true] + q[δ = false]`.
Assumes `q` dominates `p` pointwise, so `klDiv` is finite and
its real value is the KL sum.
