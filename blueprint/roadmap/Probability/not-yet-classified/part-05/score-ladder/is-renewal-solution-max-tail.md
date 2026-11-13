# Ladder decomposition of the maximum

For an i.i.d. integer score walk (no drift or
moment assumption), `P(M > k) = P(τ₊ < ∞, S_{τ₊} > k) + ∑_{j ≤ k} g j P(M > k - j)`, where
`g` is the ladder-height law. Proof: split `{M > k}` over the events `{τ₊ = n, S_n = j}`,
which depend on the first `n` scores; after time `n` the walk restarts independently with the
same law.
