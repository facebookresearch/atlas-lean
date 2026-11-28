# Polynomials with coefficients ±1

`P(z) = ∑_{k=1}^n ε_k z^k` with `ε_k ∈ {-1, 1}`, encoded via `Bool` (true = 1, false = -1);
the exponents are `i.val + 1` for `i : Fin n`, i.e. `1, ..., n`.
