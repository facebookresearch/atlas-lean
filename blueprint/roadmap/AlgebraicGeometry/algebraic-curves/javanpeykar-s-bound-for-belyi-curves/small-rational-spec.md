# The rational numbers `aₙ`

Let `a₁ = 1 / 2` and `aₙ = n / (2n - 1)` for `n ≥ 2`. Then for
every `n ≥ 1`, `1 / 2 ≤ aₙ ≤ 2 / 3` and `h_naive(aₙ) ≤ log(2n)`, where
`h_naive(p / q) = log max(|p|, |q|)` for coprime integers `p, q` with `q > 0` (here
`Height.logHeight₁`, see `Rat.logHeight₁_eq_log_max`). Moreover the `aₙ` are pairwise distinct.

A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number
Theory 8 (2014), proof of Theorem 4.5.2, p. 122, with `h_naive` as defined before
Theorem 4.5.1, p. 120.
