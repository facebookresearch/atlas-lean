# Steady vapour flux through layers in series

For a natural number `n`, layer vapour resistances `R : ℕ → ℝ` and boundary partial pressures `p_in`
and `p_out`, the steady vapour mass flux through the layers `0, …, n - 1` in series is

`g = (p_in - p_out) / ∑_{i < n} R_i`.

It is the physical steady flux when the total resistance is nonzero, in particular for positive
resistances; with the convention `u / 0 = 0` it is `0` when the total resistance vanishes. No heat
flux is involved.
