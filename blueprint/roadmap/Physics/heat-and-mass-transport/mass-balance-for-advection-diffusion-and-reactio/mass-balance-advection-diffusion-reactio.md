# Mass balance advection diffusion reaction

Mass balance: the time derivative of the signed mass
`∫ x in a..b, c t x` equals `J(t, a) - J(t, b) - k ∫ x in a..b, c t x`,
assuming differentiation under the integral sign (the derivative of the
integral is the integral of `∂ₜc`). For `a ≤ b` this is the total mass on
`[a, b]`, changing by net inflow minus decay; for `b < a` both sides are
the negatives of the balance on `[b, a]`. The decay reading needs
`0 ≤ D`, `0 ≤ k` and `0 ≤ c`.
