# Patterson's Theorem 5(2), analytic content

For `y ∈ (0, 1)`,
`y (1 - y) ∫₀¹ G_C(x, y) / (x (1 - x)) dx + a₁(y) = y`. Integrating Patterson's
Equation 14 over `t` writes the expected MRCA age at unknown ancestry as
`y (1 - y) [∫₀¹ G_C(x, y) / (x (1 - x)) dx + lim_{ε → 0⁺} G_C(1 - ε, y) / (2ε)]`,
and by `tendsto_killedGreen_one_sub_div` the second summand contributes `a₁(y)`
after multiplication by `y (1 - y)`; so this identity is his conclusion that the
expected age is `y` in scaled time (`2Ny` generations), proved here from
Theorem 4's explicit Green function. His own proof of Theorem 5(2) is a martingale
argument (Lemma 1), not formalized.
