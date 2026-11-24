# Finite-grid 2PL linking

Let `Z` be a finite grid with latent law
`pi : PMF Z` and ability map `zeta : Z → ℝ`, so that the latent ability law is
`pi.map zeta`. Change the ability scale by `θ ↦ A * θ + B` with `A ≠ 0`, push
the latent law forward to `(pi.map zeta).map (fun θ => A * θ + B)`, and
transform discriminations and difficulties by the 2PL rule `a ↦ a / A`,
`b ↦ A * b + B` (Weeks 2010, (7), (8a), (8b)); discriminations of any sign
are allowed. Then the observed response law of the latent mixture is
unchanged, so is the expected total score, and that score is the sum over
items of the grid averages of the item curves.
