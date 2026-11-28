# Mass Action Field

For a network with finite species set `S` (`[Fintype S]`) and finite reaction set `ρ`
(`[Fintype ρ]`), the mass-action vector field with rate constants `k`, using real powers:
`x ↦ ∑_{r : ρ} k r (∏_{s : S} x_s ^ (src r s)) (prod r - src r)`. It is meant for positive states
`x`.
