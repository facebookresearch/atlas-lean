# Formation Rate

For finite species `S` (`[Fintype S]`) and finite reactions `ρ` (`[Fintype ρ]`), the
species-formation function of the network in a stirred-tank reactor, with rate constants
`k (Sum.inl r)` for the true reactions `r` and `k (Sum.inr s)` for the outflow reactions
`s → 0`: `p_N(c, k)_s = ∑_{r : ρ} k_r c^{src r} (src r s - prod r s) + k_{s→0} c_s`, where
`c^{src r} = ∏_{s' : S} c_{s'} ^ (src r s')`.
