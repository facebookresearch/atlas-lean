# Minimal siphons from `J_G`

For a [weakly reversible](../../../Dynamics/smooth-dynamics/is-weakly-reversible.md)
[network](../../../Dynamics/smooth-dynamics/reaction-network.md) (each connected component strongly
connected) on finitely many species, each of which [occurs](all-species-occur.md) in some complex,
a finite set `Z` of species is a [minimal siphon](is-minimal-siphon.md) iff it is
[inclusion-minimal](is-minimal-var-set.md) among the sets `{i : c_i ∈ P}` for `P` a minimal prime of
`J_G + ⟨c_1 ⋯ c_s⟩`, where [`J_G`](ideal-j.md) is the ideal of the reaction binomials
(Shiu and Sturmfels 2010, Theorem 3.1, second clause).

The source proves it from the [first clause](is-minimal-siphon-iff-ideal-i.md), for `I_G`: for such
networks `I_G` and `J_G` have the same radical in `ℚ[c_1, …, c_s] / ⟨c_1 ⋯ c_s⟩`, so
`I_G + ⟨c_1 ⋯ c_s⟩` and `J_G + ⟨c_1 ⋯ c_s⟩` have the same minimal primes.

## Depends on

- [Chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md)
- [Weakly reversible reaction network](../../../Dynamics/smooth-dynamics/is-weakly-reversible.md)
- [All Species Occur](all-species-occur.md)
- [Is Minimal Siphon](is-minimal-siphon.md)
- [Is Minimal Var Set](is-minimal-var-set.md)
- [Ideal J](ideal-j.md)

## Proof depends on

- [Minimal siphons from the binomial ideal `I_G`](is-minimal-siphon-iff-ideal-i.md)

## Sources

- A. Shiu and B. Sturmfels, "Siphons in chemical reaction networks", Bulletin of Mathematical
  Biology 72 (2010) 1448–1463, arXiv:0904.4529, Theorem 3.1 and its proof.
