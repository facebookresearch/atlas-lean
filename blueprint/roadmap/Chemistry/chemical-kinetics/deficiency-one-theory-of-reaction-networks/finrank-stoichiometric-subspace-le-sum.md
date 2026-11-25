# The stoichiometric dimension is at most the sum over linkage classes

Let `N` be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
finite species set `S` and finitely many linkage classes (connected components of its
[linkage graph](../../../Dynamics/smooth-dynamics/linkage-graph.md)); the reactions and the
complexes may be infinite in number. The dimension `s` of the
[stoichiometric subspace](../../../Dynamics/smooth-dynamics/stoichiometric-subspace.md) `𝒮` is at
most the sum of the dimensions `s_θ` of the
[stoichiometric subspaces `𝒮_θ` of the linkage classes](linkage-class-stoichiometric-subspace.md):

`s = dim (∑_θ 𝒮_θ) ≤ ∑_θ dim 𝒮_θ = ∑_θ s_θ`,

where the first equality is [`𝒮 = ∑_θ 𝒮_θ`](stoichiometric-subspace-eq-i-sup.md) and all dimensions
are over `ℝ`.
