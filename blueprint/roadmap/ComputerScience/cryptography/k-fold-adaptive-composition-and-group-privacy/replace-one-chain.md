# Chains of replace-one steps

For databases $d, d' : \mathrm{Fin}\,n \to X$ and $k \in \mathbb{N}$, $d$ and $d'$ are joined by a replace-one chain of length $k$ when there are databases $d = z_0, z_1, \dots, z_k = d'$ with $z_i$ and $z_{i+1}$ [replace-one adjacent](../differential-privacy/replace-one.md) for each $i < k$. The chain has exactly $k$ steps; since replace-one adjacency is reflexive, some steps may leave the database unchanged.
