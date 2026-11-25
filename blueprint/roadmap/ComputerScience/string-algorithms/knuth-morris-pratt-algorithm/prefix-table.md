# The KMP prefix table

The prefix table of the Knuth–Morris–Pratt algorithm: an array `t = [(x₀, n₀), (x₁, n₁), (x₂, n₂), …]` where each `nᵢ` is the length of the longest proper prefix of `[x₀, x₁, …, xᵢ]` that is also a suffix of it; every stored length satisfies `nᵢ ≤ i`.
