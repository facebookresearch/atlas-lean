# Storage deficit at the end of the horizon

For required releases `R` and inflows `Q` over `n` time steps, the terminal storage deficit is the
Lindley reflected walk of all `n` deficits `dᵢ = Rᵢ - Qᵢ`: `K₀ = 0`,
`K_{k+1} = max 0 (K_k + d_k)`, evaluated at `k = n`. It is the
[storage deficit after the `n` steps](terminal-storage-deficit-eq-at-length.md), not the storage
capacity needed over the horizon, which is the [worst required storage](worst-required-storage.md).
