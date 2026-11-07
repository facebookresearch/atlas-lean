# Natural filtration of a process

The natural filtration of a process: `𝓕^nat_t = σ(B_u : u ≤ t)`. Unlike
Mathlib's `Filtration.natural`, this is built from measurability rather than
strong measurability, which is all that is available from adaptedness.
