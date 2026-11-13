# Expected number of segregating sites

Infinite-sites mutation at rate `θ/2` per lineage per unit time: if the number of
segregating sites `S` is integrable and has conditional mean `(θ/2) L` given the genealogy
σ-algebra `m`, then `E S = θ H_{n-1}`. (Integrability matters: Mathlib's conditional
expectation of a non-integrable function is `0`.)
