# Infinite-sites mutation on a finite genealogy

Let `𝓧` be a measurable space of genealogies and `B` a finite set of branches. For a mutation
rate `r ≥ 0` and a measurable map `ℓ` sending each genealogy `x` to branch lengths
`ℓ_b(x) ≥ 0` (`b ∈ B`), the branch-mutation kernel sends `x` to the law of independent Poisson
counts `(N_b)_{b ∈ B}` with means `r ℓ_b(x)`:

`x ↦ ∏_{b ∈ B} Po(r ℓ_b(x))`, a probability measure on `ℕ^B`.

Given the genealogy `x`, branch `b` carries a Poisson number of mutation events with mean
`r ℓ_b(x)`, independently of the other branches; `r` is the mutation rate per lineage per unit
time.
