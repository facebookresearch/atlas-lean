# Total of independent Poisson branch counts is conditionally Poisson

Let `μ` be an s-finite measure on `Ω`, let `X` be a random genealogy with values in a measurable
space `𝓧`, let `B` be a finite set of branches, `r ≥ 0` a mutation rate and `ℓ` a measurable map
sending each genealogy `x` to branch lengths `ℓ_b(x) ≥ 0`. Let `N = (N_b)_{b ∈ B}` be branch counts
whose conditional law given `X` is the [branch-mutation kernel](branch-mutation-kernel.md): the
joint law of `(X, N)` is the law of `X` composed with the kernel `x ↦ ∏_b Po(r ℓ_b(x))`. Then the
total `∑_{b ∈ B} N_b` has conditional law

`Po(r ∑_{b ∈ B} ℓ_b(X))` given `X`.
