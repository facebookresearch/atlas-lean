# Total of independent Poisson branch counts is conditionally Poisson

Let `μ` be an s-finite measure on `Ω`, let `X` be a function from `Ω` to a measurable space `𝓧` of
genealogies, let `B` be a finite set of branches, `r ≥ 0` a mutation rate and `ℓ` a measurable map
sending each genealogy `x` to branch lengths `ℓ_b(x) ≥ 0`. Let `N = (N_b)_{b ∈ B}` be natural-number
branch counts on `Ω` whose conditional law given `X` is the
[branch-mutation kernel](branch-mutation-kernel.md): the pair `(X, N)` is `μ`-almost everywhere
measurable, and the image of `μ` under `(X, N)` is the composition product of the image of `μ` under
`X` with the kernel `x ↦ ∏_b Po(r ℓ_b(x))` (these image measures need not be probability measures).
Then the total `∑_{b ∈ B} N_b` has, in the same sense, conditional law

`Po(r ∑_{b ∈ B} ℓ_b(X))` given `X`.
