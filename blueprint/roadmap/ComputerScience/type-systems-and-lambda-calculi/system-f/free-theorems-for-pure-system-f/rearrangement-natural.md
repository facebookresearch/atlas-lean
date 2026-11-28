# Naturality of rearrangements

For every closed `r : ∀X. List X → List X`,
mapping `f` after `r` agrees with `r` after mapping `f`: applied to arbitrary fold
arguments `n` and `c`, the two erased results are beta-convertible. This is the
syntactic analogue of Wadler's `a* ∘ r_A = r_A' ∘ a*`, for encoded lists of
arbitrary model terms.
