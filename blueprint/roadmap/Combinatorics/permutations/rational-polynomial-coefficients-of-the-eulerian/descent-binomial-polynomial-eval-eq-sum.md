# Evaluation as a finite coefficient sum

For `n,d : ℕ`, write `P_(n,d)(X) = (1/n!) ∏ j=0,...,n-1, (X+j-d)` in `ℚ[X]`, with the empty
product equal to `1`. For `x : ℚ`, `P_(n,d)(x) = ∑ i : Fin(n+1), coeff_i(P_(n,d)) * x^i.val`.
