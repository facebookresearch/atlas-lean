# Convolution as a sum over sorting fibers

Let `R` be a commutative ring and `n,m : ℕ`. Define `C_n(m) = ∑ f : Fin n → Fin m, sign(sort
f) [sort f]` in `R[S_n]`, with integer signs cast to `R`. `C_n(m) = ∑ σ ∈ S_n, |{f : Fin n →
Fin m | sort f=σ}| * sign(σ) [σ]`, with the cardinality and sign cast to `R`.
