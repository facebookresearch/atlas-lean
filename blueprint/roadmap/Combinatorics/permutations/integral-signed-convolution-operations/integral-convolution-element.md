# The signed sorting-label convolution element

Let `R` be a commutative ring and `n,m : ℕ`. Define `C_n(m) = ∑ f : Fin n → Fin m, sign(sort
f) [sort f]` in `R[S_n]`, with integer signs cast to `R`. `integralConvolutionElement R n m`
is this finite sum, with each labeling contributing its stable-sorting permutation.
