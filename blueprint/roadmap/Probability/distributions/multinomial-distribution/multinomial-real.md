# Multinomial mass function

The multinomial mass function: the probability `N! / ∏ᵢ xᵢ! · ∏ᵢ pᵢ ^ xᵢ` that `N`
independent throws, landing in cell `i` with probability `pᵢ`, produce the cell counts `x`; it is
`0` unless `∑ᵢ xᵢ = N`. The formula is a polynomial in `p` and is defined for every real vector
`p`; it is a probability mass function when `p` is a probability vector
(`0 ≤ pᵢ`, `∑ᵢ pᵢ = 1`), which the normalization theorems assume. The converse does not hold
in general: for `N = 0` it is the point mass at the zero vector for every `p`, even vectors
that are not probability vectors.
