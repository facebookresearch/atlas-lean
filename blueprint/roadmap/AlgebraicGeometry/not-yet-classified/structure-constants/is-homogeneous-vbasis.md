# Homogeneous `V`-basis of the Cartier module

For a formal `O_D`-module `X` over `B` and
`j : Zp2 p →+* B`, a pair `γ` of elements of the Cartier module of `X` with `γ i` in the graded
piece `i` (`X.gradedPiece j i`) for `i = 0, 1`, such that the matrix `(tangent (γ i) k)` of their
tangent vectors has unit determinant. Unlike `GradedCartierModuleData.IsHomogeneousVBasis`, it
does not ask that every element be `∑ [b i] • γ i + V y` for exactly one `b` and `y`.
