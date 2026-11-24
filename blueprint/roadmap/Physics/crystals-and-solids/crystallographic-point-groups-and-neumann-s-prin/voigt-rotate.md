# Voigt Rotate

The action of a `3 × 3` matrix `R` on a Voigt stiffness matrix `C`. The
matrix `C` encodes the rank-four elasticity tensor
`c i j k l = C (voigtIndex i j) (voigtIndex k l)`, and the action is the tensor
transformation `c' i j k l = ∑ R i a * R j b * R k c * R l d * c a b c d`,
read back in Voigt form. Neumann invariance of a stiffness matrix `C` under a
point-group element `R` is the equation `voigtRotate R C = C`.
