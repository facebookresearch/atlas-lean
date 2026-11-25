# Balanced Tensor

The coequalizer of the two coefficient actions on `M ⊗ N`. It is the balanced tensor
`M ⊗_A N` when the coefficient algebra `A` is graded-commutative (`IsCommutativeCoefficient`),
since the action of `A` on the second right module is then also a left action. Without this
hypothesis the coequalizer need not compute `M ⊗_A N`; `DerivedTensorModel` requires it.
