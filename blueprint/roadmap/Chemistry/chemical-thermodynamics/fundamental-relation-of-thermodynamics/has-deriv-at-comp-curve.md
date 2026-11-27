# Chain rule for entropy along a curve of states

Chain rule along a curve of states `t ↦ (U(t), V(t), N(t))`: if the components have derivatives
`U'`, `V'` and `N'ᵢ` at `t0` and `S` is differentiable at the state of the curve at `t0`, then `S`
along the curve has derivative `∂S/∂U * U' + ∂S/∂V * V' + ∑ ∂S/∂Nᵢ * N'ᵢ` at `t0`, the partial
derivatives taken at that state. This follows from the Fréchet derivative by decomposing
`(U', V', N')` along the coordinate directions. For a fundamental relation, `S` is differentiable at
every state of the domain.
