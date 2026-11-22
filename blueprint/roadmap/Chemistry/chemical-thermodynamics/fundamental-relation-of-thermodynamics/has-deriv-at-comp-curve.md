# Has Deriv At comp curve

Chain rule along a curve of states: if the curve components have derivatives
`U'`, `V'`, `N' i` at `t0` and `S` is differentiable at the state
`(γU t0, γV t0, γN t0)`, then `S` along the curve has derivative
`∂S/∂U * U' + ∂S/∂V * V' + ∑ ∂S/∂Nᵢ * N'ᵢ` at `t0`. Proved from the Fréchet
derivative by decomposing `(U', V', N')` along the coordinate directions. For a
`FundamentalRelation`, `FundamentalRelation.differentiableAt` supplies `hS` from
`h_diff`.
