# Competitive shares sum to one

Under competitive pricing (factor prices
equal to the marginal products `A * F_K` and `A * F_L`) AND the pointwise Euler
identity `hEuler : F (K, L) = K * F_K + L * F_L` at `(K, L)` (an explicit
hypothesis), the two factor shares sum to 1. Constant returns
imply `hEuler`, but the pointwise identity is strictly weaker: `F (K, L) = K ^ 2 + 1`
satisfies it at `(1, 1)` without having constant returns. No separate
differentiability hypothesis is needed: if `F` were not differentiable at
`(K, L)`, `fderiv` would be `0` and `hEuler` would force `F (K, L) = 0`,
contradicting `hF0`.
