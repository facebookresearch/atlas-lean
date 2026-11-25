# Competitive factor shares sum to one under the Euler identity

Let `Y = A * F(K, L)` with `A ≠ 0` and `F(K, L) ≠ 0`, and let `F_K` and `F_L` be
the derivative of `F` at `(K, L)` applied to `(1, 0)` and `(0, 1)`, the partial
derivatives (both are `0` if `F` is not differentiable at `(K, L)`). If the
Euler identity `F(K, L) = K * F_K + L * F_L` holds at `(K, L)`, the factor
shares at the marginal-product prices `A * F_K` and `A * F_L` sum to one:

`A * F_K * K / Y + A * F_L * L / Y = 1`.

Constant returns to scale imply the Euler identity, but the pointwise identity
is weaker: `F(K, L) = K ^ 2 + 1` satisfies it at `(1, 1)` without having
constant returns. No differentiability hypothesis is needed: if `F` were not
differentiable at `(K, L)`, both partial derivatives would be `0` and the Euler
identity would force `F(K, L) = 0`.
