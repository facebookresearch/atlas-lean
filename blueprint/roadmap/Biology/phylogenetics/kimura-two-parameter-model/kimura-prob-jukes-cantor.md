# Equal parameters give the Jukes–Cantor matrix

For all real `μ` and `t`, the [Kimura matrix](kimura-prob.md) with equal transition and transversion
parameters `a = b = μ t / 3` is the [Jukes–Cantor matrix](../jukes-cantor-model/jc-prob.md):
`T(μ t / 3, μ t / 3)` has entries `1/4 + 3/4 · e^(-4μt/3)` on the diagonal and
`1/4 - 1/4 · e^(-4μt/3)` off it. As a matrix identity it holds for all real `μ` and `t`; it is a
transition probability matrix when `μ t ≥ 0`.
