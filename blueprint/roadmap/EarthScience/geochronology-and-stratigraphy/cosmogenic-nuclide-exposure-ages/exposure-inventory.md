# Cosmogenic nuclide inventory under constant production

The nuclide inventory after an exposure time `t`, with constant production rate `P`, decay
constant `λ` and inherited inventory `N0`:
`N(t) = N0 * exp (-λ * t) + (P / λ) * (1 - exp (-λ * t))`. It is defined for all real `P`, `λ`,
`N0` and `t`; with the convention `x / 0 = 0`, at `λ = 0` it is the constant `N0` (not the
zero-decay inventory `N0 + P * t`). The intended domain is `P > 0`, `λ > 0`, `N0 ≥ 0` and
`t ≥ 0`.
