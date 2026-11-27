# The production–decay inventory starts at its inherited value

For every real `P`, `λ` and `N0`, the production–decay formula
`N(t) = N0 * exp (-λ * t) + (P / λ) * (1 - exp (-λ * t))` takes the value `N(0) = N0`. At
`λ = 0` the formula, with the convention `x / 0 = 0`, is the constant `N0` rather than the
zero-decay solution `N0 + P * t`; the value at `t = 0` holds there because both decay factors
equal `1`.
