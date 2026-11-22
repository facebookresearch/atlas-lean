# Has Deriv At absolute Entropy

The temperature derivative of absolute entropy is `Cp / T`: for `0 < T`, under
continuity of `Cp` on positive temperatures and integrability of `Cp t / t` on `0..T`,
`HasDerivAt (absoluteEntropy Cp trans Tt dH) (Cp T / T) T` at points `T` that are not
transition temperatures. Via Mathlib's FTC `intervalIntegral.integral_hasDerivAt_right`; the
transition sum is locally constant near such `T`.
