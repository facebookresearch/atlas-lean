# Explicit relaxation solution of the one-box energy balance

For heat capacity `C > 0`, feedback parameter `λ > 0` and all real forcing `F` and initial
value `T0`, the function `T(t) = F / λ + (T0 - F / λ) exp(-λ t / C)` satisfies `T(0) = T0` and
is differentiable at every time `t` with `T'(t) = (F - λ T(t)) / C`, that is `C T' = F - λ T`.
