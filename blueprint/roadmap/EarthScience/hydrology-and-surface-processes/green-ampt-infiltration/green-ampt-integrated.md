# Green ampt integrated

Green-Ampt integrated infiltration law on an interval `[t₀, t]`. If
`F t₀ = F₀`, `F s > 0` for `s ∈ [t₀, t]`, and `F` obeys the ponded
Green-Ampt ODE `F' = K (1 + A / F)` on `[t₀, t]` with `K > 0`, `A ≥ 0`,
then integrating gives
`t - t₀ = (F t - F₀ - A log ((F t + A) / (F₀ + A))) / K`. The proof goes
through the antiderivative `G(F) = F - A log (F + A)`, whose derivative
along `F` is the constant `K`. The hypotheses are satisfiable: e.g.
`K = 1, A = 0, F s = s + 2` on `[0, 1]` meets them with `F₀ = 2`.
