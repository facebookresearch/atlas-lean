# With V₀ = r∞ I₀, the transfer-form voltage is r∞ I₀ e^(−x/λ)

For all real `r_m`, `r_i`, `I₀` and `x`, the
[transfer-form voltage](../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/cable-voltage.md) with inlet voltage `V₀ = r∞ I₀` and inlet
current `I₀`, `r∞ I₀ cosh (x / λ) - r∞ I₀ sinh (x / λ)`, is the pure decaying exponential

`r∞ I₀ e^(-x / λ)`,

where `λ = √(r_m / r_i)` is the [length constant](../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/length-constant.md) and `r∞ = √(r_m r_i)` the [characteristic resistance](../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/char-resistance.md). The identity
`cosh u - sinh u = e^(-u)` holds for every real `u`, so no sign condition is needed (with the
conventions `√u = 0` for `u < 0` and `u / 0 = 0`, `λ` and `r∞` are defined for all real
`r_m`, `r_i`). In the model `r_m, r_i > 0`.
