# Value of the spectral imaginary-power coordinate

For all `t,r : ℝ`,
`imaginaryPowerCoordinate t r = exp(((t : ℂ)*i)*(Real.log r : ℂ))`. On positive `r`, this
is `r^(it)`.

At `r=0`, the multiplier is `exp(0)=1`. At `r<0`, `Real.log r=Real.log |r|`, so the value
is `exp(i t log |r|)`.
