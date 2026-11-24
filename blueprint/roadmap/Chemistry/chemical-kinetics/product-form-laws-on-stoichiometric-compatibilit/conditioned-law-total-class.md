# Multinomial law on its support

Conditioned on the total molecule count
`n = ∑_s x_s`, the product-form law with means `c > 0` is multinomial:
`π_c(x | ∑ x = n) = n! / ∏_s x_s! · ∏_s (c_s / ∑_s c_s)^{x_s}`. The equality of laws for a
fixed `n` is `conditionedLaw_totalClass_eq_multinomialReal`. With
`isReactionClosed_totalClass` this is the stationary law of a network that conserves the total
count, such as a network of unimolecular conversions `A_i ⇌ A_j`.
