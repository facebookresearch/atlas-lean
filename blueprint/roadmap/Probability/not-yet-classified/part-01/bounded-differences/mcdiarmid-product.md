# Mcdiarmid product

McDiarmid's bounded-differences inequality on a finite product
space with non-identical marginals (one-sided form): if changing one
coordinate of `f` changes its value by at most `c i`, then the upper
tail of `f` around its mean is sub-Gaussian with variance proxy
`(∑ i, c i ^ 2) / 4`: the MGF bound is `exp (s ^ 2 * V / 8)` with
`V = ∑ i, c i ^ 2`, which under Mathlib's sub-Gaussian convention
`exp (σ ^ 2 * s ^ 2 / 2)` is the variance proxy `V / 4`. The mean and
the tail probability are written with the product weights
`∏ i, p i (x i)`.
