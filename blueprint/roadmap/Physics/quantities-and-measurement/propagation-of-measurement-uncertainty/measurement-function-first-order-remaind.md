# Explicit remainder of the first-order linearization

Let `f` have derivative `f' y` at
every point `y` of the box `Set.Icc lo hi`, and let `f'` have derivative `f'' y` there, with
`‖f'' y‖ ≤ H` on the box. For `x` and `x + h` in the box, the error of the first-order Taylor
linearization is `|f (x + h) - f x - f' x h| ≤ 1 / 2 * H * ‖h‖ ^ 2`. The norm on `ι → ℝ` is the
sup norm and `‖f'' y‖` is the corresponding operator norm. The constant `1 / 2` is attained by
quadratic functions. The proof applies Mathlib's mean value inequality
`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` to `f'` and the comparison theorem
`image_norm_le_of_norm_deriv_right_le_deriv_boundary` along the segment from `x` to `x + h`.
