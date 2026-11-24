# Explicit remainder of the first-order linearization

Let `f : ℝ^ι → ℝ` have derivative `f' y` at every point `y` of the box `[lo, hi]` (`lo ≤ y ≤ hi`
componentwise), and let `f'` have derivative `f'' y` there, with `‖f'' y‖ ≤ H` on the box. For `x`
and `x + h` in the box, the error of the first-order Taylor linearization is
`|f (x + h) - f x - f' x h| ≤ 1 / 2 * H * ‖h‖ ^ 2`. The norm on `ℝ^ι` is the sup norm and `‖f'' y‖`
is the corresponding operator norm. The bound follows from the mean value inequality applied to `f'`
and a comparison argument along the segment from `x` to `x + h`. (Remark beyond the statement: the
constant `1 / 2` is attained by quadratic functions.)
