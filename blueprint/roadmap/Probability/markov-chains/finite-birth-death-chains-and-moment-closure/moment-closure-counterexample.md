# Mean-field moment closure is not exact for a nonlinear activation

Take `N = 2` and the activation `f(x) = (x / 2)²`, so that the birth rate in state `i` is
`(2 - i) f(i)`, and the [witness law](moment-witness.md) `w`, half mass at `0` and half at `2`. Then
the mean birth rate `∑_i w(i) (2 - i) (i / 2)²` is `0`, the mean state `∑_i w(i) i` is `1`, and
the mean-field closure value at the mean state, `(2 - 1) (1 / 2)² = 1 / 4`, differs from it:
replacing the mean of the rate by the rate at the mean is not exact.
