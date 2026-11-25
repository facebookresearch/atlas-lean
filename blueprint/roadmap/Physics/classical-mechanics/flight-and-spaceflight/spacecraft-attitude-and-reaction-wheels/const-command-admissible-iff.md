# A constant wheel command is admissible iff the endpoint limits hold

Let `T ≥ 0`, `c`, `umax` and `hmax` be real numbers and `h` a real function of time with the
derivative `c` at every `t ∈ [0, T]`. Then the constant command `u(t) = c` with momentum `h` is
[admissible](wheel-admissible.md) on `[0, T]` for the limits `umax` and `hmax` exactly when

`|c| ≤ umax`, `|h(0)| ≤ hmax` and `|h(0) + c T| ≤ hmax`.

Indeed `h(t) = h(0) + c t` on `[0, T]`, and an affine function takes its largest absolute value
on `[0, T]` at an endpoint.
