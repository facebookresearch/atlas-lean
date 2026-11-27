# A momentum reserve makes every bounded wheel command admissible

Let `T ≥ 0`, `umax` and `hmax` be real numbers and `u`, `h` real functions of time such that,
at every `t ∈ [0, T]`, `h` has the derivative `u(t)` and `|u(t)| ≤ umax`. If

`|h(0)| + umax T ≤ hmax`,

then the command `u` with momentum `h` is [admissible](wheel-admissible.md) on `[0, T]` for the
limits `umax` and `hmax`. The reserve condition is sufficient, not necessary.
