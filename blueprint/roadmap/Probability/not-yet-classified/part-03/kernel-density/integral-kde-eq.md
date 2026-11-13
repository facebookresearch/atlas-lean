# Expectation of the kernel density estimator

If `X 0, …, X (n-1)` (`n ≥ 1`) each have
law `f(x) dx` for a measurable, nonnegative density `f` bounded above by `B`, and `K` is a
measurable integrable kernel, then for `h > 0` and every `t`,
`E[kde K h X t] = ∫ K(u) f(t - h u) du`. Independence is not needed, and neither are
continuity of `f`, `K ≥ 0` or `∫ K = 1`.
