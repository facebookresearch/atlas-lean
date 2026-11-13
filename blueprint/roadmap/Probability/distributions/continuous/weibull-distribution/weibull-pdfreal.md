# Weibull PDFReal

The density of the Weibull law with shape `k` and scale `l`:
`(k / l) (x / l)^{k-1} exp(-(x / l)^k)` for `x > 0` and `0` for `x ≤ 0`. Outside `k, l > 0` it
is totalized to `0`, matching `weibullMeasure`.
