# A finite filter scales a complex exponential by its frequency response

For complex filter coefficients `h_0, …, h_{n-1}` and real `ω` and `t`,
`∑_{k < n} h_k exp(2π i ω (t - k)) = H(ω) exp(2π i ω t)`, where
`H(ω) = ∑_{k < n} h_k exp(-2π i ω k)` is the frequency response: the finite impulse response
filter with these coefficients maps the input `t ↦ exp(2π i ω t)` to the same input scaled by
`H(ω)`.
