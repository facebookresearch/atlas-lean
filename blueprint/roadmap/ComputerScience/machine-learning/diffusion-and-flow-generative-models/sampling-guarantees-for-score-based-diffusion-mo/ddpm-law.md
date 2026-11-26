# DDPM sampler laws

The laws of the DDPM sampler with step `h` and `N` steps, started at
the standard Gaussian; `s k` estimates the score at time `k h`, and step `j + 1` uses `s (N - j)`.
Only `j ≤ N` is meaningful: with natural subtraction, the steps after the `N`-th use `s 0`.
