# Binomial-ratio sum equal to Fu's $\beta_n(i)$

For natural numbers `n` and `i` with `1 ≤ i < n`,

`∑_{k=2}^{n} C(n - i - 1, k - 2) / (C(n - 1, k - 1) C(k, 2)) = β_n(i)`,

where `β_n(i) = 2n (a_{n+1} - a_i) / ((n - i + 1)(n - i)) - 2 / (n - i)` is
[Fu's coefficient](../fu-s-covariances-of-the-site-frequency-spectrum/fu-beta.md), with `a_m = ∑_{k=1}^{m-1} 1/k`. In this range all
denominators are positive and no subtraction goes below `0`. Binomial coefficients are extended
by `C(u, v) = 0` for natural `v > u`, so the terms with `k > n - i + 1` vanish.
