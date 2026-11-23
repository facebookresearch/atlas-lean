# A sum of exponential epochs stopped at a threshold epoch is `Exp(1)`

Let the epochs be
independent `T_k ~ Exp(C(k, 2))` (`piMeasure n`) and, independently, let `h ~ ν` select the epochs
`k` with `A h k`, an upward-closed set containing `n` but not `1`. If
`P(A · k) = (k - 1)(n + 1) / ((n - 1)(k + 1))` for `1 ≤ k ≤ n`, then `∑_{k : A h k} T_k` has law
`Exp(1)`. The proof compares characteristic functions: conditionally on `h` the transform is
`∏_{k : A h k} C(k, 2) / (C(k, 2) - i u)`, which `prod_ite_eq_sum_of_threshold` makes linear in
the indicators, and `sum_pairRatio_prod` sums to `1 / (1 - i u)`.
