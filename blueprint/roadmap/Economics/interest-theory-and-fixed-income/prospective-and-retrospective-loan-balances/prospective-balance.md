# Prospective balance of a level-payment loan

The prospective balance at date `k` of a loan repaid by `n` level payments `P` at the ends of
periods `1, …, n` is the present value at date `k`, at the per-period rate `r`, of the
remaining payments at dates `k + 1, …, n`: `P ∑_{t=1}^{n-k} (1 + r)⁻ᵗ`. It is defined for every
date `k`: for `k > n` truncated subtraction gives `n - k = 0`, so no payments remain and the
balance is `0`, as at `k = n`; the intended domain is `k ≤ n`. The discount factor uses the
convention `0⁻¹ = 0` when `r = -1`.
