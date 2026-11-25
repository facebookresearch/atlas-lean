# Finite-horizon government budget identity, present-value form

Let government debt `B` and primary deficits `D` satisfy the debt recursion
`B(t + 1) = (1 + r) * B(t) + D(t + 1)` for every `t`, and let `1 + r ≠ 0`. Then for
every horizon `n`, initial debt plus the present value of the primary deficits of
periods `1` to `n` equals the discounted terminal debt:

`B(0) + ∑_{s=1}^{n} (1 + r) ^ (-s) * D(s) = (1 + r) ^ (-n) * B(n)`.

The terminal debt is kept, not assumed away. Rewritten as
`B(t) = (B(t + 1) - D(t + 1)) / (1 + r)`, the debt recursion is the price
recursion of an asset paying the cash flows `-D(t)`, discounted at rate `r`.
