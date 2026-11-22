# NPV strictly decreases in r for nonnegative later flows (restated)

If the later cash flows are nonnegative, `c_k ≥ 0` for `1 ≤ k ≤ N`, and at least one of them
is positive (`c_0` is arbitrary), the net present value `NPV(r) = ∑_{k=0}^{N} (1 + r)⁻ᵏ c_k`,
computed with the discount factors `(1 + r)⁻ᵏ`, is strictly decreasing in the rate `r` on
`(-1, ∞)`.

This is the same statement as
[NPV strictly decreases in r for nonnegative later flows](strict-anti-on-npv.md). Here the net
present value is written with the discount factors `(1 + r)⁻ᵏ`; the linked page writes it as
`∑_{k=0}^{N} c_k / (1 + r)ᵏ`.
