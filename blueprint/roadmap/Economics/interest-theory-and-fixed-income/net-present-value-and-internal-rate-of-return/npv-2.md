# Net present value of a project's cash flows (restated)

The net present value at rate `r` of a project with cash flows `c_0, c_1, …, c_N`, where `c_0`
is paid today and `c_k` at the end of period `k`, is the present value of these flows over the
dates `0, …, N` under the constant-rate discount factors `(1 + r)⁻ᵏ`:
`NPV(r) = ∑_{k=0}^{N} (1 + r)⁻ᵏ c_k`. It is meaningful for `r > -1`; it is defined for every
real `r`, with the convention `0⁻¹ = 0`, so that `NPV(-1) = c_0`.

This is the same definition as [Net present value of a project's cash flows](npv.md). Here the terms
are written `(1 + r)⁻ᵏ c_k`; the linked page writes them `c_k / (1 + r)ᵏ`, which is equal for every
real `r`.
