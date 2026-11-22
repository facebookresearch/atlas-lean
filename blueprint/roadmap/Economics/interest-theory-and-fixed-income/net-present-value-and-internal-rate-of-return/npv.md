# Net present value of a project's cash flows

The net present value at rate `r` of cash flows `c_0, c_1, …, c_N`, where `c_0` is paid today
and `c_k` at the end of period `k`, is `NPV(r) = ∑_{k=0}^{N} c_k / (1 + r)ᵏ`. It is meaningful
for `r > -1`; it is defined for every real `r`, with the convention `x / 0 = 0`, so that
`NPV(-1) = c_0`.

This is the same definition as [Net present value of a project's cash flows (restated)](npv-2.md).
Here the terms are written `c_k / (1 + r)ᵏ`; the linked page writes them `(1 + r)⁻ᵏ c_k`, which is
equal for every real `r`.
