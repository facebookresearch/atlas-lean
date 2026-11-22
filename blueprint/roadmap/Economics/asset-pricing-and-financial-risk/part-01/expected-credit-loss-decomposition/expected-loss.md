# Expected credit loss on a default event

For a measure `μ` on the outcomes `ω` (in use, a probability measure), a default event `D` and
real functions `EAD` (exposure at default) and `LGD` (loss given default), the expected loss is
`E[L] = ∫ 1_D EAD LGD dμ`, the expected value of the loss `L = 1_D · EAD · LGD`, which is
`EAD(ω) · LGD(ω)` on `D` and `0` outside `D`. It is `0` when `1_D · EAD · LGD` is not
integrable, by the convention for the integral of a non-integrable function.

This is the same definition as
[Expected credit loss on a default event (restated)](expected-loss-2.md).
