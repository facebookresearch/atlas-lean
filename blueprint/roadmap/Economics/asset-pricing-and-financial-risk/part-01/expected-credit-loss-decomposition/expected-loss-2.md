# Expected credit loss on a default event

For a measure `μ` (in use, a probability measure), a default event `D` and real functions
`EAD` (exposure at default) and `LGD` (loss given default), the expected loss is
`∫ 1_D EAD LGD dμ`: the expected value of `EAD(ω) · LGD(ω)` on `D`, and `0` outside `D`. It is
`0` when `1_D · EAD · LGD` is not integrable, by the convention for the integral of a
non-integrable function.
