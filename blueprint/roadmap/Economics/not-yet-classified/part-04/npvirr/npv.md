# Npv

Net present value at rate `r` of a project with dated cash flows `c 0, c 1, …, c N`
(`c 0` today, `c k` at the end of period `k`), as the FI01 present value over the dates
`0, …, N` (source clause: "NPV(r) = Σ_{k=0}^N c_k (1 + r)⁻ᵏ"). Meaningful for `r > -1`.
