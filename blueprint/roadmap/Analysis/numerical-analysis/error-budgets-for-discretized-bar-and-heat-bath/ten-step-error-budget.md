# Ten-step error budget of a computed temperature sequence

For real numbers `C`, `G`, `T_amb` and `Δ` and a real sequence `Y`, the budget is
`(9/10)^10 |Y_0 - (T_amb + Δ)| + ∑_{j=0}^{9} (9/10)^{9-j} |η_j| + |Δ| / 10`, with the
[residuals](bath-euler-residual.md) `η_j` of `Y`: the propagated initial error, the weighted
residuals and the truncation term.
