# Kurtz's law of large numbers for mass-action stochastic reaction networks

**Kurtz's law of large numbers for mass-action stochastic reaction networks** (Kurtz 1972;
Ethier–Kurtz 1986, ch. 11, §2). Let `X N` be the chain of the network `G` with mass-action
propensities `λ^N_r(z) = N κ_r ∏_s (z_s)_{(src r s)} / N^{src r s}` at system size `N`, and `x` a
solution of the deterministic mass-action system `x' = massActionField κ x`. If the scaled initial
state converges to `x(0)` in probability, then for every `T` and `ε > 0`

`P(∃ t ∈ [0, T], ‖X^N(t) / N - x(t)‖₁ ≥ ε) → 0`  as `N → ∞`.
