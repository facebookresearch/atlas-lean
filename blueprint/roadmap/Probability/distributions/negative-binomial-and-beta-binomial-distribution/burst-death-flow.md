# Net probability flow of the bursty production–degradation chain

The net probability flow into state `n` of the bursty production–degradation chain:
bursts arrive at rate `κ` and add `B` molecules, `B` geometric with mean `b`,
`P(B = j) = b ^ j / (1 + b) ^ (j + 1)` for `j ≥ 0`; each molecule decays at rate `γ`. A burst
of size `0` changes nothing, so state `n` is left by a burst at rate `κ P(B ≥ 1) = κ b / (1 + b)`.
The flow is `κ ∑_{m < n} p(m) P(B = n - m) + γ (n + 1) p(n + 1) - (κ b / (1 + b) + γ n) p(n)`.
