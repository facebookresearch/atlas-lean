# Delay concat rate Latency

End-to-end delay bound through two rate-latency nodes, paying bursts only once: for cumulative flows through two nodes in sequence offering `β_{R₁,T₁}` and `β_{R₂,T₂}`, with `min R₁ R₂ > 0`, a `γ_{r,b}`-constrained input with `r ≤ min R₁ R₂` has virtual delay at most `T₁ + T₂ + b / min R₁ R₂` at every time. The bound does not depend on the order of the two nodes: with the nodes swapped it is $T_2 + T_1 + b / \min(R_2, R_1)$, the same value.
