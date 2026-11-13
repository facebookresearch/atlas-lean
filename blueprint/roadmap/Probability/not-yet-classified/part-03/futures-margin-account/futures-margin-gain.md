# Futures Margin Gain

Cumulative zero-interest variation-margin gain over `n` settlements for a
futures position with contract multiplier `multiplier` and futures prices
`F : ℕ → ℝ`: `∑ i ∈ range n, multiplier * (F (i + 1) - F i)`. Each daily
settlement pays the multiplier times that day's price change; there is no
interest on the margin account.
