# Error budget

Let `approx` be a computed value, and `exactMeas`, `exactTrue` the exact
outputs at the measured data `dMeas` and the true data `dTrue`. Assume the numerical error bound
`|approx - exactMeas| ≤ εnum`, the conditioning hypothesis
`|exactMeas - exactTrue| ≤ K * |dMeas - dTrue|`, and the data-uncertainty bound
`|dMeas - dTrue| ≤ εdata`. Then the total error is at most `εnum + K * εdata`.
