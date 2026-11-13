# Error budget for a Lipschitz model

If the model `F` is `K`-Lipschitz on a set containing
the measured and true data, `|approx - F dMeas| ≤ εnum` and `|dMeas - dTrue| ≤ εdata`, then
`|approx - F dTrue| ≤ εnum + K * εdata`.
