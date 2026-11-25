# Certified enclosure of a computed sum

The summands `l i` are
evaluated with per-site errors `|lhat i - l i| ≤ δ i` (supplied separately), and the computed
values are accumulated into `S` with `|S - ∑ i, lhat i| ≤ E` (for rounded recursive summation,
`E = ((1 + u) ^ n - 1) * ∑ i, |lhat i|`). Then `S` lies within `E + ∑ i, δ i` of the exact
total `∑ i, l i`.
