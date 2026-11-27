# Stock as initial stock plus cumulative flows and other changes

If a stock evolves by the per-period accounting
`K(t + 1) = K(t) + inflow(t) - outflow(t) + otherChange(t)` in every period
`t < n`, where `otherChange(t)` collects the changes recorded in period `t`
outside inflows and outflows (revaluations and other changes in volume), then
after `n` periods

`K(n) = K(0) + ∑_{t<n} inflow(t) - ∑_{t<n} outflow(t) + ∑_{t<n} otherChange(t)`.
