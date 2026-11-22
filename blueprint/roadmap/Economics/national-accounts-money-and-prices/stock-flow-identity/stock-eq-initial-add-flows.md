# Stock as initial stock plus cumulative flows and other changes

If the stock evolves by the per-period accounting
`K (t + 1) = K t + inflow t - outflow t + otherChange t` in every period `t < n`, where
`otherChange t` collects the changes recorded in period `t` outside inflows and outflows
(revaluations and other changes in volume), then after `n` periods the stock is the initial
stock plus cumulative inflows minus cumulative outflows plus cumulative other changes. This
instantiates finite-sum telescoping.
