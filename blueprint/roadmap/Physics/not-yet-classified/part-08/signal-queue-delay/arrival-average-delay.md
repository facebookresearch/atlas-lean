# Arrival-average delay

For one clearing cycle, the arrival-weighted virtual delay over
`[0, R + G)` divided by the arrival volume `lam * (R + G)` is
`R ^ 2 * mu / (2 * (mu - lam) * (R + G))`: the normalized queue area is the mean
first-in-first-out delay of the vehicles arriving in the cycle. The area enters through the
one-cycle area formula `queueLen_integral_cycle`.
