# In a prefix-feasible ledger, every battery-energy prefix is bounded

Let a mission ledger with floors `lo`, capacities `hi`, nonnegative reserves `r`, initial stocks
`s₀` and flows `flow` be
[prefix-feasible](../../classical-mechanics/flight-and-spaceflight/mission-resource-ledgers-and-burn-costs/prefix-feasible.md)
up to step `N`, and let resource `e` have the [battery flow](battery-flow.md). Then for every
`t ≤ N`,

`lo_e + r_e ≤ s₀_e + ∑_{k < t} dt_k (η_c P_{c,k} - P_{d,k} / η_d) ≤ hi_e`:

the stored energy after every prefix of the schedule, start and end included, lies between the floor
raised by the reserve and the capacity.
