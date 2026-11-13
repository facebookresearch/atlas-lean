# Compensated Bernoulli Step

The **compensated Bernoulli counting process** in `D([0,1])`: with counting increments
`ξ i ∈ {0, 1}` of success probability `p` and counting process `N k = ∑_{i<k} ξ i`,
`t ↦ (√n)⁻¹ (N ⌊n t⌋ - p ⌊n t⌋)` (counts minus compensator, diffusively scaled; see
`compensatedBernoulliStep_apply`). This is a concrete example only; it does not define a
general counting-process interface.
