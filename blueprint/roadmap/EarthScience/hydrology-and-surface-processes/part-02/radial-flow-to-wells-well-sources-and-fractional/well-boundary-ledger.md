# Mass and energy ledgers with well and boundary sources

On a chain of `n` cells of common volume `Δx > 0`, let `Fm 0, …, Fm n` be signed face mass fluxes,
shared by the mass and the energy ledger, the fluid crossing face `j` having specific internal
energy `ef j`, pressure `pf j` and density `ρf j > 0`, and let cell `i` have the injection rate
`qI i` at specific enthalpy `hI i` and the production rate `qP i`. Suppose every cell stores the
fluid mass `m i = φ i * ρc i` (porosity `φ i > 0`, fluid density `ρc i > 0`) and the fluid energy
`E i = m i * ec i`, with cell pressure `pc i`. One explicit step of length `dt` moves `m i` by `dt`
times the [cell rate](well-cell-rate.md) of the fluxes `Fm` and the well rates `qI i - qP i`, and
`E i` by `dt` times the cell rate of the [enthalpy fluxes](face-enthalpy-flux.md)
`Fm j * (ef j + pf j / ρf j)` and the [well energy rates](well-energy-rate.md). It changes the
total mass `Δx * ∑ i, m i` by `dt * ((Fm 0 - Fm n) + ∑ i, (qI i - qP i))`, and the total energy
`Δx * ∑ i, E i` by `dt` times the net boundary enthalpy inflow
`Fm 0 * (ef 0 + pf 0 / ρf 0) - Fm n * (ef n + pf n / ρf n)` plus `∑ i, (qI i * hI i - qP i * h i)`,
where `h i = (E i + φ i * pc i) / m i` is the enthalpy of the stored cell state. The face states
are free: the identities hold for every choice.
