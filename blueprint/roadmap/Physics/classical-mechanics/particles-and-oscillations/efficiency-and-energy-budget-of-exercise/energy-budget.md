# Energy budget identity

With fixed energy densities `rhoF`,
`rhoL` (positive), stores `F`, `L` and component fluxes `qF`, `qL`
satisfying the separate component balances in derivative form on
the integration window (`rhoF * F` has derivative `qF` and
`rhoL * L` has derivative `qL` at every `s ∈ [0, t]`), and the net
balance `qF + qL = intake - expenditure` on the window, the stored
energy `E = rhoF * F + rhoL * L` satisfies
`E t - E 0 = ∫ s in 0..t, (intake s - expenditure s)`. No
variable-density or hydration term is present in this declared model.
