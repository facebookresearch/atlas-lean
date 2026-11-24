# `V' ≤ 0` for reversible Michaelis–Menten

For positive rate constants and a positive
equilibrium `cstar` (a zero of `revField`), the orbital derivative of the pseudo-Helmholtz
function `G = pseudoHelmholtz cstar` is `≤ 0` at every positive state, and it vanishes exactly
at the equilibria. This is the Horn–Jackson inequality `ReactionNetwork.helmholtzRate_nonpos`
for `mmNetwork`, whose hypothesis (complex balance of `cstar`) is detailed balance,
`revField_eq_zero_iff`.
