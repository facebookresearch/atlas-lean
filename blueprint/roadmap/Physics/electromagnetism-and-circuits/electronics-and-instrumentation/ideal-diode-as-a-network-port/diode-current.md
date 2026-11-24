# Diode Current

Ideal Shockley diode current from anode to cathode at anode-to-cathode
voltage `V`, with saturation current `Is` and emission coefficient `n`:
`Is * (exp (V / (n * VT)) - 1)`. This reuses the exponential junction law
`EbersMollTerminalBalance.forwardBranchCurrent` with the scale `n * VT`; no second
exponential law or transport model is declared.
