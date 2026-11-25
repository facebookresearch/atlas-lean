# The depot amount is a one-compartment bolus amount

For all real `D`, `ka` and `t`, the depot amount `D * exp (-ka * t)` is the amount
`D * exp (-ka * t) + ∫₀ᵗ exp (-ka * (t - s)) * 0 ds` of the one-compartment model with elimination
rate `ka`, no input and initial amount `D`.
