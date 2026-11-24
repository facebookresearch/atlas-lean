# AUC splits into a linear and a saturation part

For a bolus of dose `V C₀` into volume
`V > 0`, the saturable AUC is the AUC of the linear model with clearance `CL = V Vmax / Km`
(`CompartmentKinetics`, value `D / CL = C₀ Km / Vmax`) plus `C₀² / (2 Vmax)`.
