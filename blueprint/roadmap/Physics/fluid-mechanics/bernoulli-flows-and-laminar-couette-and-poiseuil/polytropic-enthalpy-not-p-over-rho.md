# Polytropic enthalpy not p Over Rho

The enthalpy hypothesis is not automatic: a compressible-gas enthalpy
`(7 / 2) p / ρ` is not of the form `p / ρ + e₀`, so
`bernoulliFunction_along_streamline` cannot be applied to this fixture without
checking the hypothesis. (Along each circular streamline of the fixture the
Bernoulli function is nevertheless constant, since pressure, enthalpy, kinetic
energy and potential are each constant there; this example shows the hypothesis
must be checked, not that constancy fails without it.)
