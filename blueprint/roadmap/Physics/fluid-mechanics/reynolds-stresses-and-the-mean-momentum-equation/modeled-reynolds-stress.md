# Modeled Reynolds Stress

Boussinesq closure of the Reynolds stress per unit density in three dimensions,
`Rm = (2 k / 3) I - 2 νt S`, from the turbulent kinetic energy `k`, the eddy viscosity `νt` and
the mean rate of strain `S`. It models `𝔼[u'ᵢ u'ⱼ]` (`reynoldsStress`); the stress it exerts on
the mean flow is `-ρ Rm = 2 ρ νt S - (2 / 3) ρ k I`, tension positive. The definition is total;
the model domain is `k ≥ 0` and a symmetric trace-free `S`, and each result below assumes the
part of it that it uses.
