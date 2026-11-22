# Internal Energy

Internal energy of an ideal gas with constant heat capacity `Cv`, relative to a reference
state: `U(T) = U₀ + Cv * (T - T₀)`, where `U₀` is the energy at the reference temperature `T₀`.
A constant `Cv` determines only energy differences (`internalEnergy_sub`), so the reference is
an explicit parameter; in the ideal-gas model `U` does not depend on `V`. This is the model of
`EarthScience.internalEnergy_hasDerivAt`.
