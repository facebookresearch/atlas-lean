# Layered Effective Conductivity

Effective hydraulic conductivity for `n` ordered Darcy layers
in series: the total thickness divided by the summed layer
resistances `L i / K i`. Layers are indexed in flow order
`0, ..., n - 1`. This records the series effective conductivity
implied by a supplied common steady Darcy flux and continuous
interface heads satisfying the per-layer drop law below; it does
not derive Darcy's constitutive law.

The physical effective-conductivity reading is for positive
layer conductivities, the regime of the theorems below. As a
raw real quotient the definition is totalized outside that
regime: with a zero-conductivity layer the displayed value is
not `0` and has no physical meaning here (an impermeable
layer in series is outside the domain of this formula, since
Lean totalizes division by zero).
