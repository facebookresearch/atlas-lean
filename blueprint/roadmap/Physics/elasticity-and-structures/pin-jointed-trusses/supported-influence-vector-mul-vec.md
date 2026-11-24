# Supported influence Vector mul Vec

The influence vector solves the unit-load system: for
positive-definite supported stiffness, `K *ᵥ eta = aout`, where `eta`
is `influenceVector` for the fixed output `aout`. Later use takes
this solve equation for the one precomputed vector and forms no
further inverse.
