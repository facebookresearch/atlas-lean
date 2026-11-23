# Reduced Biot storage matrix

For finite index sets of displacement and pressure unknowns, an `n × n` matrix `Kinv` (standing
for the inverse of the stiffness matrix), an `n × m` coupling matrix `Q` and an `m × m` storage
compliance `C`, the reduced Biot storage matrix is `S = Qᵀ Kinv Q + C`.
