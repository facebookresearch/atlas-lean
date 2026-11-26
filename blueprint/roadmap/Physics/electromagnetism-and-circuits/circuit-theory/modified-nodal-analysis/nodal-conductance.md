# Nodal conductance matrix

For a real `n × m` matrix `B`, a set `R` of branches and resistance values `(R_e)`, the nodal
conductance matrix is `B_R diag(1 / R_e : e ∈ R) B_Rᵀ`, with `B_R` the
[resistor incidence](resistor-incidence.md). With the convention `0⁻¹ = 0`, a branch with `R_e = 0`
contributes conductance `0`; the intended domain is `R_e > 0`, as in the
[stamping hypotheses](satisfies-stamping-hypotheses.md).
