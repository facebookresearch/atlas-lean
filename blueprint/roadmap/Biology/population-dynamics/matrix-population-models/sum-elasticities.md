# Elasticities sum to one

**Elasticities sum to one** (de Kroon et al. 1986; Jones 2023, §1.9). Let `n ≥ 1` and let
`A = (a_ij)` be a nonnegative primitive `n × n` matrix (some positive power of `A` has all
entries positive), and let `lam` be its dominant eigenvalue, given by a right eigenvector `w`
(`A w = lam w`) and a left eigenvector `v` (`vᵀ A = lam vᵀ`) whose entries are all positive; by
the Perron–Frobenius theorem no other eigenvalue has such an eigenvector. Then the elasticities
`e_ij = (a_ij / lam) · v_i w_j / ⟨v, w⟩` satisfy `∑_{i,j} e_ij = 1`.

## Sources

- Jones, "Notes on Fitness Sensitivities" (2023), §§1.3, 1.4, 1.5.1, 1.8 and 1.9; de Kroon, Plaisier, van Groenendael and Caswell (1986).
