# Generic identifiability of latent class models

Let `M(r; k_1, …, k_p)` be a latent class model and let `S_1 ⊔ S_2 ⊔ S_3` be a partition of its
observed variables into three nonempty parts, with `κ_t = ∏_{j ∈ S_t} k_j` and
`min(r, κ_1) + min(r, κ_2) + min(r, κ_3) ≥ 2r + 2`. Then there is a polynomial `Q` in the parameter
coordinates that is nonzero at some parameter point and such that the parameters are identifiable
up to label swapping at every parameter point where `Q` does not vanish (Allman–Matias–Rhodes 2009,
Theorem 4, first assertion).

The source proves it by applying Kruskal's theorem to the three variables obtained by grouping the
observed variables along the partition.

## Depends on

- [Latent Class Params](latent-class-params.md)
- [Coords](coords.md)
- [Is Identifiable At](is-identifiable-at.md)

## Proof depends on

- [Kruskal's theorem](kruskal-theorem.md)

## Sources

- E. S. Allman, C. Matias and J. A. Rhodes, "Identifiability of parameters in latent structure
  models with many observed variables", Ann. Statist. 37(6A) (2009) 3099-3132, Theorem 4 and its
  proof.
