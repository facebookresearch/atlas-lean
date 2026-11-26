# Kron reduction under relabelling of the interior nodes

Let `m`, `p` and `q` be finite index sets, `e : q → p` a bijection, and `A`, `B` and `D` real
matrices of sizes `m × m`, `m × p` and `p × p`, relabelled as `B'(i, k) = B(i, e(k))`,
`D'(k, l) = D(e(k), e(l))` and `j'_I = j_I ∘ e`. For all `φ_P`, `j_P` and `j_I`:

- the [Schur complements](schur-complement-reindex-interior.md) agree,
  `A - B' D'⁻¹ B'ᵀ = A - B D⁻¹ Bᵀ`;
- the reduced right-hand sides agree, `j_P - B' D'⁻¹ j'_I = j_P - B D⁻¹ j_I`;
- the reconstructed interior potentials correspond,
  `D'⁻¹ (j'_I - B'ᵀ φ_P) = (D⁻¹ (j_I - Bᵀ φ_P)) ∘ e`;
- the retained interior source terms agree, `j'_I · (D'⁻¹ j'_I) = j_I · (D⁻¹ j_I)`.

The matrix inverse is taken to be `0` for a singular matrix; the identities hold for every `D`.
