/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.EckartYoung

/-!
# The spectral norm and the perturbation of singular values

Two consequences of the Eckart–Young theorem in operator norm
(`EckartYoungWanted.eckartYoung_best_rank_approx_operator_norm`) for a linear map
`T : E → F` between finite-dimensional inner product spaces:

* `opNorm_eq_singularValues_zero`: the operator `2`-norm is the largest singular value,
  `‖T‖₂ = σ_0(T)` (Trefethen and Bau, *Numerical Linear Algebra*, Theorem 5.3; the case `k = 0`
  of Eckart–Young, since the only map of rank `0` is `0`).
* `abs_singularValues_sub_le`: **singular values are perfectly conditioned** (Weyl's inequality
  for singular values): `|σ_k(T) - σ_k(U)| ≤ ‖T - U‖₂` for every `k`. A perturbation of norm `ε`
  moves every singular value by at most `ε`, whatever the matrix; this is why the SVD is a
  well-conditioned problem in the sense of Trefethen–Bau, Lecture 12, in contrast with the
  eigenvalues of non-normal matrices.

Singular values are zero-indexed and `σ_k = 0` for `k ≥ dim E` (Mathlib's
`LinearMap.singularValues`).

## References

* L. N. Trefethen, D. Bau III, *Numerical Linear Algebra*, SIAM, 1997, Theorem 5.3 and
  Lecture 12.
* G. H. Golub, C. F. Van Loan, *Matrix Computations*, 4th ed., Johns Hopkins, 2013,
  Section 8.6.1.
* R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge, 2013, Section 7.3.
* H. Weyl, *Das asymptotische Verteilungsgesetz der Eigenwerte linearer partieller
  Differentialgleichungen*, Math. Ann. 71 (1912), 441–479.
-/

@[expose] public section

open MathlibExt.Analysis.InnerProductSpace.EckartYoungWanted

namespace MathlibExt.Analysis.InnerProductSpace.SingularValuePerturbation

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

-- The set of operator-norm distances from `T` to maps of rank at most `k`.
private abbrev distSet (T : E →ₗ[𝕜] F) (k : ℕ) : Set ℝ :=
  {r : ℝ | ∃ S : E →ₗ[𝕜] F, Module.finrank 𝕜 S.range ≤ k ∧
    r = ‖(T - S).toContinuousLinearMap‖}

omit [FiniteDimensional 𝕜 F] in
private lemma distSet_nonempty (T : E →ₗ[𝕜] F) (k : ℕ) : (distSet T k).Nonempty :=
  ⟨_, 0, by rw [LinearMap.range_zero, finrank_bot]; exact Nat.zero_le k, rfl⟩

omit [FiniteDimensional 𝕜 F] in
private lemma distSet_bddBelow (T : E →ₗ[𝕜] F) (k : ℕ) : BddBelow (distSet T k) :=
  ⟨0, fun _ ⟨_, _, hr⟩ => hr ▸ norm_nonneg _⟩

/-- **The spectral norm is the largest singular value** (Trefethen–Bau, Theorem 5.3):
`‖T‖₂ = σ_0(T)`. -/
theorem opNorm_eq_singularValues_zero (T : E →ₗ[𝕜] F) :
    ‖T.toContinuousLinearMap‖ = T.singularValues 0 := by
  have h := eckartYoung_best_rank_approx_operator_norm T 0
  have hset : distSet T 0 = {‖T.toContinuousLinearMap‖} := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, nonpos_iff_eq_zero,
      Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
    constructor
    · rintro ⟨S, rfl, rfl⟩
      rw [sub_zero]
    · rintro rfl
      exact ⟨0, rfl, by rw [sub_zero]⟩
  rw [← h]
  change _ = sInf (distSet T 0)
  rw [hset, csInf_singleton]

/-- One half of Weyl's inequality: `σ_k(T + U) ≤ σ_k(T) + ‖U‖₂`. -/
theorem singularValues_add_le (T U : E →ₗ[𝕜] F) (k : ℕ) :
    (T + U).singularValues k ≤ T.singularValues k + ‖U.toContinuousLinearMap‖ := by
  rw [← eckartYoung_best_rank_approx_operator_norm (T + U) k,
    ← eckartYoung_best_rank_approx_operator_norm T k]
  change sInf (distSet (T + U) k) ≤ sInf (distSet T k) + _
  rw [← sub_le_iff_le_add]
  refine le_csInf (distSet_nonempty T k) ?_
  rintro _ ⟨S, hS, rfl⟩
  rw [sub_le_iff_le_add]
  refine (csInf_le (distSet_bddBelow (T + U) k) ⟨S, hS, rfl⟩).trans ?_
  have : (T + U - S).toContinuousLinearMap =
      (T - S).toContinuousLinearMap + U.toContinuousLinearMap := by
    rw [← map_add]; congr 1; abel
  rw [this]
  exact norm_add_le _ _

/-- **Weyl's inequality for singular values** (Golub–Van Loan, Section 8.6.1): singular values
are `1`-Lipschitz in the operator norm, `|σ_k(T) - σ_k(U)| ≤ ‖T - U‖₂`. -/
theorem abs_singularValues_sub_le (T U : E →ₗ[𝕜] F) (k : ℕ) :
    |T.singularValues k - U.singularValues k| ≤ ‖(T - U).toContinuousLinearMap‖ := by
  rw [abs_sub_le_iff]
  constructor
  · have := singularValues_add_le U (T - U) k
    rw [add_sub_cancel] at this
    linarith
  · have := singularValues_add_le T (U - T) k
    rw [add_sub_cancel] at this
    have hn : ‖(U - T).toContinuousLinearMap‖ = ‖(T - U).toContinuousLinearMap‖ := by
      rw [← neg_sub, map_neg, norm_neg]
    linarith

end MathlibExt.Analysis.InnerProductSpace.SingularValuePerturbation
