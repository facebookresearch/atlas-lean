/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.InnerProductSpace.RieszBasisStability

/-!
# Tests for Riesz bases and Paley–Wiener stability

The perturbed orthonormal basis of `ℂ²` given by
`f i = b i + (1 / 4) • b (i + 1)` is a Riesz basis: the total squared
perturbation is `2 * (1 / 4) ^ 2 = 1 / 8 < 1`. The constant family
`fun _ => b 0` is not a Riesz basis. The same stability argument works in
infinite dimensions: perturbing only the `0`-th vector of the standard
Hilbert basis of `ℓ²(ℕ, ℂ)` gives a Riesz basis.
-/

namespace MathlibExtTest.Analysis.InnerProductSpace.RieszBasisTests

open scoped lp _root_.InnerProductSpace
open MathlibExt.Analysis.InnerProductSpace.RieszBasis
open MathlibExt.Analysis.InnerProductSpace.RieszBasisStability

/-- The standard Hilbert basis of `ℂ²`, via the Euclidean orthonormal basis. -/
private noncomputable abbrev basis2 : HilbertBasis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)) :=
  (EuclideanSpace.basisFun (Fin 2) ℂ).toHilbertBasis

/-- The perturbed basis of `ℂ²`: each basis vector is tilted towards the next
one by `1 / 4`. -/
private noncomputable def pert2 : Fin 2 → EuclideanSpace ℂ (Fin 2) :=
  fun i => basis2 i + (1 / 4 : ℂ) • basis2 (i + 1)

/-- The total squared perturbation of `pert2` is `1 / 8 < 1`. -/
private theorem pert2_tsum_lt_one :
    ∑' i : Fin 2, ‖pert2 i - basis2 i‖ ^ 2 < 1 := by
  rw [tsum_fintype, Fin.sum_univ_two]
  have hnorm : ∀ i : Fin 2, ‖pert2 i - basis2 i‖ = 1 / 4 := by
    intro i
    have hsub : pert2 i - basis2 i = (1 / 4 : ℂ) • basis2 (i + 1) := by
      simp [pert2, add_sub_cancel_left]
    rw [hsub, norm_smul]
    have hb : ‖basis2 (i + 1)‖ = 1 := by
      have hco : (basis2 : Fin 2 → EuclideanSpace ℂ (Fin 2))
          = EuclideanSpace.basisFun (Fin 2) ℂ := by
        exact OrthonormalBasis.coe_toHilbertBasis _
      rw [hco]
      exact (EuclideanSpace.basisFun (Fin 2) ℂ).norm_eq_one _
    rw [hb, mul_one]
    norm_num
  rw [hnorm 0, hnorm 1]
  norm_num

/-- The perturbed basis of `ℂ²` is a Riesz basis, by Paley–Wiener stability. -/
theorem pert2_isRieszBasis : IsRieszBasis basis2 pert2 := by
  refine isRieszBasis_of_tsum_norm_sq_lt_one basis2 pert2 ?_ pert2_tsum_lt_one
  exact summable_of_ne_finset_zero (s := Finset.univ)
    fun i hi => absurd (Finset.mem_univ i) hi

/-- A Riesz basis is linearly independent: the perturbed basis of `ℂ²`. -/
example : LinearIndependent ℂ pert2 :=
  pert2_isRieszBasis.linearIndependent

/-- A Riesz basis has dense span: the perturbed basis of `ℂ²`. -/
example : (Submodule.span ℂ (Set.range pert2)).topologicalClosure = ⊤ :=
  pert2_isRieszBasis.dense_span

/-- The perturbed basis of `ℂ²` has a biorthogonal dual with reconstruction. -/
example :
    ∃ g : Fin 2 → EuclideanSpace ℂ (Fin 2),
      ⟪pert2 0, g 0⟫_ℂ = 1 ∧ ⟪pert2 0, g 1⟫_ℂ = 0 ∧
        ∀ x, HasSum (fun i => ⟪g i, x⟫_ℂ • pert2 i) x := by
  obtain ⟨g, hg, hrec⟩ := pert2_isRieszBasis.exists_dual
  exact ⟨g, by simpa using hg 0 0, by simpa using hg 0 1, hrec⟩

/-- The constant family `fun _ => b 0` is not a Riesz basis: a bounded
invertible operator cannot identify two distinct basis vectors. -/
example : ¬ IsRieszBasis basis2 (fun _ => basis2 0) := by
  rintro ⟨T, hT⟩
  have h01 : basis2 (0 : Fin 2) = basis2 (1 : Fin 2) :=
    T.injective (by rw [hT 0, hT 1])
  have h0 : ⟪basis2 (0 : Fin 2), basis2 (1 : Fin 2)⟫_ℂ = 0 :=
    basis2.orthonormal.inner_eq_zero (by decide)
  rw [h01] at h0
  have h1 : ⟪basis2 (1 : Fin 2), basis2 (1 : Fin 2)⟫_ℂ = 1 := by
    have h := orthonormal_iff_ite.mp basis2.orthonormal 1 1
    rw [ite_eq_left rfl] at h
    exact h
  rw [h1] at h0
  exact one_ne_zero h0

/-- The standard Hilbert basis of `ℓ²(ℕ, ℂ)`. -/
private noncomputable abbrev basisNat : HilbertBasis ℕ ℂ ℓ²(ℕ, ℂ) :=
  ⟨LinearIsometryEquiv.refl ℂ _⟩

/-- Perturb only the `0`-th vector of the standard Hilbert basis of
`ℓ²(ℕ, ℂ)`, tilting it towards the `1`-st vector by `1 / 4`. -/
private noncomputable def pertNat : ℕ → ℓ²(ℕ, ℂ) :=
  fun i => basisNat i + (if i = 0 then (1 / 4 : ℂ) • basisNat 1 else 0)

/-- The perturbed basis of `ℓ²(ℕ, ℂ)` is a Riesz basis: only one term of the
perturbation is nonzero, and its squared norm is `1 / 16 < 1`. -/
theorem pertNat_isRieszBasis : IsRieszBasis basisNat pertNat := by
  apply isRieszBasis_of_tsum_norm_sq_lt_one basisNat pertNat
  · apply summable_of_ne_finset_zero (s := {0})
    intro i hi
    simp only [Finset.mem_singleton] at hi
    have hsub : pertNat i - basisNat i = 0 := by
      simp [pertNat, hi]
    rw [hsub]
    simp
  · have hsingle : ∀ i : ℕ, ‖pertNat i - basisNat i‖ ^ 2
        = if i = 0 then (1 / 16 : ℝ) else 0 := by
      intro i
      by_cases hi : i = 0
      · subst hi
        have hsub : pertNat 0 - basisNat 0 = (1 / 4 : ℂ) • basisNat 1 := by
          simp [pertNat]
        rw [hsub, norm_smul]
        have hb : ‖basisNat 1‖ = 1 := basisNat.orthonormal.norm_eq_one 1
        rw [hb, mul_one]
        norm_num
      · have hsub : pertNat i - basisNat i = 0 := by
          simp [pertNat, hi]
        rw [hsub]
        simp [hi]
    calc ∑' i, ‖pertNat i - basisNat i‖ ^ 2
          = ∑' i : ℕ, (if i = 0 then (1 / 16 : ℝ) else 0) := tsum_congr hsingle
      _ = 1 / 16 := by
          simp [tsum_eq_single 0 (fun j hj => ite_eq_right hj)]
      _ < 1 := by norm_num

end MathlibExtTest.Analysis.InnerProductSpace.RieszBasisTests
