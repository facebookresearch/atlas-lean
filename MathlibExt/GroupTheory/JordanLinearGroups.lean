/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

namespace MathlibExt.GroupTheory.JordanLinearGroupsWanted

open scoped commutatorElement

/-- Averaging lemma: a finite-order element of a Banach algebra, all of whose
powers stay within distance 1 of the identity, is the identity. -/
private theorem jl_eq_one_of_pow {E : Type*} [NormedRing E] [NormedAlgebra ℂ E]
    [HasSummableGeomSeries E] (c : E) (m : ℕ) (hm : 0 < m)
    (hpow : c ^ m = 1) (hclose : ∀ k < m, ‖c ^ k - 1‖ < 1) : c = 1 := by
  have hmC : ((m : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hm)
  have hmR : ((m : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hm)
  have hcast : ((m : ℕ) • (1 : E)) = algebraMap ℂ E (m : ℂ) := by
    rw [← map_one (algebraMap ℂ E), ← map_nsmul, nsmul_eq_mul, mul_one]
  have hms : ((m : ℂ))⁻¹ • ((m : ℕ) • (1 : E)) = 1 := by
    rw [hcast, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hmC, map_one]
  have hdecomp : 1 - (m : ℂ)⁻¹ • (∑ k ∈ Finset.range m, c ^ k)
      = (m : ℂ)⁻¹ • (∑ k ∈ Finset.range m, (1 - c ^ k)) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range]
    rw [smul_sub, hms]
  have hSnorm : ‖∑ k ∈ Finset.range m, (1 - c ^ k)‖ < (m : ℝ) := by
    calc ‖∑ k ∈ Finset.range m, (1 - c ^ k)‖
        ≤ ∑ k ∈ Finset.range m, ‖1 - c ^ k‖ := norm_sum_le _ _
      _ < ∑ k ∈ Finset.range m, (1 : ℝ) := by
          apply Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr hm⟩
          intro k hk
          rw [Finset.mem_range] at hk
          rw [norm_sub_rev]
          exact hclose k hk
      _ = (m : ℝ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hnorm : ‖1 - (m : ℂ)⁻¹ • (∑ k ∈ Finset.range m, c ^ k)‖ < 1 := by
    rw [hdecomp, norm_smul]
    have h1 : ‖((m : ℂ))⁻¹‖ = ((m : ℝ))⁻¹ := by
      rw [norm_inv, Complex.norm_natCast]
    rw [h1]
    calc ((m : ℝ))⁻¹ * ‖∑ k ∈ Finset.range m, (1 - c ^ k)‖
        < ((m : ℝ))⁻¹ * (m : ℝ) :=
          mul_lt_mul_of_pos_left hSnorm (inv_pos.mpr (Nat.cast_pos.mpr hm))
      _ = 1 := inv_mul_cancel₀ hmR
  set P : E := (m : ℂ)⁻¹ • (∑ k ∈ Finset.range m, c ^ k) with hP
  have hU : ((Units.oneSub (1 - P) hnorm : E)) = P := by
    rw [Units.val_oneSub, sub_sub_cancel]
  have hPmul : P * (c - 1) = 0 := by
    rw [hP, smul_mul_assoc, geom_sum_mul, hpow, sub_self, smul_zero]
  have hzero : (Units.oneSub (1 - P) hnorm : E) * (c - 1) = 0 := by
    rw [hU]
    exact hPmul
  have hc : c - 1 = 0 :=
    (IsUnit.mul_right_eq_zero (Units.oneSub (1 - P) hnorm).isUnit).mp hzero
  exact sub_eq_zero.mp hc

/-- The bundled unitary commutator coerces to the product of coercions. -/
private theorem jl_unitary_commutator_coe {E : Type*} [Monoid E] [StarMul E]
    (U V : unitary E) :
    (((⁅U, V⁆ : unitary E)) : E)
      = (U : E) * (V : E) * star (U : E) * star (V : E) := by
  have hUinv : ((U⁻¹ : unitary E) : E) = star ((U : unitary E) : E) := by
    rw [← Unitary.star_eq_inv, Unitary.coe_star]
  have hVinv : ((V⁻¹ : unitary E) : E) = star ((V : unitary E) : E) := by
    rw [← Unitary.star_eq_inv, Unitary.coe_star]
  rw [commutatorElement_def]
  simp only [Submonoid.coe_mul, hUinv, hVinv]

/-- Commutator estimate: for unitaries, `‖⁅U,V⁆ - 1‖ ≤ 2 ‖U - 1‖ ‖V - 1‖`. -/
private theorem jl_norm_commutator_sub_one_le {E : Type*} [NormedRing E] [StarRing E]
    [CStarRing E] (u v : E) (hu : u ∈ unitary E) (hv : v ∈ unitary E) :
    ‖u * v * star u * star v - 1‖ ≤ 2 * ‖u - 1‖ * ‖v - 1‖ := by
  have hU : u * star u = 1 := Unitary.mul_star_self_of_mem hu
  have hV : v * star v = 1 := Unitary.mul_star_self_of_mem hv
  have hmem : star u * star v ∈ unitary E :=
    mul_mem (Unitary.star_mem hu) (Unitary.star_mem hv)
  have hid : (u * v - v * u) * (star u * star v) = u * v * star u * star v - 1 := by
    have e : (u * v - v * u) * (star u * star v)
        = (u * v * star u * star v) - (v * (u * star u) * star v) := by
      noncomm_ring
    rw [e, hU, mul_one, hV]
  calc ‖u * v * star u * star v - 1‖
      = ‖(u * v - v * u) * (star u * star v)‖ := by rw [← hid]
    _ = ‖u * v - v * u‖ :=
        CStarRing.norm_mul_coe_unitary _ ⟨star u * star v, hmem⟩
    _ ≤ 2 * ‖u - 1‖ * ‖v - 1‖ := by
        have e2 : u * v - v * u = (u - 1) * (v - 1) - (v - 1) * (u - 1) := by
          noncomm_ring
        rw [e2]
        calc ‖(u - 1) * (v - 1) - (v - 1) * (u - 1)‖
            ≤ ‖(u - 1) * (v - 1)‖ + ‖(v - 1) * (u - 1)‖ := norm_sub_le _ _
          _ ≤ ‖u - 1‖ * ‖v - 1‖ + (‖v - 1‖ * ‖u - 1‖) := by
              apply add_le_add <;> exact norm_mul_le _ _
          _ = 2 * ‖u - 1‖ * ‖v - 1‖ := by ring

section jlBridge
open scoped Matrix.Norms.L2Operator

/-- Bridge: for `g` with unitary coercion, `↑g⁻¹ = star ↑g`. -/
private theorem jl_coe_inv_eq_star (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) ℂ)
    (hg : ((g : Matrix.GeneralLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
      ∈ unitary (Matrix (Fin n) (Fin n) ℂ)) :
    (((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ)) : Matrix (Fin n) (Fin n) ℂ)
      = star (((g : Matrix.GeneralLinearGroup (Fin n) ℂ)) :
        Matrix (Fin n) (Fin n) ℂ) := by
  have h : ((g : Matrix.GeneralLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
      * star ((g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Unitary.mul_star_self_of_mem hg
  have hinv : ((((g : Matrix.GeneralLinearGroup (Fin n) ℂ)) :
      Matrix (Fin n) (Fin n) ℂ))⁻¹
        * ((((g : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
          Matrix (Fin n) (Fin n) ℂ) = 1 := by
    rw [← Matrix.coe_units_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc (((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ)) :
        Matrix (Fin n) (Fin n) ℂ)
      = ((((g : Matrix.GeneralLinearGroup (Fin n) ℂ)) :
        Matrix (Fin n) (Fin n) ℂ))⁻¹ :=
        Matrix.coe_units_inv g
    _ = ((((g : Matrix.GeneralLinearGroup (Fin n) ℂ)) :
          Matrix (Fin n) (Fin n) ℂ))⁻¹
            * ((((g : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
              Matrix (Fin n) (Fin n) ℂ)
            * star ((((g : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
              Matrix (Fin n) (Fin n) ℂ) := by
        rw [mul_assoc, h, mul_one]
    _ = star _ := by
        rw [hinv, one_mul]

/-- Bridge: the inverse also has unitary coercion. -/
private theorem jl_inv_unitary (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) ℂ)
    (hg : ((g : Matrix.GeneralLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
      ∈ unitary (Matrix (Fin n) (Fin n) ℂ)) :
    (((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ)) : Matrix (Fin n) (Fin n) ℂ)
      ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := by
  rw [jl_coe_inv_eq_star n g hg]
  exact Unitary.star_mem hg

/-- Bridge (left): left multiplication by a unitary coercion is isometric. -/
private theorem jl_norm_unitary_mul_left (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) ℂ)
    (hg : ((g : Matrix.GeneralLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
      ∈ unitary (Matrix (Fin n) (Fin n) ℂ)) (x : Matrix (Fin n) (Fin n) ℂ) :
    ‖((g : Matrix.GeneralLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
      * x‖ = ‖x‖ :=
  CStarRing.norm_coe_unitary_mul
    ⟨((g : Matrix.GeneralLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ), hg⟩ x

/-- Bridge (right): right multiplication by a unitary coercion is isometric. -/
private theorem jl_norm_unitary_mul_right (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) ℂ)
    (hg : ((g : Matrix.GeneralLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
      ∈ unitary (Matrix (Fin n) (Fin n) ℂ)) (x : Matrix (Fin n) (Fin n) ℂ) :
    ‖x * ((g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ)‖ = ‖x‖ :=
  CStarRing.norm_mul_coe_unitary x
    ⟨((g : Matrix.GeneralLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ), hg⟩

/-- Bridge: conjugation by a unitary coercion is isometric. -/
private theorem jl_norm_conj (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) ℂ)
    (hg : ((g : Matrix.GeneralLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
      ∈ unitary (Matrix (Fin n) (Fin n) ℂ)) (x : Matrix (Fin n) (Fin n) ℂ) :
    ‖((g : Matrix.GeneralLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
      * x * (((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ)) :
        Matrix (Fin n) (Fin n) ℂ)‖ = ‖x‖ := by
  have hginv : ((((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
      Matrix (Fin n) (Fin n) ℂ)
      = ((star ⟨((g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ), hg⟩ :
        unitary (Matrix (Fin n) (Fin n) ℂ)) : Matrix (Fin n) (Fin n) ℂ) := by
    rw [Unitary.coe_star]
    exact jl_coe_inv_eq_star n g hg
  have e1 : ‖((g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ) * x
        * ((star ⟨((g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
          Matrix (Fin n) (Fin n) ℂ), hg⟩ :
          unitary (Matrix (Fin n) (Fin n) ℂ)) : Matrix (Fin n) (Fin n) ℂ)‖
      = ‖((g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ) * x‖ :=
    CStarRing.norm_mul_coe_unitary _
      (star ⟨((g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ), hg⟩)
  rw [hginv, e1]
  exact jl_norm_unitary_mul_left n g hg x

/-- Bridge: distance of unitary coercions equals distance of `g⁻¹ * h` to 1. -/
private theorem jl_dist_unitary (n : ℕ)
    (g h : Matrix.GeneralLinearGroup (Fin n) ℂ)
    (hg : ((g : Matrix.GeneralLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
      ∈ unitary (Matrix (Fin n) (Fin n) ℂ)) :
    ‖((g : Matrix.GeneralLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
      - ((h : Matrix.GeneralLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)‖
      = ‖((((g⁻¹ * h : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
        Matrix (Fin n) (Fin n) ℂ) - 1‖ := by
  have hginv : ((((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
      Matrix (Fin n) (Fin n) ℂ)
      ∈ unitary (Matrix (Fin n) (Fin n) ℂ) :=
    jl_inv_unitary n g hg
  have hgg : ((((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
      Matrix (Fin n) (Fin n) ℂ)
        * ((((g : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
          Matrix (Fin n) (Fin n) ℂ) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e : ((((g⁻¹ * h : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
        Matrix (Fin n) (Fin n) ℂ) - 1
      = ((((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
        Matrix (Fin n) (Fin n) ℂ)
        * (((((h : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
          Matrix (Fin n) (Fin n) ℂ)
          - ((((g : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
            Matrix (Fin n) (Fin n) ℂ)) := by
    have e2 : ((((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
          Matrix (Fin n) (Fin n) ℂ)
            * (((((h : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
              Matrix (Fin n) (Fin n) ℂ)
              - ((((g : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
                Matrix (Fin n) (Fin n) ℂ))
        = ((((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
          Matrix (Fin n) (Fin n) ℂ)
            * ((((h : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
              Matrix (Fin n) (Fin n) ℂ)
          - (((((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
            Matrix (Fin n) (Fin n) ℂ)
            * ((((g : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
              Matrix (Fin n) (Fin n) ℂ)) := by
      noncomm_ring
    simp only [Units.val_mul]
    rw [e2, hgg]
  have enorm : ‖((((g⁻¹ * h : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
        Matrix (Fin n) (Fin n) ℂ) - 1‖
      = ‖(((h : Matrix.GeneralLinearGroup (Fin n) ℂ)) :
        Matrix (Fin n) (Fin n) ℂ)
        - (((g : Matrix.GeneralLinearGroup (Fin n) ℂ)) :
          Matrix (Fin n) (Fin n) ℂ)‖ := by
    rw [e]
    exact jl_norm_unitary_mul_left n g⁻¹ hginv _
  calc ‖((g : Matrix.GeneralLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
        - ((h : Matrix.GeneralLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)‖
      = ‖((h : Matrix.GeneralLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
        - ((g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
          Matrix (Fin n) (Fin n) ℂ)‖ := norm_sub_rev _ _
    _ = ‖((((g⁻¹ * h : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
        Matrix (Fin n) (Fin n) ℂ) - 1‖ := enorm.symm

/-- The bundled unitary commutator coerces to the GL commutator. -/
private theorem jl_coe_commutator_GL (n : ℕ)
    (g h : Matrix.GeneralLinearGroup (Fin n) ℂ)
    (U V : unitary (Matrix (Fin n) (Fin n) ℂ))
    (hU : (U : Matrix (Fin n) (Fin n) ℂ)
        = ((g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
          Matrix (Fin n) (Fin n) ℂ))
    (hV : (V : Matrix (Fin n) (Fin n) ℂ)
        = ((h : Matrix.GeneralLinearGroup (Fin n) ℂ) :
          Matrix (Fin n) (Fin n) ℂ)) :
    (((⁅U, V⁆ : unitary (Matrix (Fin n) (Fin n) ℂ))) :
      Matrix (Fin n) (Fin n) ℂ)
      = (((⁅g, h⁆ : Matrix.GeneralLinearGroup (Fin n) ℂ)) :
        Matrix (Fin n) (Fin n) ℂ) := by
  have hgU : ((g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ)
      ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := by
    rw [← hU]
    exact U.2
  have hhU : ((h : Matrix.GeneralLinearGroup (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ)
      ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := by
    rw [← hV]
    exact V.2
  rw [jl_unitary_commutator_coe, commutatorElement_def, hU, hV]
  simp only [Units.val_mul]
  rw [jl_coe_inv_eq_star n g hgU, jl_coe_inv_eq_star n h hhU]

end jlBridge

section jlTrick
open scoped MatrixOrder ComplexOrder

/-- Unitary trick: the averaged form `Q = ∑ ⋆g * g` is positive definite
and `G`-invariant. -/
private theorem jl_avg_form_posDef_invariant (n : ℕ)
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℂ)) [Finite ↥G] :
    ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.PosDef ∧
      ∀ h : ↥G, star ((((h : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
        Matrix (Fin n) (Fin n) ℂ) * Q
        * ((((h : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
          Matrix (Fin n) (Fin n) ℂ) = Q := by
  have := Fintype.ofFinite ↥G
  refine ⟨∑ g : ↥G, Matrix.conjTranspose ((((g : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
    Matrix (Fin n) (Fin n) ℂ)
      * ((((g : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
        Matrix (Fin n) (Fin n) ℂ), ?_, ?_⟩
  · have h1 : (1 : ↥G) ∈ (Finset.univ : Finset ↥G) := Finset.mem_univ 1
    rw [← Finset.add_sum_erase _ _ h1]
    have e1 : Matrix.conjTranspose (((((1 : ↥G) : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
        Matrix (Fin n) (Fin n) ℂ)
          * (((((1 : ↥G) : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
            Matrix (Fin n) (Fin n) ℂ) = 1 := by
      have h1c : (((((1 : ↥G) : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
          Matrix (Fin n) (Fin n) ℂ) = 1 := by
        simp
      rw [h1c]
      simp
    rw [e1]
    exact Matrix.PosDef.one.add_posSemidef
      (Matrix.posSemidef_sum _
        (fun i _ => Matrix.posSemidef_conjTranspose_mul_self _))
  · intro h
    have hgh : ∀ a b : ↥G, (((((a * b : ↥G) :
        Matrix.GeneralLinearGroup (Fin n) ℂ))) :
          Matrix (Fin n) (Fin n) ℂ)
        = ((((a : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
          Matrix (Fin n) (Fin n) ℂ)
          * ((((b : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
            Matrix (Fin n) (Fin n) ℂ) := by
      intro a b
      rw [Subgroup.coe_mul G a b, Units.val_mul]
    have eterm : ∀ g : ↥G, star ((((h : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
          Matrix (Fin n) (Fin n) ℂ)
            * ((Matrix.conjTranspose ((((g : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
              Matrix (Fin n) (Fin n) ℂ)
              * ((((g : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
                Matrix (Fin n) (Fin n) ℂ)))
            * ((((h : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
              Matrix (Fin n) (Fin n) ℂ)
          = star (((((g * h : ↥G) : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
            Matrix (Fin n) (Fin n) ℂ)
            * (((((g * h : ↥G) : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
              Matrix (Fin n) (Fin n) ℂ) := by
      intro g
      rw [hgh g h, star_mul, ← Matrix.star_eq_conjTranspose]
      simp only [mul_assoc]
    calc star ((((h : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
            Matrix (Fin n) (Fin n) ℂ)
              * (∑ g : ↥G, Matrix.conjTranspose ((((g : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
                Matrix (Fin n) (Fin n) ℂ)
                * ((((g : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
                  Matrix (Fin n) (Fin n) ℂ))
              * ((((h : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
                Matrix (Fin n) (Fin n) ℂ)
          = ∑ g : ↥G, star (((((g * h : ↥G) :
              Matrix.GeneralLinearGroup (Fin n) ℂ))) :
              Matrix (Fin n) (Fin n) ℂ)
              * (((((g * h : ↥G) : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
                Matrix (Fin n) (Fin n) ℂ) := by
            rw [Finset.mul_sum, Finset.sum_mul]
            exact Finset.sum_congr rfl (fun g _ => eterm g)
        _ = ∑ g : ↥G, Matrix.conjTranspose ((((g : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
              Matrix (Fin n) (Fin n) ℂ)
              * ((((g : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
                Matrix (Fin n) (Fin n) ℂ) := by
            have hre : (∑ x : ↥G, star (((((x * h : ↥G) :
                Matrix.GeneralLinearGroup (Fin n) ℂ))) :
                  Matrix (Fin n) (Fin n) ℂ)
                * (((((x * h : ↥G) : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
                  Matrix (Fin n) (Fin n) ℂ))
                = ∑ x : ↥G, Matrix.conjTranspose ((((x : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
                  Matrix (Fin n) (Fin n) ℂ)
                  * ((((x : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
                    Matrix (Fin n) (Fin n) ℂ) :=
              Fintype.sum_equiv (Equiv.mulRight h) _ _ (fun x => by
                change star (((((x * h : ↥G) :
                    Matrix.GeneralLinearGroup (Fin n) ℂ))) :
                    Matrix (Fin n) (Fin n) ℂ)
                  * (((((x * h : ↥G) : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
                    Matrix (Fin n) (Fin n) ℂ)
                  = Matrix.conjTranspose (((((x * h : ↥G) : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
                    Matrix (Fin n) (Fin n) ℂ)
                    * (((((x * h : ↥G) :
                      Matrix.GeneralLinearGroup (Fin n) ℂ))) :
                      Matrix (Fin n) (Fin n) ℂ)
                rw [← Matrix.star_eq_conjTranspose])
            exact hre

/-- Conjugation into the unitary group: a finite `G` is conjugate into `U(n)`. -/
private theorem jl_exists_conj_unitary (n : ℕ)
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℂ)) [Finite ↥G] :
    ∃ P : Matrix.GeneralLinearGroup (Fin n) ℂ,
      ∀ g : Matrix.GeneralLinearGroup (Fin n) ℂ, g ∈ G →
        ((((P * g * P⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
          Matrix (Fin n) (Fin n) ℂ)
          ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  obtain ⟨Q, hQpos, hQinv⟩ := jl_avg_form_posDef_invariant n G
  have hQnn : 0 ≤ Q := hQpos.posSemidef.nonneg
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hQnn
  have hQunit : IsUnit Q := hQpos.isUnit
  have hdetQ : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQunit
  have hdet : Q.det = star B.det * B.det := by
    rw [hB, Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]
  rw [hdet] at hdetQ
  have hdetB : IsUnit B.det := isUnit_of_mul_isUnit_right hdetQ
  obtain ⟨P, hP⟩ := (Matrix.isUnit_iff_isUnit_det B).mpr hdetB
  subst hP
  refine ⟨P, fun g hg => ?_⟩
  rw [Matrix.mem_unitaryGroup_iff']
  have hginv := hQinv ⟨g, hg⟩
  have eU : ((((P * g * P⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
      Matrix (Fin n) (Fin n) ℂ)
      = ((((P : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
        Matrix (Fin n) (Fin n) ℂ)
        * ((((g : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
          Matrix (Fin n) (Fin n) ℂ)
        * ((((P⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
          Matrix (Fin n) (Fin n) ℂ) := by
    simp only [Units.val_mul]
  have hPBi : ((((P : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
      Matrix (Fin n) (Fin n) ℂ)
        * ((((P⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
          Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Units.mul_inv P
  rw [eU, star_mul, star_mul]
  have step1 : star ((((P⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
        Matrix (Fin n) (Fin n) ℂ)
          * (star ((((g : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
            Matrix (Fin n) (Fin n) ℂ)
            * star ((((P : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
              Matrix (Fin n) (Fin n) ℂ))
          * (((((P : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
            Matrix (Fin n) (Fin n) ℂ)
            * ((((g : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
              Matrix (Fin n) (Fin n) ℂ)
            * ((((P⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
              Matrix (Fin n) (Fin n) ℂ))
        = star ((((P⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
          Matrix (Fin n) (Fin n) ℂ)
          * (star ((((g : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
            Matrix (Fin n) (Fin n) ℂ) * Q
            * ((((g : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
              Matrix (Fin n) (Fin n) ℂ))
          * ((((P⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
            Matrix (Fin n) (Fin n) ℂ) := by
    rw [hB]
    simp only [mul_assoc]
  rw [step1, hginv]
  have step2 : star ((((P⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
        Matrix (Fin n) (Fin n) ℂ) * Q
          * ((((P⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
            Matrix (Fin n) (Fin n) ℂ)
        = star (((((P : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
            Matrix (Fin n) (Fin n) ℂ)
            * ((((P⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
              Matrix (Fin n) (Fin n) ℂ))
          * (((((P : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
            Matrix (Fin n) (Fin n) ℂ)
            * ((((P⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
              Matrix (Fin n) (Fin n) ℂ)) := by
    rw [hB, star_mul]
    simp only [mul_assoc]
  rw [step2, hPBi, star_one, one_mul]

end jlTrick

/-- Transfer: the conclusion is invariant under conjugation in GL. -/
private theorem jl_of_map_conj (n J : ℕ)
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℂ))
    (φ : Matrix.GeneralLinearGroup (Fin n) ℂ →*
      Matrix.GeneralLinearGroup (Fin n) ℂ)
    (hinj : Function.Injective φ)
    (A' : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℂ))
    (hle : A' ≤ G.map φ)
    (hnorm : ∀ g ∈ G.map φ, ∀ a ∈ A', g * a * g⁻¹ ∈ A')
    (hcomm : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x)
    (hJ : A'.relIndex (G.map φ) ≤ J) :
    ∃ A : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℂ), A ≤ G ∧
      (∀ g ∈ G, ∀ a ∈ A, g * a * g⁻¹ ∈ A) ∧
      (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧
      A.relIndex G ≤ J := by
  refine ⟨A'.comap φ, ?_, ?_, ?_, ?_⟩
  · have h : A'.comap φ ≤ (G.map φ).comap φ := Subgroup.comap_mono hle
    rw [Subgroup.comap_map_eq_self_of_injective hinj] at h
    exact h
  · intro g hg a ha
    change φ (g * a * g⁻¹) ∈ A'
    have hga : φ g ∈ G.map φ := Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
    have haa : φ a ∈ A' := ha
    have hmem := hnorm (φ g) hga (φ a) haa
    have e : φ (g * a * g⁻¹) = φ g * φ a * (φ g)⁻¹ := by
      simp only [map_mul, map_inv]
    rw [e]
    exact hmem
  · intro x hx y hy
    have hmem := hcomm (φ x) hx (φ y) hy
    have e : φ (x * y) = φ (y * x) := by
      simp only [map_mul]
      exact hmem
    exact hinj e
  · rw [Subgroup.relIndex_comap]
    exact hJ

/-- Frobenius lemma: a finite-order unitary commuting with its commutator
with a near-identity unitary commutes with it. -/
private theorem jl_commute_of_commute_commutator {E : Type*} [NormedRing E]
    [StarRing E] [CStarRing E] [NormedAlgebra ℂ E] [HasSummableGeomSeries E]
    (U V : unitary E) (m : ℕ) (hm : 0 < m) (hUm : U ^ m = 1)
    (hcomm : U * ⁅U, V⁆ = ⁅U, V⁆ * U)
    (hV : ‖((V : unitary E) : E) - 1‖ < 1 / 2) : U * V = V * U := by
  rcases subsingleton_or_nontrivial E with hsub | hnt
  · have := hsub
    have : Subsingleton (unitary E) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    exact Subsingleton.elim _ _
  · have := hnt
    have hUC : Commute U ⁅U, V⁆ := hcomm
    have ha : U * V * U⁻¹ = ⁅U, V⁆ * V := by
      rw [commutatorElement_def]
      group
    have haU : U * V = ⁅U, V⁆ * V * U := by
      have e : U * V = (U * V * U⁻¹) * U := by group
      rw [e, ha]
    have key : ∀ k : ℕ, U ^ k * V = ⁅U, V⁆ ^ k * V * U ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hUkC : Commute (U ^ k) ⁅U, V⁆ := hUC.pow_left k
        have hCC : ⁅U, V⁆ * ⁅U, V⁆ ^ k = ⁅U, V⁆ ^ k * ⁅U, V⁆ :=
          ((Commute.refl ⁅U, V⁆).pow_right k).eq
        calc U ^ (k + 1) * V
            = (U ^ k * U) * V := by rw [pow_succ]
          _ = U ^ k * (U * V) := by simp only [mul_assoc]
          _ = U ^ k * (⁅U, V⁆ * V * U) := by rw [haU]
          _ = (U ^ k * ⁅U, V⁆) * (V * U) := by simp only [mul_assoc]
          _ = (⁅U, V⁆ * U ^ k) * (V * U) := by rw [hUkC.eq]
          _ = ⁅U, V⁆ * ((U ^ k * V) * U) := by simp only [mul_assoc]
          _ = ⁅U, V⁆ * ((⁅U, V⁆ ^ k * V * U ^ k) * U) := by rw [ih]
          _ = ⁅U, V⁆ * (⁅U, V⁆ ^ k * V * (U ^ k * U)) := by
              simp only [mul_assoc]
          _ = (⁅U, V⁆ * (⁅U, V⁆ ^ k * V)) * (U ^ k * U) := by
              simp only [mul_assoc]
          _ = ((⁅U, V⁆ * ⁅U, V⁆ ^ k) * V) * (U ^ k * U) := by
              simp only [mul_assoc]
          _ = ((⁅U, V⁆ ^ k * ⁅U, V⁆) * V) * (U ^ k * U) := by rw [hCC]
          _ = ⁅U, V⁆ ^ (k + 1) * V * U ^ (k + 1) := by
              rw [pow_succ (⁅U, V⁆) k, pow_succ U k]
    have hkeym := key m
    rw [hUm] at hkeym
    have hCmV : ⁅U, V⁆ ^ m * V = V := by simpa using hkeym.symm
    have hmC : ⁅U, V⁆ ^ m = 1 := by
      have h2 : ⁅U, V⁆ ^ m * V = 1 * V := by rw [hCmV, one_mul]
      exact mul_right_cancel h2
    have hUU : ∀ k : ℕ, ((((U ^ k : unitary E))) : E)
          * (((((U ^ k)⁻¹ : unitary E))) : E) = 1 := by
      intro k
      have e1 : (((((U ^ k)⁻¹ : unitary E))) : E)
          = star ((((U ^ k : unitary E))) : E) := by
        rw [← Unitary.star_eq_inv, Unitary.coe_star]
      rw [e1]
      exact Unitary.mul_star_self_of_mem (U ^ k).2
    have hbound : ∀ k : ℕ, ‖((((⁅U, V⁆ ^ k : unitary E))) : E) - 1‖
        ≤ 2 * ‖((V : unitary E) : E) - 1‖ := by
      intro k
      have hCV : ⁅U, V⁆ ^ k * V = U ^ k * V * (U ^ k)⁻¹ := by
        have e : ⁅U, V⁆ ^ k * V
            = (⁅U, V⁆ ^ k * V * U ^ k) * (U ^ k)⁻¹ := by group
        rw [e, ← key k]
      have eC : ((((⁅U, V⁆ ^ k * V : unitary E))) : E)
          = ((((U ^ k : unitary E))) : E) * ((((V : unitary E))) : E)
            * (((((U ^ k)⁻¹ : unitary E))) : E) := by
        rw [hCV]
        simp only [Submonoid.coe_mul]
      have hfirst : ‖((((⁅U, V⁆ ^ k * V : unitary E))) : E) - 1‖
          = ‖((V : unitary E) : E) - 1‖ := by
        have e2 : ((((U ^ k : unitary E))) : E)
              * ((((V : unitary E)) : E) - 1)
              * (((((U ^ k)⁻¹ : unitary E))) : E)
            = ((((U ^ k : unitary E))) : E) * ((((V : unitary E))) : E)
              * (((((U ^ k)⁻¹ : unitary E))) : E)
              - (((((U ^ k : unitary E))) : E)
                * (((((U ^ k)⁻¹ : unitary E))) : E)) := by
          noncomm_ring
        have eAB : ((((U ^ k : unitary E))) : E) * ((((V : unitary E))) : E)
              * (((((U ^ k)⁻¹ : unitary E))) : E) - 1
            = ((((U ^ k : unitary E))) : E)
              * ((((V : unitary E)) : E) - 1)
              * (((((U ^ k)⁻¹ : unitary E))) : E) := by
          rw [e2, hUU k]
        rw [eC, eAB, CStarRing.norm_mul_coe_unitary,
          CStarRing.norm_coe_unitary_mul]
      have hCk1 : ‖((((⁅U, V⁆ ^ k : unitary E))) : E)‖ = 1 :=
        CStarRing.norm_coe_unitary _
      have hsecond : ‖((((⁅U, V⁆ ^ k : unitary E))) : E)
          * (1 - ((((V : unitary E))) : E))‖
          ≤ ‖1 - ((((V : unitary E))) : E)‖ := by
        calc ‖((((⁅U, V⁆ ^ k : unitary E))) : E)
              * (1 - ((((V : unitary E))) : E))‖
            ≤ ‖((((⁅U, V⁆ ^ k : unitary E))) : E)‖
              * ‖1 - ((((V : unitary E))) : E)‖ := norm_mul_le _ _
          _ = ‖1 - ((((V : unitary E))) : E)‖ := by rw [hCk1, one_mul]
      have edecomp : ((((⁅U, V⁆ ^ k : unitary E))) : E) - 1
          = (((((⁅U, V⁆ ^ k * V : unitary E))) : E) - 1)
            + ((((⁅U, V⁆ ^ k : unitary E))) : E)
              * (1 - ((((V : unitary E))) : E)) := by
        simp only [Submonoid.coe_mul]
        noncomm_ring
      calc ‖((((⁅U, V⁆ ^ k : unitary E))) : E) - 1‖
          = ‖((((⁅U, V⁆ ^ k * V : unitary E))) : E) - 1
            + ((((⁅U, V⁆ ^ k : unitary E))) : E)
              * (1 - ((((V : unitary E))) : E))‖ := by rw [edecomp]
        _ ≤ ‖((((⁅U, V⁆ ^ k * V : unitary E))) : E) - 1‖
            + ‖((((⁅U, V⁆ ^ k : unitary E))) : E)
              * (1 - ((((V : unitary E))) : E))‖ := norm_add_le _ _
        _ ≤ ‖((V : unitary E) : E) - 1‖ + ‖1 - ((V : unitary E) : E)‖ :=
          add_le_add hfirst.le hsecond
        _ = 2 * ‖((V : unitary E) : E) - 1‖ := by
            rw [norm_sub_rev (1 : E) ((V : unitary E) : E)]
            ring
    have hClt : ∀ k < m, ‖((((⁅U, V⁆ : unitary E))) : E) ^ k - 1‖ < 1 := by
      intro k _
      rw [← SubmonoidClass.coe_pow]
      calc ‖((((⁅U, V⁆ ^ k : unitary E))) : E) - 1‖
          ≤ 2 * ‖((V : unitary E) : E) - 1‖ := hbound k
        _ < 1 := by linarith [hV]
    have hCpow : ((((⁅U, V⁆ : unitary E))) : E) ^ m = 1 := by
      rw [← SubmonoidClass.coe_pow, hmC, OneMemClass.coe_one]
    have hCeq := jl_eq_one_of_pow ((((⁅U, V⁆ : unitary E))) : E) m hm hCpow hClt
    have hC1 : ⁅U, V⁆ = 1 := Subtype.ext hCeq
    exact commutatorElement_eq_one_iff_mul_comm.mp hC1

section jlDescent
open scoped Matrix.Norms.L2Operator

/-- Iterated commutator sequence: `seq 0 = y`, `seq (k+1) = [x, seq k]`. -/
private def jlSeq (n : ℕ) (x y : Matrix.GeneralLinearGroup (Fin n) ℂ) :
    ℕ → Matrix.GeneralLinearGroup (Fin n) ℂ
  | 0 => y
  | k + 1 => ⁅x, jlSeq n x y k⁆

private theorem jlSeq_zero (n : ℕ) (x y : Matrix.GeneralLinearGroup (Fin n) ℂ) :
    jlSeq n x y 0 = y := by
  rfl

private theorem jlSeq_succ (n : ℕ) (x y : Matrix.GeneralLinearGroup (Fin n) ℂ)
    (k : ℕ) : jlSeq n x y (k + 1) = ⁅x, jlSeq n x y k⁆ := by
  rfl

/-- Iterated commutators: halving distances, eventual triviality. -/
private theorem jl_iterated_commutator (n : ℕ)
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℂ)) [Finite ↥G]
    (hall : ∀ g : ↥G, ((((g : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
      Matrix (Fin n) (Fin n) ℂ) ∈ unitary (Matrix (Fin n) (Fin n) ℂ))
    (x y : Matrix.GeneralLinearGroup (Fin n) ℂ) (hxG : x ∈ G) (hyG : y ∈ G)
    (hx : ‖((((x : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
      Matrix (Fin n) (Fin n) ℂ) - 1‖ < 1 / 4)
    (hy : ‖((((y : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
      Matrix (Fin n) (Fin n) ℂ) - 1‖ < 1 / 4) :
    (∀ k, jlSeq n x y k ∈ G)
      ∧ (∀ k, ‖((((jlSeq n x y k :
        Matrix.GeneralLinearGroup (Fin n) ℂ))) :
        Matrix (Fin n) (Fin n) ℂ) - 1‖ < 1 / 4)
      ∧ (∀ k, ((((jlSeq n x y k :
        Matrix.GeneralLinearGroup (Fin n) ℂ))) :
        Matrix (Fin n) (Fin n) ℂ) ∈ unitary (Matrix (Fin n) (Fin n) ℂ))
      ∧ ∃ j ≥ 1, jlSeq n x y j = 1 := by
  have hxU : ((x : Matrix.GeneralLinearGroup (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ) ∈ unitary (Matrix (Fin n) (Fin n) ℂ) :=
    hall ⟨x, hxG⟩
  have hcomm_mem : ∀ a b : Matrix.GeneralLinearGroup (Fin n) ℂ,
      a ∈ G → b ∈ G → ⁅a, b⁆ ∈ G := by
    intro a b ha hb
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hcoe_comm : ∀ a b : Matrix.GeneralLinearGroup (Fin n) ℂ,
      ((a : Matrix (Fin n) (Fin n) ℂ) ∈ unitary (Matrix (Fin n) (Fin n) ℂ)) →
      ((b : Matrix (Fin n) (Fin n) ℂ) ∈ unitary (Matrix (Fin n) (Fin n) ℂ)) →
      (((⁅a, b⁆ : Matrix.GeneralLinearGroup (Fin n) ℂ)) :
        Matrix (Fin n) (Fin n) ℂ)
        = (a : Matrix (Fin n) (Fin n) ℂ) * (b : Matrix (Fin n) (Fin n) ℂ)
          * star (a : Matrix (Fin n) (Fin n) ℂ)
          * star (b : Matrix (Fin n) (Fin n) ℂ) := by
    intro a b ha hb
    rw [commutatorElement_def]
    simp only [Units.val_mul]
    rw [jl_coe_inv_eq_star n a ha, jl_coe_inv_eq_star n b hb]
  have hmem : ∀ k, jlSeq n x y k ∈ G := by
    intro k
    induction k with
    | zero => rw [jlSeq_zero]; exact hyG
    | succ k ih => rw [jlSeq_succ]; exact hcomm_mem x _ hxG ih
  have hU : ∀ k, ((jlSeq n x y k : Matrix.GeneralLinearGroup (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ) ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := by
    intro k
    induction k with
    | zero => rw [jlSeq_zero]; exact hall ⟨y, hyG⟩
    | succ k ih =>
      rw [jlSeq_succ, hcoe_comm x _ hxU ih]
      exact mul_mem (mul_mem (mul_mem hxU ih) (Unitary.star_mem hxU))
        (Unitary.star_mem ih)
  have hhalf : ∀ k, ‖((jlSeq n x y (k + 1) :
      Matrix.GeneralLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) - 1‖
      ≤ (1 / 2) * ‖((jlSeq n x y k : Matrix.GeneralLinearGroup (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ) - 1‖ := by
    intro k
    rw [jlSeq_succ, hcoe_comm x _ hxU (hU k)]
    refine le_trans (jl_norm_commutator_sub_one_le _ _ hxU (hU k)) ?_
    have hx2 : 2 * ‖(x : Matrix (Fin n) (Fin n) ℂ) - 1‖ ≤ 1 / 2 := by
      have hnn := norm_nonneg ((x : Matrix (Fin n) (Fin n) ℂ) - 1)
      linarith
    calc 2 * ‖(x : Matrix (Fin n) (Fin n) ℂ) - 1‖
          * ‖((jlSeq n x y k : Matrix.GeneralLinearGroup (Fin n) ℂ) :
            Matrix (Fin n) (Fin n) ℂ) - 1‖
        = (2 * ‖(x : Matrix (Fin n) (Fin n) ℂ) - 1‖)
          * ‖((jlSeq n x y k : Matrix.GeneralLinearGroup (Fin n) ℂ) :
            Matrix (Fin n) (Fin n) ℂ) - 1‖ := by ring
      _ ≤ (1 / 2) * ‖((jlSeq n x y k : Matrix.GeneralLinearGroup (Fin n) ℂ) :
          Matrix (Fin n) (Fin n) ℂ) - 1‖ :=
        mul_le_mul_of_nonneg_right hx2 (norm_nonneg _)
  have hb : ∀ k, ‖((jlSeq n x y k : Matrix.GeneralLinearGroup (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ) - 1‖ < 1 / 4 := by
    intro k
    induction k with
    | zero => rw [jlSeq_zero]; exact hy
    | succ k ih =>
      refine lt_of_le_of_lt (hhalf k) ?_
      have hlt := mul_lt_mul_of_pos_left ih (show (0 : ℝ) < 1 / 2 by norm_num)
      linarith
  have hiter : ∀ (i d : ℕ), ‖((jlSeq n x y (i + d) :
      Matrix.GeneralLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) - 1‖
      ≤ (1 / 2) ^ d * ‖((jlSeq n x y i :
        Matrix.GeneralLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
        - 1‖ := by
    intro i d
    induction d with
    | zero => simp
    | succ d ih =>
      have e : i + (d + 1) = (i + d) + 1 := by omega
      rw [e]
      calc ‖((jlSeq n x y ((i + d) + 1) :
            Matrix.GeneralLinearGroup (Fin n) ℂ) :
            Matrix (Fin n) (Fin n) ℂ) - 1‖
          ≤ (1 / 2) * ‖((jlSeq n x y (i + d) :
              Matrix.GeneralLinearGroup (Fin n) ℂ) :
              Matrix (Fin n) (Fin n) ℂ) - 1‖ := hhalf _
        _ ≤ (1 / 2) * ((1 / 2) ^ d * ‖((jlSeq n x y i :
              Matrix.GeneralLinearGroup (Fin n) ℂ) :
              Matrix (Fin n) (Fin n) ℂ) - 1‖) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1 / 2) ^ (d + 1) * ‖((jlSeq n x y i :
              Matrix.GeneralLinearGroup (Fin n) ℂ) :
              Matrix (Fin n) (Fin n) ℂ) - 1‖ := by ring
  have hfinal : ∀ (p d : ℕ), d ≠ 0 → jlSeq n x y p = jlSeq n x y (p + d) →
      ∃ j ≥ 1, jlSeq n x y j = 1 := by
    intro p d hd heqpd
    have hbound := hiter p d
    rw [← heqpd] at hbound
    have hpow : (1 / 2 : ℝ) ^ d < 1 :=
      pow_lt_one₀ (by norm_num) (by norm_num) hd
    have hN0 : ‖((jlSeq n x y p : Matrix.GeneralLinearGroup (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ) - 1‖ = 0 := by
      have hnnN := norm_nonneg (((jlSeq n x y p :
        Matrix.GeneralLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) - 1)
      have hle : ‖((jlSeq n x y p : Matrix.GeneralLinearGroup (Fin n) ℂ) :
          Matrix (Fin n) (Fin n) ℂ) - 1‖ * (1 - (1 / 2) ^ d) ≤ 0 := by
        nlinarith [hbound]
      have hpos : (0 : ℝ) < 1 - (1 / 2) ^ d := by linarith
      have hle0 : ‖((jlSeq n x y p : Matrix.GeneralLinearGroup (Fin n) ℂ) :
          Matrix (Fin n) (Fin n) ℂ) - 1‖ ≤ 0 := by
        by_contra hc
        rw [not_le] at hc
        have hmul := mul_pos hc hpos
        linarith
      linarith
    have hM : ((jlSeq n x y (p + d) : Matrix.GeneralLinearGroup (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ) = 1 := by
      rw [← heqpd]
      exact sub_eq_zero.mp (norm_eq_zero.mp hN0)
    exact ⟨p + d, by omega, Units.ext hM⟩
  obtain ⟨i, j, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k => (⟨jlSeq n x y k, hmem k⟩ : ↥G))
  have hseq_eq : jlSeq n x y i = jlSeq n x y j := congrArg Subtype.val heq
  refine ⟨hmem, hb, hU, ?_⟩
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
    have hd : d ≠ 0 := by omega
    exact hfinal i d hd hseq_eq
  · obtain ⟨d, rfl⟩ : ∃ d, i = j + d := ⟨i - j, by omega⟩
    have hd : d ≠ 0 := by omega
    exact hfinal j d hd hseq_eq.symm

/-- Frobenius step: if `x` commutes with `⁅x, s⁆` and `s` is within
`1 / 2` of `1`, then `x` commutes with `s`. Applies N7 to bundled unitaries. -/
private theorem jl_frobenius_step (n : ℕ)
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℂ)) [Finite ↥G]
    (x s : Matrix.GeneralLinearGroup (Fin n) ℂ) (hxG : x ∈ G)
    (hxU : ((x : Matrix.GeneralLinearGroup (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ) ∈ unitary (Matrix (Fin n) (Fin n) ℂ))
    (hsU : ((s : Matrix.GeneralLinearGroup (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ) ∈ unitary (Matrix (Fin n) (Fin n) ℂ))
    (hsnorm : ‖(((s : Matrix.GeneralLinearGroup (Fin n) ℂ)) :
      Matrix (Fin n) (Fin n) ℂ) - 1‖ < 1 / 2)
    (hcomm : x * ⁅x, s⁆ = ⁅x, s⁆ * x) :
    x * s = s * x := by
  have : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) :=
    FiniteDimensional.complete ℂ (Matrix (Fin n) (Fin n) ℂ)
  have hxfin : IsOfFinOrder (⟨x, hxG⟩ : ↥G) := isOfFinOrder_of_finite _
  have hmpos : 0 < orderOf (⟨x, hxG⟩ : ↥G) := hxfin.orderOf_pos
  have hxpow : x ^ orderOf (⟨x, hxG⟩ : ↥G) = 1 := by
    have h := pow_orderOf_eq_one (⟨x, hxG⟩ : ↥G)
    have h2 := congrArg Subtype.val h
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h2
    exact h2
  have hxpowM : (x : Matrix (Fin n) (Fin n) ℂ)
      ^ orderOf (⟨x, hxG⟩ : ↥G) = 1 := by
    rw [← Units.val_pow_eq_pow_val, hxpow, Units.val_one]
  have hUm : (⟨(x : Matrix (Fin n) (Fin n) ℂ), hxU⟩ :
      unitary (Matrix (Fin n) (Fin n) ℂ)) ^ orderOf (⟨x, hxG⟩ : ↥G) = 1 := by
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact hxpowM
  have hC : ((⁅(⟨(x : Matrix (Fin n) (Fin n) ℂ), hxU⟩ :
      unitary (Matrix (Fin n) (Fin n) ℂ)),
      (⟨(s : Matrix (Fin n) (Fin n) ℂ), hsU⟩ :
        unitary (Matrix (Fin n) (Fin n) ℂ))⁆ :
      unitary (Matrix (Fin n) (Fin n) ℂ)) : Matrix (Fin n) (Fin n) ℂ)
      = (((⁅x, s⁆ : Matrix.GeneralLinearGroup (Fin n) ℂ)) :
        Matrix (Fin n) (Fin n) ℂ) :=
    jl_coe_commutator_GL n x s
      (⟨(x : Matrix (Fin n) (Fin n) ℂ), hxU⟩ :
        unitary (Matrix (Fin n) (Fin n) ℂ))
      (⟨(s : Matrix (Fin n) (Fin n) ℂ), hsU⟩ :
        unitary (Matrix (Fin n) (Fin n) ℂ)) rfl rfl
  have hcommM : (x : Matrix (Fin n) (Fin n) ℂ)
      * (((⁅x, s⁆ : Matrix.GeneralLinearGroup (Fin n) ℂ)) :
        Matrix (Fin n) (Fin n) ℂ)
      = (((⁅x, s⁆ : Matrix.GeneralLinearGroup (Fin n) ℂ)) :
        Matrix (Fin n) (Fin n) ℂ) * (x : Matrix (Fin n) (Fin n) ℂ) := by
    have h := congrArg (Units.val : Matrix.GeneralLinearGroup (Fin n) ℂ →
      Matrix (Fin n) (Fin n) ℂ) hcomm
    simpa [Units.val_mul] using h
  have hcommU : (⟨(x : Matrix (Fin n) (Fin n) ℂ), hxU⟩ :
      unitary (Matrix (Fin n) (Fin n) ℂ))
        * ⁅(⟨(x : Matrix (Fin n) (Fin n) ℂ), hxU⟩ :
          unitary (Matrix (Fin n) (Fin n) ℂ)),
          (⟨(s : Matrix (Fin n) (Fin n) ℂ), hsU⟩ :
            unitary (Matrix (Fin n) (Fin n) ℂ))⁆
      = ⁅(⟨(x : Matrix (Fin n) (Fin n) ℂ), hxU⟩ :
          unitary (Matrix (Fin n) (Fin n) ℂ)),
          (⟨(s : Matrix (Fin n) (Fin n) ℂ), hsU⟩ :
            unitary (Matrix (Fin n) (Fin n) ℂ))⁆
        * (⟨(x : Matrix (Fin n) (Fin n) ℂ), hxU⟩ :
          unitary (Matrix (Fin n) (Fin n) ℂ)) := by
    apply Subtype.ext
    simp only [Submonoid.coe_mul]
    rw [hC]
    exact hcommM
  have key := jl_commute_of_commute_commutator
    (⟨(x : Matrix (Fin n) (Fin n) ℂ), hxU⟩ :
      unitary (Matrix (Fin n) (Fin n) ℂ))
    (⟨(s : Matrix (Fin n) (Fin n) ℂ), hsU⟩ :
      unitary (Matrix (Fin n) (Fin n) ℂ))
    (orderOf (⟨x, hxG⟩ : ↥G)) hmpos hUm hcommU hsnorm
  have keyM := congrArg (Subtype.val : unitary (Matrix (Fin n) (Fin n) ℂ) →
    Matrix (Fin n) (Fin n) ℂ) key
  simp only [Submonoid.coe_mul] at keyM
  apply Units.ext
  simp only [Units.val_mul]
  exact keyM

/-- Near-identity elements commute: `x * y = y * x`. -/
private theorem jl_commute_of_near_one (n : ℕ)
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℂ)) [Finite ↥G]
    (hall : ∀ g : ↥G, ((((g : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
      Matrix (Fin n) (Fin n) ℂ) ∈ unitary (Matrix (Fin n) (Fin n) ℂ))
    (x y : Matrix.GeneralLinearGroup (Fin n) ℂ) (hxG : x ∈ G) (hyG : y ∈ G)
    (hx : ‖((((x : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
      Matrix (Fin n) (Fin n) ℂ) - 1‖ < 1 / 4)
    (hy : ‖((((y : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
      Matrix (Fin n) (Fin n) ℂ) - 1‖ < 1 / 4) :
    x * y = y * x := by
  obtain ⟨_hmem, hb, hU, j, hj1, hjseq⟩ :=
    jl_iterated_commutator n G hall x y hxG hyG hx hy
  have hxU : ((x : Matrix.GeneralLinearGroup (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ) ∈ unitary (Matrix (Fin n) (Fin n) ℂ) :=
    hall ⟨x, hxG⟩
  have step : ∀ k, 1 ≤ k → jlSeq n x y (k + 1) = 1 → jlSeq n x y k = 1 := by
    intro k hk1 hnext
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [jlSeq_succ] at hnext
    have hcomm : x * ⁅x, jlSeq n x y k'⁆ = ⁅x, jlSeq n x y k'⁆ * x :=
      commutatorElement_eq_one_iff_mul_comm.mp hnext
    have hsnorm : ‖(((jlSeq n x y k' : Matrix.GeneralLinearGroup (Fin n) ℂ)) :
        Matrix (Fin n) (Fin n) ℂ) - 1‖ < 1 / 2 :=
      lt_trans (hb _) (by norm_num)
    have hconcl := jl_frobenius_step n G x (jlSeq n x y k') hxG hxU (hU _)
      hsnorm hcomm
    rw [jlSeq_succ]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hconcl
  have key : ∀ d, d + 1 ≤ j → jlSeq n x y (j - d) = 1 := by
    intro d
    induction d with
    | zero => intro _; simpa using hjseq
    | succ d ih =>
      intro hd
      have h1 := ih (by omega)
      have hk1 : 1 ≤ j - (d + 1) := by omega
      have e : j - (d + 1) + 1 = j - d := by omega
      have hnext : jlSeq n x y (j - (d + 1) + 1) = 1 := by
        rw [e]
        exact h1
      exact step _ hk1 hnext
  have h1 : jlSeq n x y 1 = 1 := by
    have h := key (j - 1) (by omega)
    have e : j - (j - 1) = 1 := by omega
    rwa [e] at h
  have hC1 : ⁅x, y⁆ = 1 := by
    have h := h1
    rw [show (1 : ℕ) = 0 + 1 from rfl, jlSeq_succ, jlSeq_zero] at h
    exact h
  exact commutatorElement_eq_one_iff_mul_comm.mp hC1

end jlDescent

section jlCore
open scoped Matrix.Norms.L2Operator

/-- The near-identity set: elements of `G` within `1 / 4` of `1`. -/
private def jlNearOneSet (n : ℕ)
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℂ)) :
    Set (Matrix.GeneralLinearGroup (Fin n) ℂ) :=
  {g | g ∈ G ∧ ‖((g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ) - 1‖ < 1 / 4}

/-- The near-identity closure is contained in `G` and commutative. -/
private theorem jl_near_one_closure_comm (n : ℕ)
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℂ)) [Finite ↥G]
    (hall : ∀ g : ↥G, ((((g : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
      Matrix (Fin n) (Fin n) ℂ) ∈ unitary (Matrix (Fin n) (Fin n) ℂ)) :
    Subgroup.closure (jlNearOneSet n G) ≤ G ∧
    ∀ a ∈ Subgroup.closure (jlNearOneSet n G),
    ∀ b ∈ Subgroup.closure (jlNearOneSet n G), a * b = b * a := by
  have hmem : ∀ g : Matrix.GeneralLinearGroup (Fin n) ℂ, g ∈ jlNearOneSet n G →
      g ∈ G ∧ ‖((g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ) - 1‖ < 1 / 4 :=
    fun g hg => hg
  refine ⟨?_, ?_⟩
  · rw [Subgroup.closure_le]
    intro g hg
    exact (hmem g hg).1
  · have hpair : (jlNearOneSet n G).Pairwise Commute := by
      intro a ha b hb _
      change a * b = b * a
      obtain ⟨haG, han⟩ := hmem a ha
      obtain ⟨hbG, hbn⟩ := hmem b hb
      exact jl_commute_of_near_one n G hall a b haG hbG han hbn
    have : IsMulCommutative ↥(Subgroup.closure (jlNearOneSet n G)) :=
      Subgroup.isMulCommutative_closure hpair
    intro a ha b hb
    have h := mul_comm' (⟨a, ha⟩ : ↥(Subgroup.closure (jlNearOneSet n G)))
      (⟨b, hb⟩ : ↥(Subgroup.closure (jlNearOneSet n G)))
    have h2 := congrArg Subtype.val h
    simpa using h2

/-- The near-identity closure is normalized by `G`. -/
private theorem jl_near_one_closure_normal (n : ℕ)
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℂ)) [Finite ↥G]
    (hall : ∀ g : ↥G, ((((g : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
      Matrix (Fin n) (Fin n) ℂ) ∈ unitary (Matrix (Fin n) (Fin n) ℂ))
    (g : Matrix.GeneralLinearGroup (Fin n) ℂ) (hg : g ∈ G)
    (a : Matrix.GeneralLinearGroup (Fin n) ℂ)
    (ha : a ∈ Subgroup.closure (jlNearOneSet n G)) :
    g * a * g⁻¹ ∈ Subgroup.closure (jlNearOneSet n G) := by
  have hgU : ((g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ) ∈ unitary (Matrix (Fin n) (Fin n) ℂ) :=
    hall ⟨g, hg⟩
  have hcg : ∀ s : Matrix.GeneralLinearGroup (Fin n) ℂ,
      (MulAut.conj g).toMonoidHom s = g * s * g⁻¹ :=
    fun s => MulAut.conj_apply g s
  have hmaps : ∀ s ∈ jlNearOneSet n G,
      (MulAut.conj g).toMonoidHom s ∈ jlNearOneSet n G := by
    intro s hs
    have hs' : s ∈ G ∧ ‖((s : Matrix.GeneralLinearGroup (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ) - 1‖ < 1 / 4 := hs
    have hgg : ((g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
          Matrix (Fin n) (Fin n) ℂ)
            * (((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ)) :
              Matrix (Fin n) (Fin n) ℂ) = 1 := Units.mul_inv g
    have e : (((((MulAut.conj g).toMonoidHom s :
        Matrix.GeneralLinearGroup (Fin n) ℂ))) :
          Matrix (Fin n) (Fin n) ℂ) - 1
        = ((g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
          Matrix (Fin n) (Fin n) ℂ)
          * ((((s : Matrix.GeneralLinearGroup (Fin n) ℂ)) :
            Matrix (Fin n) (Fin n) ℂ) - 1)
          * (((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ)) :
            Matrix (Fin n) (Fin n) ℂ) := by
      rw [hcg]
      simp only [Units.val_mul]
      have e4 : ((g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
            Matrix (Fin n) (Fin n) ℂ)
              * ((((s : Matrix.GeneralLinearGroup (Fin n) ℂ)) :
                Matrix (Fin n) (Fin n) ℂ) - 1)
              * (((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ)) :
                Matrix (Fin n) (Fin n) ℂ)
          = ((g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
            Matrix (Fin n) (Fin n) ℂ)
            * (((s : Matrix.GeneralLinearGroup (Fin n) ℂ)) :
              Matrix (Fin n) (Fin n) ℂ)
            * (((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ)) :
              Matrix (Fin n) (Fin n) ℂ) - 1 := by
        have e5 : ((g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
              Matrix (Fin n) (Fin n) ℂ)
                * ((((s : Matrix.GeneralLinearGroup (Fin n) ℂ)) :
                  Matrix (Fin n) (Fin n) ℂ) - 1)
                * (((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ)) :
                  Matrix (Fin n) (Fin n) ℂ)
            = ((g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
              Matrix (Fin n) (Fin n) ℂ)
              * (((s : Matrix.GeneralLinearGroup (Fin n) ℂ)) :
                Matrix (Fin n) (Fin n) ℂ)
              * (((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ)) :
                Matrix (Fin n) (Fin n) ℂ)
              - ((g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
                Matrix (Fin n) (Fin n) ℂ)
              * (((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ)) :
                Matrix (Fin n) (Fin n) ℂ) := by
          noncomm_ring
        rw [e5, hgg]
      rw [e4]
    refine ⟨?_, ?_⟩
    · rw [hcg]
      exact mul_mem (mul_mem hg hs'.1) (inv_mem hg)
    · rw [e, jl_norm_conj n g hgU]
      exact hs'.2
  have hsub : (Subgroup.closure (jlNearOneSet n G)).map (MulAut.conj g).toMonoidHom
      ≤ Subgroup.closure (jlNearOneSet n G) := by
    rw [MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro y ⟨s, hs, rfl⟩
    exact hmaps s hs
  have hmem : (MulAut.conj g).toMonoidHom a
      ∈ (Subgroup.closure (jlNearOneSet n G)).map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
  have hfin := hsub hmem
  rwa [hcg] at hfin

/-- Finite cover of the unitary group by `1 / 8`-balls. -/
private theorem jl_cover_unitary (n : ℕ) :
    ∃ N : Finset (Matrix (Fin n) (Fin n) ℂ),
    ∀ M : Matrix (Fin n) (Fin n) ℂ, M ∈ unitary (Matrix (Fin n) (Fin n) ℂ) →
      ∃ y ∈ N, ‖M - y‖ < 1 / 8 := by
  have : ProperSpace (Matrix (Fin n) (Fin n) ℂ) :=
    FiniteDimensional.proper ℂ (Matrix (Fin n) (Fin n) ℂ)
  have hcomp : IsCompact (Metric.closedBall (0 : Matrix (Fin n) (Fin n) ℂ) 1) :=
    isCompact_closedBall 0 1
  obtain ⟨t, _, hfin, hcover⟩ :=
    hcomp.finite_cover_balls (show (0 : ℝ) < 1 / 8 by norm_num)
  refine ⟨hfin.toFinset, fun M hM => ?_⟩
  have hM1 : ‖M‖ ≤ 1 := by
    rcases subsingleton_or_nontrivial (Matrix (Fin n) (Fin n) ℂ) with hsub | hnt
    · have hM0 : M = 0 := Subsingleton.elim M 0
      rw [hM0, norm_zero]
      exact zero_le_one
    · have : Nontrivial (Matrix (Fin n) (Fin n) ℂ) := hnt
      have h1 : ‖M‖ = 1 := CStarRing.norm_coe_unitary ⟨M, hM⟩
      exact h1.le
  have hMball : M ∈ Metric.closedBall (0 : Matrix (Fin n) (Fin n) ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hM1
  obtain ⟨y, hyt, hMemy⟩ := Set.mem_iUnion₂.mp (hcover hMball)
  refine ⟨y, hfin.mem_toFinset.mpr hyt, ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hMemy
  exact hMemy

/-- Index bound by the cover cardinality. -/
private theorem jl_relIndex_le (n : ℕ)
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℂ)) [Finite ↥G]
    (hall : ∀ g : ↥G, ((((g : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
      Matrix (Fin n) (Fin n) ℂ) ∈ unitary (Matrix (Fin n) (Fin n) ℂ))
    (N : Finset (Matrix (Fin n) (Fin n) ℂ))
    (hN : ∀ M : Matrix (Fin n) (Fin n) ℂ, M ∈ unitary (Matrix (Fin n) (Fin n) ℂ) →
      ∃ y ∈ N, ‖M - y‖ < 1 / 8) :
    (Subgroup.closure (jlNearOneSet n G)).relIndex G ≤ N.card := by
  have hchoice : ∀ q : (↥G ⧸ (Subgroup.closure (jlNearOneSet n G)).subgroupOf G),
      ∃ y ∈ N, ‖(((q.out : Matrix.GeneralLinearGroup (Fin n) ℂ)) :
        Matrix (Fin n) (Fin n) ℂ) - y‖ < 1 / 8 := by
    intro q
    exact hN _ (hall q.out)
  choose y hyN hyclose using hchoice
  have hinj : Function.Injective
      (fun q : (↥G ⧸ (Subgroup.closure (jlNearOneSet n G)).subgroupOf G) =>
        (⟨y q, hyN q⟩ : ↥N)) := by
    intro q q' heq
    have hyeq : y q = y q' := congrArg Subtype.val heq
    have hxG : ((q.out : Matrix.GeneralLinearGroup (Fin n) ℂ)) ∈ G := q.out.2
    have hxG' : ((q'.out : Matrix.GeneralLinearGroup (Fin n) ℂ)) ∈ G := q'.out.2
    have hxU : ((((q.out : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
        Matrix (Fin n) (Fin n) ℂ) ∈ unitary (Matrix (Fin n) (Fin n) ℂ) :=
      hall q.out
    have h1 := hyclose q
    have h2 := hyclose q'
    rw [hyeq] at h1
    have h2' : ‖y q' - ((((q'.out : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
        Matrix (Fin n) (Fin n) ℂ)‖ < 1 / 8 := by
      rw [norm_sub_rev]
      exact h2
    have htri : ‖((((q.out : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
          Matrix (Fin n) (Fin n) ℂ)
          - ((((q'.out : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
            Matrix (Fin n) (Fin n) ℂ)‖ < 1 / 4 := by
      calc ‖((((q.out : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
            Matrix (Fin n) (Fin n) ℂ)
            - ((((q'.out : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
              Matrix (Fin n) (Fin n) ℂ)‖
          = ‖((((q.out : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
              Matrix (Fin n) (Fin n) ℂ) - y q'
            + (y q' - ((((q'.out : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
              Matrix (Fin n) (Fin n) ℂ))‖ := by
            congr 1
            abel
        _ ≤ ‖((((q.out : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
              Matrix (Fin n) (Fin n) ℂ) - y q'‖
            + ‖y q' - ((((q'.out : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
              Matrix (Fin n) (Fin n) ℂ)‖ := norm_add_le _ _
        _ < 1 / 8 + 1 / 8 := add_lt_add h1 h2'
        _ = 1 / 4 := by norm_num
    have hdist := jl_dist_unitary n ((q.out : Matrix.GeneralLinearGroup (Fin n) ℂ))
      ((q'.out : Matrix.GeneralLinearGroup (Fin n) ℂ)) hxU
    have hcloseGL : ‖((((((q.out : Matrix.GeneralLinearGroup (Fin n) ℂ))⁻¹ *
          ((q'.out : Matrix.GeneralLinearGroup (Fin n) ℂ)) :
        Matrix.GeneralLinearGroup (Fin n) ℂ))) :
        Matrix (Fin n) (Fin n) ℂ) - 1‖ < 1 / 4 := by
      rwa [hdist] at htri
    have hclose : ‖(((q.out : ↥G)⁻¹ * (q'.out : ↥G) :
        Matrix.GeneralLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) - 1‖ <
        1 / 4 := hcloseGL
    have hmemG : (((q.out : ↥G)⁻¹ * (q'.out : ↥G) :
        Matrix.GeneralLinearGroup (Fin n) ℂ)) ∈ G :=
      mul_mem (inv_mem hxG) hxG'
    have hSmem : (((q.out : ↥G)⁻¹ * (q'.out : ↥G) :
        Matrix.GeneralLinearGroup (Fin n) ℂ)) ∈ jlNearOneSet n G :=
      ⟨hmemG, hclose⟩
    have hsubmem : (((q.out : ↥G))⁻¹ * (q'.out : ↥G)) ∈
        (Subgroup.closure (jlNearOneSet n G)).subgroupOf G :=
      Subgroup.subset_closure hSmem
    have hclass : QuotientGroup.mk ((q.out : ↥G)) =
        QuotientGroup.mk ((q'.out : ↥G)) :=
      QuotientGroup.eq.mpr hsubmem
    have e1 : QuotientGroup.mk ((q.out : ↥G)) = q := Quotient.out_eq q
    have e2 : QuotientGroup.mk ((q'.out : ↥G)) = q' := Quotient.out_eq q'
    rw [e1, e2] at hclass
    exact hclass
  have hle : Nat.card (↥G ⧸ (Subgroup.closure (jlNearOneSet n G)).subgroupOf G)
      ≤ Nat.card ↥N :=
    Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_finsetCard N] at hle
  exact hle

/-- The unitary core: uniform bound for finite unitary subgroups. -/
private theorem jl_unitary_core (n : ℕ) :
    ∃ J : ℕ, ∀ G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℂ), Finite ↥G →
      (∀ g : ↥G, ((((g : Matrix.GeneralLinearGroup (Fin n) ℂ))) :
        Matrix (Fin n) (Fin n) ℂ) ∈ unitary (Matrix (Fin n) (Fin n) ℂ)) →
      ∃ A : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℂ), A ≤ G ∧
        (∀ g ∈ G, ∀ a ∈ A, g * a * g⁻¹ ∈ A) ∧
        (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧
        A.relIndex G ≤ J := by
  obtain ⟨N, hN⟩ := jl_cover_unitary n
  refine ⟨N.card, fun G hfin hall => ?_⟩
  have : Finite ↥G := hfin
  obtain ⟨hle, hcomm⟩ := jl_near_one_closure_comm n G hall
  refine ⟨Subgroup.closure (jlNearOneSet n G), hle, ?_, ?_, ?_⟩
  · intro g hg a ha
    exact jl_near_one_closure_normal n G hall g hg a ha
  · intro x hx y hy
    exact hcomm x hx y hy
  · exact jl_relIndex_le n G hall N hN

end jlCore

end MathlibExt.GroupTheory.JordanLinearGroupsWanted

@[expose] public section

/-!
# Jordan's theorem for finite complex linear groups — wishlist

Records that finite subgroups of `GL_n(ℂ)` have abelian normal subgroups of bounded index.
-/

namespace MathlibExt.GroupTheory.JordanLinearGroupsWanted

/--
**Jordan's theorem on finite linear groups.** For every natural number $n$ there is a natural
number $J$ such that every finite subgroup $G$ of $\mathrm{GL}_n(\mathbb{C})$ contains an abelian
subgroup $A$ that is normal in $G$ and has index $[G : A] \le J$.

Proves `Wanted` entry `jordan_linear_groups`.

Source: C. Jordan, J. Reine Angew. Math. 84 (1878); Lean
states complex GL_n specialization `GL_n(ℂ)` while general theorem holds over any char-zero field
with bound depending only on n.
-/
public theorem jordan_linear_groups
    (n : ℕ) : ∃ J : ℕ, ∀ (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) Complex)),
      Finite ↥G →
        ∃ (A : Subgroup (Matrix.GeneralLinearGroup (Fin n) Complex)),
          A ≤ G ∧
          (∀ g ∈ G, ∀ a ∈ A, g * a * g⁻¹ ∈ A) ∧
          (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧
          A.relIndex G ≤ J := by
  obtain ⟨J, hJ⟩ := jl_unitary_core n
  refine ⟨J, fun G hfinG => ?_⟩
  have : Finite ↥G := hfinG
  obtain ⟨P, hP⟩ := jl_exists_conj_unitary n G
  have hφinj : Function.Injective (MulAut.conj P).toMonoidHom :=
    MulEquiv.injective (MulAut.conj P)
  have hfinG' : Finite ↥(G.map (MulAut.conj P).toMonoidHom) := by
    apply Finite.of_surjective (fun x : ↥G =>
      (⟨(MulAut.conj P).toMonoidHom x,
        Subgroup.mem_map.mpr
          ⟨(x : Matrix.GeneralLinearGroup (Fin n) ℂ), x.2, rfl⟩⟩ :
        ↥(G.map (MulAut.conj P).toMonoidHom)))
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hall' : ∀ u : ↥(G.map (MulAut.conj P).toMonoidHom),
      (((u : Matrix.GeneralLinearGroup (Fin n) ℂ)) :
        Matrix (Fin n) (Fin n) ℂ) ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    have hPy := hP x hx
    have e : y = P * x * P⁻¹ := by
      rw [← hxy]
      exact MulAut.conj_apply P x
    subst e
    exact hPy
  obtain ⟨A', hAle, hAnorm, hAcomm, hAJ⟩ :=
    hJ (G.map (MulAut.conj P).toMonoidHom) hfinG' hall'
  exact jl_of_map_conj n J G _ hφinj A' hAle hAnorm hAcomm hAJ

end MathlibExt.GroupTheory.JordanLinearGroupsWanted
