/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.NormNum
import MathlibExt.GroupTheory.DicksonPGL2Wild
import MathlibExt.GroupTheory.LargeNormalSubsetSquareKourovka20Problem74

/-! Regression tests for Kourovka Notebook Problem 20.74. -/

open MathlibExt.GroupTheory.LargeNormalSubsetSquareKourovka20Problem74Wanted
open scoped MatrixGroups Pointwise

example (G : Type) [Group G] : HasLargeInverseClosedNormalSubsetWithSmallSquare G ↔
    ∃ S : Set G, (∀ g s : G, s ∈ S → g * s * g⁻¹ ∈ S) ∧ (∀ s ∈ S, s⁻¹ ∈ S) ∧
      (Nat.card G : ℝ) / Real.logb 2 (Nat.card G) < S.ncard ∧ S * S ≠ Set.univ :=
  Iff.rfl

example : ¬ ∃ N : ℕ, ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → HasLargeInverseClosedNormalSubsetWithSmallSquare G →
    Nat.card G ≤ N :=
  finitelyManySimpleGroupsWithLargeNormalSubset_refuted

section

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private abbrev project : SL(2, ZMod 5) →* PSL(2, ZMod 5) :=
  QuotientGroup.mk' (Subgroup.center SL(2, ZMod 5))

private def traceOne : Set PSL(2, ZMod 5) :=
  project '' {A : SL(2, ZMod 5) | A.val.trace = 1}

private theorem traceOne_normal (g s : PSL(2, ZMod 5)) (hs : s ∈ traceOne) :
    g * s * g⁻¹ ∈ traceOne := by
  obtain ⟨A, hA, rfl⟩ := hs
  obtain ⟨P, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(2, ZMod 5)) g
  refine ⟨P * A * P⁻¹, ?_, by simp⟩
  change (P * A * P⁻¹).val.trace = 1
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  have h := Matrix.trace_units_conj (Matrix.SpecialLinearGroup.toGL P) A.val
  rw [← map_inv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at h
  exact h.trans hA

private theorem traceOne_inv (s : PSL(2, ZMod 5)) (hs : s ∈ traceOne) : s⁻¹ ∈ traceOne := by
  obtain ⟨A, hA, rfl⟩ := hs
  refine ⟨A⁻¹, ?_, by simp⟩
  change A⁻¹.val.trace = 1
  simpa [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.trace_fin_two, add_comm]
    using hA

-- The two free entries give twenty distinct projective elements of trace one.
private def traceOneLift (a : ZMod 5) (b : (ZMod 5)ˣ) : SL(2, ZMod 5) :=
  ⟨!![a, ↑b; (↑(b⁻¹) : ZMod 5) * (a * (1 - a) - 1), 1 - a], by
    rw [Matrix.det_fin_two_of, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_mul, sub_sub_cancel]⟩

private theorem trace_traceOneLift (a : ZMod 5) (b : (ZMod 5)ˣ) :
    (traceOneLift a b).val.trace = 1 := by
  simp only [traceOneLift, Matrix.trace_fin_two_of, add_sub_cancel]

private theorem traceOne_card_ge : 20 ≤ traceOne.ncard := by
  let f (ab : ZMod 5 × (ZMod 5)ˣ) : traceOne :=
    ⟨project (traceOneLift ab.1 ab.2), ⟨_, trace_traceOneLift _ _, rfl⟩⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hproj : project (traceOneLift x.1 x.2) = project (traceOneLift y.1 y.2) :=
      congrArg Subtype.val hxy
    obtain ⟨z, hz, hmul⟩ := (QuotientGroup.mk'_eq_mk' _).mp hproj
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
    have hmat : (traceOneLift x.1 x.2).val * Matrix.scalar (Fin 2) r =
        (traceOneLift y.1 y.2).val := by
      simpa only [Matrix.SpecialLinearGroup.coe_mul, ← hr] using congrArg Subtype.val hmul
    rw [Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal] at hmat
    have hr₁ : r = 1 := by
      simpa [Matrix.trace_smul, trace_traceOneLift, smul_eq_mul] using congrArg Matrix.trace hmat
    rw [hr₁, one_smul] at hmat
    apply Prod.ext
    · exact congrArg (fun A : Matrix (Fin 2) (Fin 2) (ZMod 5) ↦ A 0 0) hmat
    · exact Units.ext (congrArg (fun A : Matrix (Fin 2) (Fin 2) (ZMod 5) ↦ A 0 1) hmat)
  have h := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_prod, Nat.card_units, Nat.card_zmod, Nat.card_coe_set_eq] using h

private theorem traceOne_large :
    (Nat.card PSL(2, ZMod 5) : ℝ) / Real.logb 2 (Nat.card PSL(2, ZMod 5)) < traceOne.ncard := by
  have ho : Nat.card PSL(2, ZMod 5) = 60 := by
    rw [MetaMathlibExt.Dickson.card_projectiveSpecialLinearGroup_fin_two 5 (ZMod 5) (by decide),
      ZMod.card]
    decide
  rw [ho]
  have hlog : (4 : ℝ) < Real.logb 2 60 := by
    apply (Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)).2
    norm_num [Real.rpow_natCast]
  have hcard : (20 : ℝ) ≤ traceOne.ncard := by exact_mod_cast traceOne_card_ge
  have hlt : (60 : ℝ) / Real.logb 2 60 < 15 :=
    (div_lt_iff₀ (by linarith)).2 (by linarith)
  linarith

private def unipotent : SL(2, ZMod 5) := ⟨!![1, 1; 0, 1], by simp⟩

private def traceZero : SL(2, ZMod 5) := ⟨!![0, -1; 1, 0], by simp⟩

-- The public coverage result applies to the concrete large subset, including at a nonidentity
-- unipotent element and at a trace-zero element.
example : (∀ g s : PSL(2, ZMod 5), s ∈ traceOne → g * s * g⁻¹ ∈ traceOne) ∧
    (∀ s ∈ traceOne, s⁻¹ ∈ traceOne) ∧
    (Nat.card PSL(2, ZMod 5) : ℝ) / Real.logb 2 (Nat.card PSL(2, ZMod 5)) < traceOne.ncard ∧
    unipotent.val.trace = 2 ∧ project unipotent ≠ 1 ∧ project unipotent ∈ traceOne * traceOne ∧
    traceZero.val.trace = 0 ∧ project traceZero ∈ traceOne * traceOne := by
  have hchar : ringChar (ZMod 5) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; decide
  have hT : project (traceOneLift 0 1) ∈ traceOne := ⟨_, trace_traceOneLift _ _, rfl⟩
  have hcover := psl2_square_eq_univ_of_trace hchar traceOne_normal traceOne_inv
    (traceOneLift 0 1) hT (by simp [trace_traceOneLift]) (by rw [trace_traceOneLift]; decide)
  refine ⟨traceOne_normal, traceOne_inv, traceOne_large, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · intro h
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp
      ((QuotientGroup.eq_one_iff unipotent).mp h)
    have h₀₁ := congrArg (fun A : Matrix (Fin 2) (Fin 2) (ZMod 5) ↦ A 0 1) hr
    simp [unipotent] at h₀₁
  · rw [hcover]; exact Set.mem_univ _
  · decide
  · rw [hcover]; exact Set.mem_univ _

end
