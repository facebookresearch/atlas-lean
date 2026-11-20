/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_LanglandsTunnell_Converse_ArchDatumR_exists_lt_mellin_W_
 diagOne_ne_zero_of_weightZero_of_parity.lean`,
`Definitions/Def_LanglandsTunnell_ArchParam.lean`,
`Definitions/Def_LanglandsTunnell_ArchEpsilon.lean`,
`Definitions/Def_LanglandsTunnell_JLConverse.lean`,
`Definitions/Def_AutomorphicForm_ArchWeightChar.lean`,
`Definitions/Def_AutomorphicForm_RowIsometryInvariance.lean`
and
`P2M/Sol/S_LanglandsTunnell_Converse_ArchDatumR_exists_lt_mellin_W_
 diagOne_ne_zero_of_weightZero_of_parity.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib - https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Analysis.Analytic.IteratedFDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.MellinInversion
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

open MeasureTheory

noncomputable section

namespace LanglandsTunnell

open Complex

/-- A real archimedean Langlands parameter: either a principal-series
pair or a discrete-series parameter. -/
inductive RealArchParam where

  | principal (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) : RealArchParam

  | discrete (u : ℂ) (k : ℕ) (hk : 1 ≤ k) : RealArchParam

def signShift (a : ZMod 2) : ℂ := if a = 0 then 0 else 1

@[simp] theorem signShift_zero : signShift 0 = 0 := by simp [signShift]

@[simp] theorem signShift_one : signShift 1 = 1 := by simp [signShift]

namespace RealArchParam

def gammaR : RealArchParam → Multiset ℂ
  | principal u₁ a₁ u₂ a₂ => {u₁ + signShift a₁, u₂ + signShift a₂}
  | discrete _ _ _ => 0

def gammaC : RealArchParam → Multiset ℂ
  | principal _ _ _ _ => 0
  | discrete u k _ => {u + (k : ℂ) / 2}

def archFactor (P : RealArchParam) (s : ℂ) : ℂ :=
  (P.gammaR.map fun μ => Gammaℝ (s + μ)).prod * (P.gammaC.map fun ν => Gammaℂ (s + ν)).prod

def twist : RealArchParam → ℂ → ZMod 2 → RealArchParam
  | principal u₁ a₁ u₂ a₂, u, a => principal (u₁ + u) (a₁ + a) (u₂ + u) (a₂ + a)
  | discrete u₀ k hk, u, _ => discrete (u₀ + u) k hk

def dual : RealArchParam → RealArchParam
  | principal u₁ a₁ u₂ a₂ => principal (-u₁) a₁ (-u₂) a₂
  | discrete u k hk => discrete (-u) k hk

def centralExponent : RealArchParam → ℂ
  | principal u₁ _ u₂ _ => u₁ + u₂
  | discrete u _ _ => 2 * u

def centralSign : RealArchParam → ZMod 2
  | principal _ a₁ _ a₂ => a₁ + a₂
  | discrete _ k _ => (k : ZMod 2) + 1

@[simp] theorem twist_zero (P : RealArchParam) : P.twist 0 0 = P := by
  cases P <;> simp [twist]

theorem twist_twist (P : RealArchParam) (u u' : ℂ) (a a' : ZMod 2) :
    (P.twist u a).twist u' a' = P.twist (u + u') (a + a') := by
  cases P <;> simp [twist, add_assoc]

@[simp] theorem dual_dual (P : RealArchParam) : P.dual.dual = P := by
  cases P <;> simp [dual]

theorem gammaC_twist (P : RealArchParam) (u : ℂ) (a : ZMod 2) :
    (P.twist u a).gammaC = P.gammaC.map (· + u) := by
  cases P <;> simp [twist, gammaC, add_right_comm]

theorem gammaR_twist_zero (P : RealArchParam) (u : ℂ) :
    (P.twist u 0).gammaR = P.gammaR.map (· + u) := by
  cases P <;> simp [twist, gammaR, add_right_comm]

end RealArchParam

def signEpsilon (a : ZMod 2) : ℂ := if a = 0 then 1 else I

@[simp] theorem signEpsilon_zero : signEpsilon 0 = 1 := by simp [signEpsilon]

@[simp] theorem signEpsilon_one : signEpsilon 1 = I := by simp [signEpsilon]

theorem signEpsilon_sq (a : ZMod 2) : signEpsilon a ^ 2 = if a = 0 then 1 else -1 := by
  by_cases h : a = 0
  · simp [signEpsilon, h]
  · simp [signEpsilon, h, I_sq]

namespace RealArchParam

def epsilonFactor : RealArchParam → ℂ
  | principal _ a₁ _ a₂ => signEpsilon a₁ * signEpsilon a₂
  | discrete _ k _ => I ^ (k + 1)

@[simp] theorem epsilonFactor_principal (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) :
    (principal u₁ a₁ u₂ a₂).epsilonFactor = signEpsilon a₁ * signEpsilon a₂ := rfl

@[simp] theorem epsilonFactor_discrete (u : ℂ) (k : ℕ) (hk : 1 ≤ k) :
    (discrete u k hk).epsilonFactor = I ^ (k + 1) := rfl

theorem epsilonFactor_twist_zero (P : RealArchParam) (u : ℂ) :
    (P.twist u 0).epsilonFactor = P.epsilonFactor := by
  cases P <;> simp [twist, epsilonFactor]

theorem epsilonFactor_dual (P : RealArchParam) : P.dual.epsilonFactor = P.epsilonFactor := by
  cases P <;> rfl

end RealArchParam
end LanglandsTunnell

namespace AutomorphicForm.WindowedSiegel

variable {K : Type*} [NormedField K]

variable {K : Type*} [NormedField K]

def IsRowIsometry (k : GL (Fin 2) K) : Prop :=
  ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ = 1 ∧
    ∀ x y : K,
      ‖x * (k : Matrix (Fin 2) (Fin 2) K) 0 0 + y * (k : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2
        + ‖x * (k : Matrix (Fin 2) (Fin 2) K) 0 1
            + y * (k : Matrix (Fin 2) (Fin 2) K) 1 1‖ ^ 2
      = ‖x‖ ^ 2 + ‖y‖ ^ 2

theorem isRowIsometry_one : IsRowIsometry (1 : GL (Fin 2) K) := by
  constructor
  · simp
  · intro x y
    have h00 : (1 : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := Matrix.one_apply_eq 0
    have h11 : (1 : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := Matrix.one_apply_eq 1
    have h10 : (1 : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := Matrix.one_apply_ne (by decide)
    have h01 : (1 : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := Matrix.one_apply_ne (by decide)
    show ‖x * (1 : Matrix (Fin 2) (Fin 2) K) 0 0 + y * (1 : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2
        + ‖x * (1 : Matrix (Fin 2) (Fin 2) K) 0 1 + y * (1 : Matrix (Fin 2) (Fin 2) K) 1 1‖ ^ 2
      = ‖x‖ ^ 2 + ‖y‖ ^ 2
    rw [h00, h11, h10, h01, mul_one, mul_one, mul_zero, mul_zero, add_zero, zero_add]

theorem IsRowIsometry.mul {k k' : GL (Fin 2) K} (hk : IsRowIsometry k)
    (hk' : IsRowIsometry k') : IsRowIsometry (k * k') := by
  obtain ⟨hdet, hrow⟩ := hk
  obtain ⟨hdet', hrow'⟩ := hk'
  have hcoe : ((k * k' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (k : Matrix (Fin 2) (Fin 2) K) * (k' : Matrix (Fin 2) (Fin 2) K) := rfl
  constructor
  · rw [hcoe, Matrix.det_mul, norm_mul, hdet, hdet', one_mul]
  · intro x y
    have hentry : ∀ i : Fin 2,
        x * ((k : Matrix (Fin 2) (Fin 2) K) * (k' : Matrix (Fin 2) (Fin 2) K)) 0 i
          + y * ((k : Matrix (Fin 2) (Fin 2) K) * (k' : Matrix (Fin 2) (Fin 2) K)) 1 i
        = (x * (k : Matrix (Fin 2) (Fin 2) K) 0 0 + y * (k : Matrix (Fin 2) (Fin 2) K) 1 0)
              * (k' : Matrix (Fin 2) (Fin 2) K) 0 i
          + (x * (k : Matrix (Fin 2) (Fin 2) K) 0 1 + y * (k : Matrix (Fin 2) (Fin 2) K) 1 1)
              * (k' : Matrix (Fin 2) (Fin 2) K) 1 i := by
      intro i
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    show ‖x * ((k * k' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0
          + y * ((k * k' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2
        + ‖x * ((k * k' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1
            + y * ((k * k' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1‖ ^ 2
      = ‖x‖ ^ 2 + ‖y‖ ^ 2
    rw [hcoe, hentry 0, hentry 1,
      hrow' (x * (k : Matrix (Fin 2) (Fin 2) K) 0 0 + y * (k : Matrix (Fin 2) (Fin 2) K) 1 0)
        (x * (k : Matrix (Fin 2) (Fin 2) K) 0 1 + y * (k : Matrix (Fin 2) (Fin 2) K) 1 1),
      hrow x y]

theorem IsRowIsometry.inv {k : GL (Fin 2) K} (hk : IsRowIsometry k) :
    IsRowIsometry k⁻¹ := by
  obtain ⟨hdet, hrow⟩ := hk
  have hcoe : ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      * ((k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := Units.inv_mul k
  constructor
  · have hd : ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det
        * ((k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
      rw [← Matrix.det_mul, hcoe, Matrix.det_one]
    have hnorm := congrArg norm hd
    rwa [norm_mul, hdet, mul_one, norm_one] at hnorm
  · intro x y
    set A := ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hA
    set B := ((k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hB
    have entry : ∀ i j : Fin 2,
        A i 0 * B 0 j + A i 1 * B 1 j = (1 : Matrix (Fin 2) (Fin 2) K) i j := by
      intro i j
      calc A i 0 * B 0 j + A i 1 * B 1 j
          = (A * B) i j := by rw [Matrix.mul_apply, Fin.sum_univ_two]
        _ = (1 : Matrix (Fin 2) (Fin 2) K) i j := by rw [hcoe]
    have e00 := entry 0 0
    have e01 := entry 0 1
    have e10 := entry 1 0
    have e11 := entry 1 1
    rw [Matrix.one_apply_eq] at e00 e11
    rw [Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide)] at e01
    rw [Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e10
    have hwx : (x * A 0 0 + y * A 1 0) * B 0 0 + (x * A 0 1 + y * A 1 1) * B 1 0 = x := by
      calc (x * A 0 0 + y * A 1 0) * B 0 0 + (x * A 0 1 + y * A 1 1) * B 1 0
          = x * (A 0 0 * B 0 0 + A 0 1 * B 1 0) + y * (A 1 0 * B 0 0 + A 1 1 * B 1 0) := by
            ring
        _ = x * 1 + y * 0 := by rw [e00, e10]
        _ = x := by ring
    have hwy : (x * A 0 0 + y * A 1 0) * B 0 1 + (x * A 0 1 + y * A 1 1) * B 1 1 = y := by
      calc (x * A 0 0 + y * A 1 0) * B 0 1 + (x * A 0 1 + y * A 1 1) * B 1 1
          = x * (A 0 0 * B 0 1 + A 0 1 * B 1 1) + y * (A 1 0 * B 0 1 + A 1 1 * B 1 1) := by
            ring
        _ = x * 0 + y * 1 := by rw [e01, e11]
        _ = y := by ring
    have key := hrow (x * A 0 0 + y * A 1 0) (x * A 0 1 + y * A 1 1)
    rw [hwx, hwy] at key
    exact key.symm

variable (K)

def rowIsometrySubgroup : Subgroup (GL (Fin 2) K) where
  carrier := {k : GL (Fin 2) K | IsRowIsometry k}
  one_mem' := isRowIsometry_one
  mul_mem' := fun hk hk' => IsRowIsometry.mul hk hk'
  inv_mem' := fun hk => IsRowIsometry.inv hk

variable {K}

theorem mem_rowIsometrySubgroup_iff {k : GL (Fin 2) K} :
    k ∈ rowIsometrySubgroup K ↔ IsRowIsometry k := Iff.rfl
theorem weyl_mem_rowIsometrySubgroup :
    (Matrix.GeneralLinearGroup.mk'' (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K)
      (by
        rw [Matrix.det_fin_two_of]
        norm_num) : GL (Fin 2) K) ∈ rowIsometrySubgroup K := by
  constructor
  · show ‖(!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K).det‖ = 1
    rw [Matrix.det_fin_two_of]
    norm_num
  · intro x y
    have h00 : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) 0 0 = 0 := rfl
    have h01 : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) 0 1 = 1 := rfl
    have h10 : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) 1 0 = -1 := rfl
    have h11 : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 := rfl
    show ‖x * (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) 0 0
          + y * (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2
        + ‖x * (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) 0 1
            + y * (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) 1 1‖ ^ 2
      = ‖x‖ ^ 2 + ‖y‖ ^ 2
    rw [h00, h01, h10, h11, mul_zero, mul_neg_one, zero_add, mul_one, mul_zero, add_zero,
      norm_neg]
    ring

end AutomorphicForm.WindowedSiegel

namespace AutomorphicForm

open WindowedSiegel


variable (K : Type*) [NormedField K]

def rowIsometrySubgroup₀ : Subgroup (GL (Fin 2) K) :=
  (Matrix.GeneralLinearGroup.det).ker ⊓ rowIsometrySubgroup K

theorem mem_rowIsometrySubgroup₀_iff {k : GL (Fin 2) K} :
    k ∈ rowIsometrySubgroup₀ K ↔
      (k : Matrix (Fin 2) (Fin 2) K).det = 1 ∧ IsRowIsometry k := by
  unfold rowIsometrySubgroup₀
  constructor
  · rintro ⟨hd, hi⟩
    exact ⟨Units.val_eq_one.mpr hd, hi⟩
  · rintro ⟨hd, hi⟩
    refine ⟨?_, hi⟩
    ext; exact hd

theorem rowIsometrySubgroup₀_le :
    rowIsometrySubgroup₀ K ≤ rowIsometrySubgroup K := inf_le_right

theorem weyl_mem_rowIsometrySubgroup₀ :
    (Matrix.GeneralLinearGroup.mk'' (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K)
      (by rw [Matrix.det_fin_two_of]; norm_num) : GL (Fin 2) K)
      ∈ rowIsometrySubgroup₀ K := by
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨?_, weyl_mem_rowIsometrySubgroup⟩
  show (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K).det = 1
  rw [Matrix.det_fin_two_of]; ring



theorem entries_of_mem_rowIsometrySubgroup₀ {k : GL (Fin 2) ℝ}
    (hk : k ∈ rowIsometrySubgroup₀ ℝ) :
    let a := (k : Matrix (Fin 2) (Fin 2) ℝ) 0 0
    let b := (k : Matrix (Fin 2) (Fin 2) ℝ) 0 1
    (k : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = -b ∧
      (k : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = a ∧ a ^ 2 + b ^ 2 = 1 := by
  obtain ⟨hd, hdn, hiso⟩ := (mem_rowIsometrySubgroup₀_iff ℝ).mp hk
  set a := (k : Matrix (Fin 2) (Fin 2) ℝ) 0 0
  set b := (k : Matrix (Fin 2) (Fin 2) ℝ) 0 1
  set c := (k : Matrix (Fin 2) (Fin 2) ℝ) 1 0
  set d := (k : Matrix (Fin 2) (Fin 2) ℝ) 1 1
  have h10 : a ^ 2 + b ^ 2 = 1 := by
    have := hiso 1 0
    simp only [one_mul, zero_mul, add_zero, Real.norm_eq_abs, sq_abs, norm_one,
      one_pow, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at this
    linarith
  have h01 : c ^ 2 + d ^ 2 = 1 := by
    have := hiso 0 1
    simp only [zero_mul, one_mul, zero_add, Real.norm_eq_abs, sq_abs, norm_one,
      one_pow, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at this
    linarith
  have h11 : a * c + b * d = 0 := by
    have h1 := hiso 1 1
    simp only [one_mul, Real.norm_eq_abs, sq_abs, norm_one, one_pow] at h1
    nlinarith [h10, h01]
  have hdet : a * d - b * c = 1 := by
    have := hd; rw [Matrix.det_fin_two] at this; linarith

  refine ⟨?_, ?_, h10⟩
  · nlinarith [sq_nonneg (a - d), sq_nonneg (b + c), h10, h01, h11, hdet]
  · nlinarith [sq_nonneg (a - d), sq_nonneg (b + c), h10, h01, h11, hdet]

def firstRowℂ (k : GL (Fin 2) ℝ) : ℂ :=
  ⟨(k : Matrix (Fin 2) (Fin 2) ℝ) 0 0, (k : Matrix (Fin 2) (Fin 2) ℝ) 0 1⟩

theorem normSq_firstRowℂ_of_mem {k : GL (Fin 2) ℝ}
    (hk : k ∈ rowIsometrySubgroup₀ ℝ) :
    Complex.normSq (firstRowℂ k) = 1 := by
  obtain ⟨_, _, hab⟩ := entries_of_mem_rowIsometrySubgroup₀ hk
  simp only [firstRowℂ, Complex.normSq_mk]
  nlinarith

theorem firstRowℂ_ne_zero_of_mem {k : GL (Fin 2) ℝ}
    (hk : k ∈ rowIsometrySubgroup₀ ℝ) :
    firstRowℂ k ≠ 0 := fun h0 => by
  have h := normSq_firstRowℂ_of_mem hk
  rw [h0, map_zero] at h
  exact one_ne_zero h.symm

theorem firstRowℂ_mul_of_mem {k k' : GL (Fin 2) ℝ}
    (hk' : k' ∈ rowIsometrySubgroup₀ ℝ) :
    firstRowℂ (k * k') = firstRowℂ k * firstRowℂ k' := by
  obtain ⟨hc', hd', _⟩ := entries_of_mem_rowIsometrySubgroup₀ hk'
  apply Complex.ext
  · show ((k * k' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = _
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hc',
      Complex.mul_re, firstRowℂ, firstRowℂ]
    ring
  · show ((k * k' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = _
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hd',
      Complex.mul_im, firstRowℂ, firstRowℂ]

noncomputable def archWeightOneℝ : rowIsometrySubgroup₀ ℝ →* ℂˣ where
  toFun k := Units.mk0 (firstRowℂ (k : GL (Fin 2) ℝ))
    (firstRowℂ_ne_zero_of_mem k.2)
  map_one' := Units.ext <| Complex.ext (by simp [firstRowℂ]) (by simp [firstRowℂ])
  map_mul' k k' := by
    ext
    exact firstRowℂ_mul_of_mem k'.2

noncomputable def archWeightCharℝ (n : ℤ) : rowIsometrySubgroup₀ ℝ →* ℂˣ :=
  (zpowGroupHom n).comp archWeightOneℝ

theorem archWeightOneℝ_weyl :
    (archWeightOneℝ
      ⟨_, weyl_mem_rowIsometrySubgroup₀ ℝ⟩ : ℂ) = ⟨0, 1⟩ := by
  show firstRowℂ _ = (⟨0, 1⟩ : ℂ)
  apply Complex.ext <;> simp [firstRowℂ]

theorem archWeightOneℝ_ne_one :
    archWeightOneℝ ⟨_, weyl_mem_rowIsometrySubgroup₀ ℝ⟩ ≠ 1 := by
  intro h
  have : (⟨0, 1⟩ : ℂ) = 1 := archWeightOneℝ_weyl ▸ (Units.val_eq_one.mpr h)
  simp [Complex.ext_iff] at this


end AutomorphicForm

namespace LanglandsTunnell.Converse

open Complex

namespace ArchR

def diagOne (y : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![y, 0; 0, 1]

def unip (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, x; 0, 1]

def weyl : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

def psi (x : ℝ) : ℂ := exp (2 * (Real.pi : ℂ) * I * x)

def glSet : Set (Fin 2 → Fin 2 → ℝ) := {M | (Matrix.of M).det ≠ 0}

def asPi (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (M : Fin 2 → Fin 2 → ℝ) : ℂ := W (Matrix.of M)

def diagOneMulCoords (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ := Matrix.of.symm
  (diagOne y * k)

def quasiChar (u : ℂ) (a : ZMod 2) (y : ℝ) : ℂ :=
  ((|y| : ℝ) : ℂ) ^ u * (if a = 0 then 1 else ((SignType.sign y : ℝ) : ℂ))

def centralChar (P : RealArchParam) (y : ℝ) : ℂ := quasiChar P.centralExponent P.centralSign y

def IsK (k : Matrix (Fin 2) (Fin 2) ℝ) : Prop := k ∈ Matrix.orthogonalGroup (Fin 2) ℝ

def zetaIntegrand (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ) (a :
  ZMod 2) (s : ℂ)
    (y : ℝ) : ℂ :=
  W (diagOne y * g) * quasiChar u a y * ((|y| : ℝ) : ℂ) ^ (s - 1) * ((|y| : ℝ) : ℂ)⁻¹

end ArchR

open ArchR in

/-- A real archimedean Whittaker datum: a smooth Whittaker function with
unipotent and central laws, an entire zeta function, and decay bounds. -/
structure ArchDatumR (P : RealArchParam) where

  W : Matrix (Fin 2) (Fin 2) ℝ → ℂ

  smooth : ContDiffOn ℝ (⊤ : ℕ∞) (asPi W) glSet

  unip_law : ∀ (x : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ), W (unip x * g) = psi x * W g

  central_law : ∀ (z : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ), z ≠ 0 →
    W (z • g) = centralChar P z * ((|z| : ℝ) : ℂ) * W g

  zetaEntire : Matrix (Fin 2) (Fin 2) ℝ → ℂ → ZMod 2 → ℂ → ℂ
  zetaEntire_differentiable : ∀ g u a, Differentiable ℂ (zetaEntire g u a)

  zeta_abscissa : ℝ
  zeta_integrable : ∀ g u a s, g.det ≠ 0 → zeta_abscissa < s.re + u.re →
    MeasureTheory.Integrable (zetaIntegrand W g u a s)

  zeta_eq : ∀ g u a s, g.det ≠ 0 → zeta_abscissa < s.re + u.re →
    ∫ y : ℝ, zetaIntegrand W g u a s y = (P.twist u a).archFactor s * zetaEntire g u a s

  functional_equation : ∀ g u a s, g.det ≠ 0 →
    zetaEntire (weyl * g) (-(u + P.centralExponent)) (a + P.centralSign) (1 - s)
      = (P.twist u a).epsilonFactor * zetaEntire g u a s

  zetaEntire_finiteOrder : ∀ g u a (A B : ℝ), ∃ C D : ℝ, ∀ s : ℂ, A ≤ s.re → s.re ≤ B →
    ‖zetaEntire g u a s‖ ≤ C * Real.exp (D * |s.im|)

  decay_top : ∀ (j N : ℕ), ∃ C : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), IsK k → 1 ≤ |y| →
    ‖iteratedFDerivWithin ℝ j (asPi W) glSet (diagOneMulCoords y k)‖ ≤ C * |y| ^ (-(N : ℝ))

  decay_zero : ∀ j : ℕ, ∃ (C σ : ℝ), ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), IsK k → y ≠ 0 → |y|
    ≤ 1 →
    ‖iteratedFDerivWithin ℝ j (asPi W) glSet (diagOneMulCoords y k)‖ ≤ C * |y| ^ (-σ)

namespace ArchDatumR

variable {P : RealArchParam}

def dualFun (D : ArchDatumR P) (g : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := (ArchR.centralChar P g.det)⁻¹
  * D.W g

end ArchDatumR
end LanglandsTunnell.Converse

namespace LanglandsTunnell.Converse

open ArchR AutomorphicForm MeasureTheory Set

private noncomputable def rotM (c d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![d / Real.sqrt (c ^ 2 + d ^ 2), -c / Real.sqrt (c ^ 2 + d ^ 2); c / Real.sqrt (c ^ 2 + d ^ 2),
    d / Real.sqrt (c ^ 2 + d ^ 2)]

private theorem sqrt_pos_of {c d : ℝ} (h : c ≠ 0 ∨ d ≠ 0) : 0 < Real.sqrt (c ^ 2 + d ^ 2) := by
  apply Real.sqrt_pos.2
  rcases h with h | h
  · have := sq_pos_of_ne_zero h; positivity
  · have := sq_pos_of_ne_zero h; positivity

private theorem det_rotM {c d : ℝ} (h : c ≠ 0 ∨ d ≠ 0) : (rotM c d).det = 1 := by
  have hr := sqrt_pos_of h
  have hr2 : Real.sqrt (c ^ 2 + d ^ 2) ^ 2 = c ^ 2 + d ^ 2 := Real.sq_sqrt (by positivity)
  rw [rotM, Matrix.det_fin_two_of]
  field_simp
  linarith [hr2]

private noncomputable def rotGL {c d : ℝ} (h : c ≠ 0 ∨ d ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (rotM c d) (by rw [det_rotM h]; exact one_ne_zero)

private theorem rotGL_coe {c d : ℝ} (h : c ≠ 0 ∨ d ≠ 0) : ((rotGL h : GL (Fin 2) ℝ) : Matrix (Fin
  2) (Fin 2) ℝ) = rotM c d := rfl

private theorem rotGL_mem {c d : ℝ} (h : c ≠ 0 ∨ d ≠ 0) : rotGL h ∈ rowIsometrySubgroup₀ ℝ := by
  have hr := sqrt_pos_of h
  have hr2 : Real.sqrt (c ^ 2 + d ^ 2) ^ 2 = c ^ 2 + d ^ 2 := Real.sq_sqrt (by positivity)
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨by rw [rotGL_coe, det_rotM h], ?_, ?_⟩
  · rw [rotGL_coe, det_rotM h, norm_one]
  · intro x y
    simp only [rotGL_coe, rotM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
    field_simp
    linear_combination (-(x ^ 2 + y ^ 2)) * hr2

private theorem archWeightCharℝ_zero (r : rowIsometrySubgroup₀ ℝ) : ((archWeightCharℝ 0 r : ℂˣ) :
  ℂ) = 1 := by
  show ((((archWeightOneℝ r) ^ (0 : ℤ)) : ℂˣ) : ℂ) = 1
  rw [zpow_zero, Units.val_one]

private theorem continuousOn_torus {P : RealArchParam} (D : ArchDatumR P) :
    ContinuousOn (fun τ : ℝ => D.W (diagOne τ)) {τ | τ ≠ 0} := by
  have hc : Continuous fun τ : ℝ => (fun i j => (!![τ, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j :
    Fin 2 → Fin 2 → ℝ) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  have hmaps : Set.MapsTo (fun τ : ℝ => (fun i j => (!![τ, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j
    : Fin 2 → Fin 2 → ℝ))
      {τ | τ ≠ 0} glSet := by
    intro τ hτ
    show (Matrix.of fun i j => (!![τ, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j).det ≠ 0
    rw [Matrix.det_fin_two]
    simpa using hτ
  have h := D.smooth.continuousOn.comp hc.continuousOn hmaps
  refine h.congr fun τ _ => ?_
  show D.W (diagOne τ) = D.W (Matrix.of fun i j => (!![τ, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j)
  rfl

private theorem exists_torus_ne_zero {P : RealArchParam} (D : ArchDatumR P)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ 0 r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDnz : ∃ g : GL (Fin 2) ℝ, D.W (g : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0) :
    ∃ τ : ℝ, τ ≠ 0 ∧ D.W (diagOne τ) ≠ 0 := by
  obtain ⟨g, hg⟩ := hDnz
  set G : Matrix (Fin 2) (Fin 2) ℝ := (g : Matrix (Fin 2) (Fin 2) ℝ) with hG
  set c : ℝ := G 1 0 with hc
  set d : ℝ := G 1 1 with hd
  have hdet : G.det ≠ 0 := by
    rw [hG]; exact (Matrix.isUnits_det_units g).ne_zero
  have hcd : c ≠ 0 ∨ d ≠ 0 := by
    by_contra h
    push Not at h
    apply hdet
    rw [Matrix.det_fin_two, ← hc, ← hd, h.1, h.2]; ring
  set r : ℝ := Real.sqrt (c ^ 2 + d ^ 2) with hr
  have hr0 : 0 < r := sqrt_pos_of hcd
  have hr2 : r ^ 2 = c ^ 2 + d ^ 2 := Real.sq_sqrt (by positivity)

  set α : ℝ := (G 0 0 * d - G 0 1 * c) / r with hα
  set β : ℝ := (G 0 0 * c + G 0 1 * d) / r with hβ
  set Xm : Matrix (Fin 2) (Fin 2) ℝ := !![α, β; 0, r] with hXm
  have hXrot : Xm * rotM c d = G := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [hXm, rotM, Matrix.mul_apply, Fin.sum_univ_two, hα, hβ, ← hr]
      field_simp
      linear_combination (-(G 0 0)) * hr2
    · simp [hXm, rotM, Matrix.mul_apply, Fin.sum_univ_two, hα, hβ, ← hr]
      field_simp
      linear_combination (-(G 0 1)) * hr2
    · simp [hXm, rotM, Matrix.mul_apply, Fin.sum_univ_two, ← hr, ← hc]
      field_simp
    · simp [hXm, rotM, Matrix.mul_apply, Fin.sum_univ_two, ← hr, ← hd]
      field_simp
  have hαr : α * r ≠ 0 := by
    have h1 : Xm.det = α * r := by rw [hXm, Matrix.det_fin_two_of]; ring
    have h2 : Xm.det * (rotM c d).det = G.det := by rw [← Matrix.det_mul, hXrot]
    rw [det_rotM hcd, mul_one, h1] at h2
    rw [h2]; exact hdet
  have hα0 : α ≠ 0 := fun h => hαr (by rw [h, zero_mul])
  set Xg : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero Xm
    (by rw [hXm, Matrix.det_fin_two_of]; simpa using hαr) with hXg
  have hXg_coe : ((Xg : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = Xm := rfl

  have h1 : D.W G = D.W Xm := by
    have h := hDW ⟨rotGL hcd, rotGL_mem hcd⟩ Xg
    rw [archWeightCharℝ_zero, one_mul, hXg_coe] at h
    rw [← h]
    congr 1
    rw [Units.val_mul, hXg_coe]
    exact hXrot.symm

  have hXm_eq : Xm = r • (unip (β / r) * diagOne (α / r)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hXm, unip, diagOne, Matrix.smul_apply] <;>
      field_simp
  have h2 : D.W Xm = centralChar P r * ((|r| : ℝ) : ℂ) * (psi (β / r) * D.W (diagOne (α / r))) := by
    rw [hXm_eq, D.central_law r _ hr0.ne', D.unip_law]
  refine ⟨α / r, div_ne_zero hα0 hr0.ne', fun h0 => hg ?_⟩
  show D.W G = 0
  rw [h1, h2, h0, mul_zero, mul_zero]



open LanglandsTunnell.Converse.ArchR Set

private theorem archFactor_twist_ne_zero (u₁ u₂ : ℂ) (c : ZMod 2) {s : ℂ} (hs : ‖u₁‖ + ‖u₂‖ + 1 <
  s.re) :
    ((RealArchParam.principal u₁ c u₂ c).twist 0 c).archFactor s ≠ 0 := by
  have hcc : c + c = 0 := by
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with h | h <;> subst h <;> decide
  simp only [RealArchParam.twist, RealArchParam.archFactor, RealArchParam.gammaR,
    RealArchParam.gammaC, hcc, signShift_zero,
    add_zero, Multiset.map_zero, Multiset.prod_zero, mul_one, Multiset.insert_eq_cons,
      Multiset.map_cons,
    Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton]
  have h1 : 0 < (s + u₁).re := by
    rw [Complex.add_re]; have := Complex.abs_re_le_norm u₁; have := neg_abs_le u₁.re; linarith
      [norm_nonneg u₂]
  have h2 : 0 < (s + u₂).re := by
    rw [Complex.add_re]; have := Complex.abs_re_le_norm u₂; have := neg_abs_le u₂.re; linarith
      [norm_nonneg u₁]
  exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos h1) (Complex.Gammaℝ_ne_zero_of_re_pos h2)

private theorem quasiChar_zero_neg {c : ZMod 2} {t : ℝ} (ht : 0 < t) :
    quasiChar 0 c (-t) = (-1 : ℂ) ^ c.val := by
  unfold quasiChar
  rw [Complex.cpow_zero, one_mul]
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with h | h <;> subst h
  · simp
  · simp only [show ((1 : ZMod 2) = 0) = False from by decide, ite_false]
    have hs : SignType.sign (-t) = -1 := by rw [Left.sign_neg, sign_pos ht]
    rw [hs]
    simp [show (1 : ZMod 2).val = 1 from rfl]

private theorem quasiChar_zero_pos {c : ZMod 2} {t : ℝ} (ht : 0 < t) : quasiChar 0 c t = 1 := by
  unfold quasiChar
  rw [Complex.cpow_zero, one_mul]
  split_ifs
  · rfl
  · rw [sign_pos ht]; simp

private theorem neg_one_pow_mul_self (c : ZMod 2) : (-1 : ℂ) ^ c.val * (-1 : ℂ) ^ c.val = 1 := by
  rw [← mul_pow, neg_mul_neg, one_mul, one_pow]


/-- For a weight-zero archimedean datum of principal-series parity type,
some point to the right of any given abscissa has convergent, nonzero
Mellin transform along the diagonal torus. -/
theorem ArchDatumR.exists_lt_mellin_W_diagOne_ne_zero_of_weightZero_of_parity
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (u₁ u₂ : ℂ) (c : ZMod 2) (hP : P₂ = RealArchParam.principal u₁ c u₂ c)
    (hpar : ∀ τ : ℝ, τ ≠ 0 → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c.val * D.W (ArchR.diagOne τ))
    (hDW0 : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = D.W (x : Matrix
          (Fin 2) (Fin 2) ℝ))
    (hDnz : ∃ g : GL (Fin 2) ℝ, D.W (g : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0) (x₀ : ℝ) :
    ∃ x : ℝ, x₀ < x ∧ MellinConvergent (fun τ : ℝ => D.W (ArchR.diagOne τ)) (x : ℂ) ∧
      mellin (fun τ : ℝ => D.W (ArchR.diagOne τ)) (x : ℂ) ≠ 0 := by
  set f : ℝ → ℂ := fun τ => D.W (diagOne τ) with hf

  have hDW' : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ 0 r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ) := fun r x => by
    rw [hDW0, archWeightCharℝ_zero, one_mul]
  obtain ⟨τ₀, hτ₀, hne⟩ := exists_torus_ne_zero D hDW' hDnz
  have hcont := continuousOn_torus D

  set A : ℝ := D.zeta_abscissa with hA
  have hkey : ∀ s : ℂ, A < s.re →
      MellinConvergent f (s - 1) ∧
        2 * mellin f (s - 1) = (P₂.twist 0 c).archFactor s * D.zetaEntire 1 0 c s := by
    intro s hs
    have hdet : (1 : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by simp
    have hs' : D.zeta_abscissa < s.re + (0 : ℂ).re := by simpa using hs
    have hint := D.zeta_integrable 1 0 c s hdet hs'
    have heq := D.zeta_eq 1 0 c s hdet hs'

    have hpos : ∀ t ∈ Ioi (0 : ℝ), zetaIntegrand D.W 1 0 c s t = (t : ℂ) ^ (s - 1 - 1) • f t := by
      intro t ht
      have ht : 0 < t := ht
      have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
      simp only [zetaIntegrand, Matrix.mul_one, quasiChar_zero_pos ht, abs_of_pos ht, smul_eq_mul,
        hf]
      rw [show s - 1 - 1 = (s - 1) + (-1 : ℂ) by ring, Complex.cpow_add _ _ ht0,
        Complex.cpow_neg_one]
      ring
    have hneg : ∀ t ∈ Ioi (0 : ℝ), zetaIntegrand D.W 1 0 c s (-t) = zetaIntegrand D.W 1 0 c s t :=
      by
      intro t ht
      have ht : 0 < t := ht
      simp only [zetaIntegrand, Matrix.mul_one, quasiChar_zero_pos ht, quasiChar_zero_neg ht,
        abs_neg, hpar t ht.ne']
      linear_combination (D.W (diagOne t) * (((|t| : ℝ) : ℂ) ^ (s - 1)) * (((|t| : ℝ) : ℂ))⁻¹) *
        neg_one_pow_mul_self c
    have hI : IntegrableOn (zetaIntegrand D.W 1 0 c s) (Ioi 0) := hint.integrableOn
    have hconv : MellinConvergent f (s - 1) := (hI.congr_fun hpos measurableSet_Ioi)
    refine ⟨hconv, ?_⟩
    have hsplit := intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hI
    have hIic : ∫ t in Iic (0 : ℝ), zetaIntegrand D.W 1 0 c s t = ∫ t in Ioi (0 : ℝ), zetaIntegrand
      D.W 1 0 c s t := by
      rw [← neg_zero, ← integral_comp_neg_Ioi 0 (zetaIntegrand D.W 1 0 c s), neg_zero]
      exact setIntegral_congr_fun measurableSet_Ioi hneg
    have hmel : ∫ t in Ioi (0 : ℝ), zetaIntegrand D.W 1 0 c s t = mellin f (s - 1) := by
      rw [mellin]; exact setIntegral_congr_fun measurableSet_Ioi hpos
    rw [← heq, ← hsplit, hIic, hmel]
    ring

  by_contra hcon
  push Not at hcon
  set B : ℝ := max (max x₀ (A - 1)) (‖u₁‖ + ‖u₂‖ + 1) + 1 with hB
  have hBx : x₀ + 1 ≤ B := by
    have h1 := le_max_left (max x₀ (A - 1)) (‖u₁‖ + ‖u₂‖ + 1)
    have h2 := le_max_left x₀ (A - 1)
    linarith
  have hBA : A ≤ B := by
    have h1 := le_max_left (max x₀ (A - 1)) (‖u₁‖ + ‖u₂‖ + 1)
    have h2 := le_max_right x₀ (A - 1)
    linarith
  have hBu : ‖u₁‖ + ‖u₂‖ + 1 < B := by
    have h1 := le_max_right (max x₀ (A - 1)) (‖u₁‖ + ‖u₂‖ + 1)
    linarith

  have hzero : ∀ x : ℝ, B < x → D.zetaEntire 1 0 c (x : ℂ) = 0 := by
    intro x hx
    have hxA : A < ((x : ℂ)).re := by simp; linarith
    obtain ⟨hconv, hk⟩ := hkey x hxA
    have hm : mellin f ((x : ℂ) - 1) = 0 := by
      have h := hcon (x - 1) (by linarith)
      have : ((x - 1 : ℝ) : ℂ) = (x : ℂ) - 1 := by push_cast; ring
      rw [this] at h
      exact h hconv
    rw [hm, mul_zero] at hk
    have hAF : (P₂.twist 0 c).archFactor (x : ℂ) ≠ 0 := by
      rw [hP]; exact archFactor_twist_ne_zero u₁ u₂ c (by simp; linarith)
    exact (mul_eq_zero.1 hk.symm).resolve_left hAF

  have hent : AnalyticOnNhd ℂ (D.zetaEntire 1 0 c) univ :=
    (D.zetaEntire_differentiable 1 0 c).differentiableOn.analyticOnNhd isOpen_univ
  have hall : ∀ z : ℂ, D.zetaEntire 1 0 c z = 0 := by
    have z₀mem : ((B + 1 : ℝ) : ℂ) ∈ (univ : Set ℂ) := mem_univ _
    rcases (hent _ z₀mem).eventually_eq_zero_or_eventually_ne_zero with h | h
    · intro z
      exact hent.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ z₀mem h
        (mem_univ z)
    · exfalso
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
      obtain ⟨ε, hε, hball⟩ := h
      have hpt : dist (((B + 1 + ε / 2 : ℝ)) : ℂ) ((B + 1 : ℝ) : ℂ) < ε := by
        rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        rw [show B + 1 + ε / 2 - (B + 1) = ε / 2 by ring, abs_of_pos (by linarith)]
        linarith
      have hne' : ((B + 1 + ε / 2 : ℝ) : ℂ) ≠ ((B + 1 : ℝ) : ℂ) := by
        intro h; have := Complex.ofReal_injective h; linarith
      exact hball hpt hne' (hzero _ (by linarith))

  have hmel0 : ∀ w : ℂ, A - 1 < w.re → mellin f w = 0 := by
    intro w hw
    obtain ⟨-, hk⟩ := hkey (w + 1) (by simp; linarith)
    rw [hall, mul_zero, show w + 1 - 1 = w by ring] at hk
    exact (mul_eq_zero.1 hk).resolve_left two_ne_zero

  have hfzero : ∀ x : ℝ, 0 < x → f x = 0 := by
    intro x hx
    have hconvB : MellinConvergent f (B : ℂ) := by
      have := (hkey ((B : ℂ) + 1) (by simp; linarith)).1
      rwa [show (B : ℂ) + 1 - 1 = (B : ℂ) by ring] at this
    have hline : ∀ y : ℝ, mellin f ((B : ℂ) + (y : ℂ) * Complex.I) = 0 := fun y =>
      hmel0 _ (by simp; linarith)
    have hvert : Complex.VerticalIntegrable (mellin f) B := by
      have : (fun y : ℝ => mellin f ((B : ℂ) + (y : ℂ) * Complex.I)) = 0 := funext hline
      rw [Complex.VerticalIntegrable, this]; exact integrable_zero _ _ _
    have hcx : ContinuousAt f x := (hcont x hx.ne').continuousAt (isOpen_ne.mem_nhds hx.ne')
    have hinv := mellinInv_mellin_eq B f hx hconvB hvert hcx
    rw [← hinv, mellinInv]
    simp only [hline, smul_zero, integral_zero]

  rcases lt_or_gt_of_ne hτ₀ with hlt | hgt
  · apply hne
    have h := hpar (-τ₀) (neg_ne_zero.2 hτ₀)
    rw [neg_neg] at h
    have h0 := hfzero (-τ₀) (by linarith)
    simp only [hf] at h0
    rw [h, h0, mul_zero]
  · exact hne (hfzero τ₀ hgt)


end LanglandsTunnell.Converse
