/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.QPochhammer
public import MathlibExt.NumberTheory.ModularForms.JacobiTheta.Ramanujan
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import MathlibExt.NumberTheory.ModularForms.OldForms
import MathlibExt.GroupTheory.CyclicSubgroupsZModSquare
import MathlibExt.NumberTheory.ModularForms.SturmBoundGamma0
import MathlibExt.NumberTheory.ModularForms.QParamProduct
import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanPsiFChi
import MathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct
import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
import all Mathlib.Combinatorics.Enumerative.Pentagonal.Basic
import all Mathlib.NumberTheory.ArithmeticFunction.Misc
import all Mathlib.NumberTheory.Divisors
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Eisenstein-series formula for the level-40 theta product

We prove `MetaMathlibExt.phi_sq_mul_phi_sq_ten_eisenstein` on the open unit disk.
After clearing the eta-product denominators and squaring, the difference is a
weight-32 modular form on Γ₀(40). We use Sturm's bound and exact integer
arithmetic on the initial coefficients, then recover the sign from the leading
coefficient of the cleared eta product.
-/

open scoped MatrixGroups ModularForm Real UpperHalfPlane BigOperators Manifold
open Complex Matrix.SpecialLinearGroup ModularGroup ModularForm
open UpperHalfPlane hiding I

namespace MetaMathlibExt

/-- `f_k = (x;x)_∞` at `x = q^k`. -/
local notation "𝔣" x:max => QPochhammer.qPochhammerInfRaw x x
/-- Ramanujan's `φ(x) = f(x,x) = ∑_{n ∈ ℤ} x^{n²}`. -/
local notation "φ" x:max => ramanujanThetaRaw x x
/-- The weight-two Eisenstein series `P(x) = 1 - 24 ∑_{m ≥ 1} m x^m / (1 - x^m)`. -/
local notation "𝐏" x:max =>
  (1 - 24 * tsum fun m : ℕ => ((m + 1 : ℕ) : ℂ) * x ^ (m + 1) / (1 - x ^ (m + 1)))

local notation "𝕢" => Function.Periodic.qParam 1

namespace phi_sq_mul_phi_sq_ten_eisenstein

-- The two components of the eta-squared multiplier are determined by
-- the reductions of the matrix modulo 3 and modulo 4.
private def phase3 (a b c d : ZMod 3) : ZMod 3 :=
  if a = 0 then c * (d + a) else a * (b - c)

private def phase4 (a b c d : ZMod 4) : ZMod 4 :=
  if a = 1 ∨ a = -1 then a * (b - c) + (a - 1) else c * (d + a + 1)

private lemma phase3_mulT : ∀ a b c d : ZMod 3, a * d - b * c = 1 →
    phase3 a (a + b) c (c + d) = phase3 a b c d + 1 := by decide

private lemma phase3_mulS : ∀ a b c d : ZMod 3, a * d - b * c = 1 →
    phase3 b (-a) d (-c) = phase3 a b c d := by decide

private lemma phase4_mulT : ∀ a b c d : ZMod 4, a * d - b * c = 1 →
    phase4 a (a + b) c (c + d) = phase4 a b c d + 1 := by decide

private lemma phase4_mulS : ∀ a b c d : ZMod 4, a * d - b * c = 1 →
    phase4 b (-a) d (-c) = phase4 a b c d + 1 := by decide

private def phase (γ : SL(2, ℤ)) : ZMod 3 × ZMod 4 :=
  (phase3 (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1), phase4 (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1))

private lemma phase_one : phase 1 = 0 := by
  norm_num [phase, phase3, phase4]

private lemma phase_T (γ : SL(2, ℤ)) : phase (γ * T) = phase γ + (1, 1) := by
  have hd : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact γ.2
  have h3 := congrArg (fun x : ℤ => (x : ZMod 3)) hd
  have h4 := congrArg (fun x : ℤ => (x : ZMod 4)) hd
  push_cast at h3 h4
  exact Prod.ext
    (by simpa [phase, T, Matrix.mul_apply, Fin.sum_univ_two] using phase3_mulT _ _ _ _ h3)
    (by simpa [phase, T, Matrix.mul_apply, Fin.sum_univ_two] using phase4_mulT _ _ _ _ h4)

private lemma phase_S (γ : SL(2, ℤ)) : phase (γ * S) = phase γ + (0, 1) := by
  have hd : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact γ.2
  have h3 := congrArg (fun x : ℤ => (x : ZMod 3)) hd
  have h4 := congrArg (fun x : ℤ => (x : ZMod 4)) hd
  push_cast at h3 h4
  exact Prod.ext
    (by simpa [phase, S, Matrix.mul_apply, Fin.sum_univ_two] using phase3_mulS _ _ _ _ h3)
    (by simpa [phase, S, Matrix.mul_apply, Fin.sum_univ_two] using phase4_mulS _ _ _ _ h4)

private lemma phase_mul (γ δ : SL(2, ℤ)) : phase (γ * δ) = phase γ + phase δ := by
  have hδ : δ ∈ Subgroup.closure {S, T} := by simp [SpecialLinearGroup.SL2Z_generators]
  induction hδ using Subgroup.closure_induction_right with
  | one => simp [phase_one]
  | mul_right a _ b hbmem hb =>
    rcases (by simpa using hbmem : b = S ∨ b = T) with rfl | rfl
    · rw [← mul_assoc, phase_S, phase_S, hb, add_assoc]
    · rw [← mul_assoc, phase_T, phase_T, hb, add_assoc]
  | mul_inv_cancel a _ b hbmem hb =>
    rcases (by simpa using hbmem : b = S ∨ b = T) with rfl | rfl
    · apply add_right_cancel (b := (0, 1))
      rw [← phase_S, mul_assoc, inv_mul_cancel_right,
        add_assoc, ← phase_S, inv_mul_cancel_right]
      exact hb
    · apply add_right_cancel (b := (1, 1))
      rw [← phase_T, mul_assoc, inv_mul_cancel_right,
        add_assoc, ← phase_T, inv_mul_cancel_right]
      exact hb

private noncomputable def multiplier (x : ZMod 3 × ZMod 4) : ℂ :=
  ZMod.stdAddChar x.1 * ZMod.stdAddChar (-x.2)

private lemma multiplier_zero : multiplier 0 = 1 := by simp [multiplier]

private lemma multiplier_add (x y : ZMod 3 × ZMod 4) :
    multiplier (x + y) = multiplier x * multiplier y := by
  simp only [multiplier, Prod.fst_add, Prod.snd_add, neg_add,
    AddChar.map_add_eq_mul]
  ring

private lemma multiplier_T : multiplier (1, 1) = exp (π * I / 6) := by
  simp only [multiplier]
  rw [show (1 : ZMod 3) = ((1 : ℤ) : ZMod 3) by rfl,
      show -(1 : ZMod 4) = ((-1 : ℤ) : ZMod 4) by simp,
      ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ← exp_add]
  congr 1
  push_cast
  ring

private lemma multiplier_S : multiplier (0, 1) = -I := by
  simp only [multiplier, AddChar.map_zero_eq_one, one_mul]
  rw [show -(1 : ZMod 4) = ((-1 : ℤ) : ZMod 4) by simp, ZMod.stdAddChar_coe]
  norm_num only [Int.cast_ofNat]
  rw [show 2 * π * I * (-1 : ℂ) / 4 = -(π / 2 * I) by ring, exp_neg]
  simp [exp_pi_div_two_mul_I, inv_I]

private noncomputable def etaSquare (z : ℍ) : ℂ := η z ^ 2

private lemma etaSquare_T : etaSquare ∣[(1 : ℤ)] T = multiplier (phase T) • etaSquare := by
  ext z
  have h := phase_T 1
  rw [one_mul, phase_one, zero_add] at h
  rw [h, multiplier_T]
  simp only [SL_slash_apply, modular_T_smul, coe_vadd, Complex.ofReal_one,
    Pi.smul_apply, smul_eq_mul, etaSquare, ModularForm.eta]
  have hdenom : denom T z = 1 := by simp [ModularGroup.denom_apply, T]
  rw [hdenom, one_zpow, mul_one, add_comm (1 : ℂ), show Function.Periodic.qParam 24 ((z : ℂ) + 1) =
    exp (π * I / 12) * Function.Periodic.qParam 24 z by
      simp only [Function.Periodic.qParam, ofReal_ofNat]
      rw [show 2 * π * I * ((z : ℂ) + 1) / 24 = π * I / 12 + 2 * π * I * z / 24 by ring]
      rw [exp_add]]
  have hper : Function.Periodic (Function.Periodic.qParam 1 : ℂ → ℂ) 1 := by
    intro z
    simp [Function.Periodic.qParam, mul_add, exp_add]
  simp only [eta_q, show ∀ w, Function.Periodic.qParam 1 (w + 1) =
    Function.Periodic.qParam 1 w from hper, mul_pow, ← exp_nat_mul]
  push_cast
  ring_nf

private lemma etaSquare_S : etaSquare ∣[(1 : ℤ)] S = multiplier (phase S) • etaSquare := by
  ext z
  have h := phase_S 1
  rw [one_mul, phase_one, zero_add] at h
  rw [h, multiplier_S]
  simp only [SL_slash_apply, ModularGroup.denom_S, zpow_neg_one, modular_S_smul,
    Pi.smul_apply, smul_eq_mul, etaSquare]
  have he := eta_comp_eq_csqrt_I_inv z.2
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, neg_div, one_div] at he
  rw [inv_neg, he]
  have hs (w : ℂ) : w.sqrt ^ 2 = w := by
    exact Complex.cpow_nat_inv_pow w two_ne_zero
  rw [mul_pow, mul_pow, inv_pow, hs, hs, inv_I]
  field_simp [z.ne_zero]

private lemma etaSquare_slash (γ : SL(2, ℤ)) :
    etaSquare ∣[(1 : ℤ)] γ = multiplier (phase γ) • etaSquare := by
  have hγ : γ ∈ Subgroup.closure {S, T} := by simp [SpecialLinearGroup.SL2Z_generators]
  induction hγ using Subgroup.closure_induction with
  | mem a ha =>
    rcases (by simpa using ha : a = S ∨ a = T) with rfl | rfl
    · exact etaSquare_S
    · exact etaSquare_T
  | one => simp [phase_one, multiplier_zero, SlashAction.slash_one]
  | mul a b _ _ ha hb =>
    rw [SlashAction.slash_mul, ha, phase_mul, multiplier_add, SL_smul_slash, hb, smul_smul]
  | inv a _ ha =>
    have h := congrArg (fun f : ℍ → ℂ => f ∣[(1 : ℤ)] a⁻¹) ha
    rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one, SL_smul_slash] at h
    have hm : multiplier (phase a⁻¹) * multiplier (phase a) = 1 := by
      rw [← multiplier_add, ← phase_mul, inv_mul_cancel, phase_one, multiplier_zero]
    have h' := congrArg (multiplier (phase a⁻¹) • ·) h
    rwa [smul_smul, hm, one_smul, eq_comm] at h'

-- Rescale by the eight positive divisors of 40. For a matrix in Γ₀(40),
-- the conjugated matrices still have integral entries.
private def level (i : Fin 8) : ℕ := ![1, 2, 4, 5, 8, 10, 20, 40] i

private def colevel (i : Fin 8) : ℕ := 40 / level i

private lemma level_pos (i : Fin 8) : 0 < level i := by
  fin_cases i <;> decide

private lemma level_dvd (i : Fin 8) : level i ∣ 40 := by
  fin_cases i <;> decide

private noncomputable def dilate (i : Fin 8) : GL (Fin 2) ℝ := heckeDiagMatrix (level i)

private lemma dilate_apply (i : Fin 8) (z : ℍ) :
    ((dilate i • z : ℍ) : ℂ) = (level i : ℂ) * (z : ℂ) :=
  coe_heckeDiagMatrix_smul (level_pos i).ne' z

private def rescale (i : Fin 8) (γ : SL(2, ℤ)) (k : ℤ)
    (hc : γ 1 0 = 40 * k) : SL(2, ℤ) :=
  ⟨!![γ 0 0, (level i : ℤ) * γ 0 1; ((colevel i : ℕ) : ℤ) * k, γ 1 1], by
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      rw [← Matrix.det_fin_two]; exact γ.2
    have hm : (level i : ℤ) * ((colevel i : ℕ) : ℤ) = 40 := by
      exact_mod_cast (Nat.mul_div_cancel' (level_dvd i) : level i * colevel i = 40)
    rw [hc] at hdet
    rw [Matrix.det_fin_two_of]
    linear_combination hdet - γ 0 1 * k * hm⟩

private lemma rescale_denom (i : Fin 8) (γ : SL(2, ℤ)) (k : ℤ)
    (hc : γ 1 0 = 40 * k) (z : ℍ) :
    denom (rescale i γ k hc) ((dilate i • z : ℍ) : ℂ) = denom γ z := by
  have hm : (level i : ℂ) * ((colevel i : ℕ) : ℂ) = 40 := by
    exact_mod_cast (Nat.mul_div_cancel' (level_dvd i) : level i * colevel i = 40)
  rw [ModularGroup.denom_apply, ModularGroup.denom_apply, dilate_apply, hc]
  change (↑(((colevel i : ℕ) : ℤ) * k) : ℂ) * (↑(level i) * z) + ↑(γ 1 1) =
    ↑(40 * k : ℤ) * z + ↑(γ 1 1)
  push_cast
  linear_combination (k : ℂ) * (z : ℂ) * hm

private lemma rescale_smul (i : Fin 8) (γ : SL(2, ℤ)) (k : ℤ)
    (hc : γ 1 0 = 40 * k) (z : ℍ) :
    rescale i γ k hc • (dilate i • z) = dilate i • (γ • z) := by
  apply UpperHalfPlane.ext
  rw [dilate_apply, coe_specialLinearGroup_apply, coe_specialLinearGroup_apply]
  change ((γ 0 0 : ℂ) * ((dilate i • z : ℍ) : ℂ) + ↑((level i : ℤ) * γ 0 1)) /
    denom (rescale i γ k hc) ((dilate i • z : ℍ) : ℂ) =
    (level i : ℂ) * (((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ)) / denom γ z)
  rw [rescale_denom, dilate_apply]
  push_cast
  ring

private lemma phase3_rescale_calc : ∀ (a b c d e f : ZMod 3), e * f = 1 →
    phase3 a (e * b) (f * c) d = e * phase3 a b c d := by decide

private lemma phase_rescale_fst (i : Fin 8) (γ : SL(2, ℤ)) (k : ℤ)
    (hc : γ 1 0 = 40 * k) :
    (phase (rescale i γ k hc)).1 = (level i : ZMod 3) * (phase γ).1 := by
  have hm : (level i : ZMod 3) * ((colevel i : ℕ) : ZMod 3) = 1 := by
    rw [← Nat.cast_mul, colevel, Nat.mul_div_cancel' (level_dvd i)]
    decide
  have hk : (40 : ZMod 3) * (k : ZMod 3) = k := by
    rw [show (40 : ZMod 3) = 1 by decide, one_mul]
  change phase3 _ (↑((level i : ℤ) * γ 0 1)) (↑(((colevel i : ℕ) : ℤ) * k)) _ =
    (level i : ZMod 3) * phase3 (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
  rw [hc]
  push_cast
  rw [hk]
  exact phase3_rescale_calc (γ 0 0) (γ 0 1) k (γ 1 1) (level i) (colevel i : ℕ) hm

private lemma mod4_first (γ : SL(2, ℤ)) {k : ℤ} (hc : γ 1 0 = 40 * k) :
    (γ 0 0 : ZMod 4) = 1 ∨ (γ 0 0 : ZMod 4) = -1 := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact γ.2
  have hdet4 := congrArg (fun n : ℤ => (n : ZMod 4)) hdet
  rw [hc] at hdet4
  push_cast at hdet4
  rw [show (40 : ZMod 4) = 0 by decide, zero_mul, mul_zero, sub_zero] at hdet4
  exact (by decide : ∀ a d : ZMod 4, a * d = 1 → a = 1 ∨ a = -1) _ _ hdet4

private lemma phase_rescale_snd (i : Fin 8) (γ : SL(2, ℤ)) (k : ℤ)
    (hc : γ 1 0 = 40 * k) :
    (phase (rescale i γ k hc)).2 =
      (γ 0 0 : ZMod 4) * ((level i : ZMod 4) * (γ 0 1 : ZMod 4) -
        ((colevel i : ℕ) : ZMod 4) * (k : ZMod 4)) + ((γ 0 0 : ZMod 4) - 1) := by
  change phase4 (γ 0 0) (↑((level i : ℤ) * γ 0 1)) (↑(((colevel i : ℕ) : ℤ) * k))
    (γ 1 1) = _
  simp only [phase4, mod4_first γ hc, ite_true]
  push_cast
  rfl

private lemma multiplier_sum_pow (r : Fin 8 → ℕ) (p : Fin 8 → ZMod 3 × ZMod 4) :
    multiplier (∑ i, r i • p i) = ∏ i, multiplier (p i) ^ r i := by
  have hp (n : ℕ) (x : ZMod 3 × ZMod 4) : multiplier (n • x) = multiplier x ^ n := by
    induction n with
    | zero => simp [multiplier_zero]
    | succ n ih => rw [succ_nsmul, multiplier_add, ih, pow_succ]
  have h : ∀ s : Finset (Fin 8),
      multiplier (∑ i ∈ s, r i • p i) = ∏ i ∈ s, multiplier (p i) ^ r i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [multiplier_zero]
    | insert i s hi ih =>
      simp only [Finset.sum_insert hi, Finset.prod_insert hi, multiplier_add, hp, ih]
  exact h Finset.univ

private lemma phases_cancel (r : Fin 8 → ℕ) (γ : SL(2, ℤ)) (k : ℤ)
    (hc : γ 1 0 = 40 * k) (hT : 12 ∣ ∑ i, level i * r i)
    (hS : 4 ∣ ∑ i, (colevel i) * r i)
    (hW : 2 ∣ ∑ i, r i) :
    ∑ i, r i • phase (rescale i γ k hc) = 0 := by
  have castT (m : ℕ) (hm : m ∣ 12) : (↑(∑ i, level i * r i) : ZMod m) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_trans hm hT)
  have castS : (↑(∑ i, (colevel i) * r i) : ZMod 4) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hS
  have hW' : (↑(∑ i, r i) : ZMod 4) * ((γ 0 0 : ZMod 4) - 1) = 0 := by
    obtain ⟨x, hx⟩ := hW
    rw [hx, Nat.cast_mul]
    rcases mod4_first γ hc with ha | ha
    · simp [ha]
    · rw [ha, mul_comm, ← mul_assoc]
      have hz : (-(1 : ZMod 4) - 1) * ((2 : ℕ) : ZMod 4) = 0 := by decide
      rw [hz, zero_mul]
  apply Prod.ext
  · have ht := castT 3 (by decide)
    push_cast at ht
    simp only [Prod.fst_sum, nsmul_eq_mul, Prod.fst_mul, Prod.fst_natCast,
      phase_rescale_fst, Prod.fst_zero]
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
    have hs : (∑ i, (r i : ZMod 3) * (level i : ZMod 3)) = 0 := by
      simpa only [mul_comm] using ht
    rw [hs, zero_mul]
  · have ht := castT 4 (by decide)
    push_cast at ht castS hW'
    simp only [Prod.snd_sum, nsmul_eq_mul, Prod.snd_mul, Prod.snd_natCast,
      phase_rescale_snd, Prod.snd_zero]
    calc
      _ = (γ 0 0 : ZMod 4) *
        (((∑ i, (level i : ZMod 4) * (r i : ZMod 4))) * (γ 0 1 : ZMod 4) -
         ((∑ i, ((colevel i : ℕ) : ZMod 4) * (r i : ZMod 4))) * (k : ZMod 4)) +
        (∑ i, (r i : ZMod 4)) * ((γ 0 0 : ZMod 4) - 1) := by
          simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
            ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ = 0 := by rw [ht, castS, hW']; ring

-- The products only use nonnegative powers of eta squared. This lets
-- us verify boundedness at all cusps using the boundedness of Δ.
private noncomputable def etaProduct (r : Fin 8 → ℕ) (z : ℍ) : ℂ :=
  ∏ i, etaSquare (dilate i • z) ^ r i

private lemma etaProduct_slash (r : Fin 8 → ℕ) (hT : 12 ∣ ∑ i, level i * r i)
    (hS : 4 ∣ ∑ i, (colevel i) * r i) (hW : 2 ∣ ∑ i, r i)
    {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 40) :
    etaProduct r ∣[((∑ i, r i : ℕ) : ℤ)] γ = etaProduct r := by
  have hc : (40 : ℤ) ∣ γ 1 0 := by
    have h := CongruenceSubgroup.Gamma0_mem.mp hγ
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
  obtain ⟨k, hk⟩ := hc
  ext z
  rw [SL_slash_apply]
  have he (i : Fin 8) : etaSquare (dilate i • (γ • z)) =
      multiplier (phase (rescale i γ k hk)) * etaSquare (dilate i • z) * denom γ z := by
    have h := congrFun (etaSquare_slash (rescale i γ k hk)) (dilate i • z)
    rw [SL_slash_apply, rescale_smul, rescale_denom, zpow_neg_one, Pi.smul_apply,
      smul_eq_mul, mul_inv_eq_iff_eq_mul₀ (denom_ne_zero γ z)] at h
    exact h
  simp only [etaProduct, he, mul_pow, Finset.prod_mul_distrib, ← Finset.prod_pow_eq_pow_sum,
    zpow_neg, zpow_natCast,
    ← multiplier_sum_pow, phases_cancel r γ k hk hT hS hW, multiplier_zero, one_mul]
  have hprod : (∏ i, denom γ z ^ r i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (denom_ne_zero γ z)
  rw [mul_assoc, mul_inv_cancel₀ hprod, mul_one]

open Filter
open EisensteinSeries

private lemma dilate_rat (i : Fin 8) :
    (CuspForm.heckeDiagMatrixQ (level_pos i).ne').map (Rat.castHom ℝ) = dilate i := by
  apply Units.ext
  rw [dilate, val_heckeDiagMatrix (level_pos i).ne']
  unfold CuspForm.heckeDiagMatrixQ
  ext j k
  fin_cases j <;> fin_cases k <;> simp

private lemma bounded_dilate (i : Fin 8) (w : ℤ) {f : ℍ → ℂ}
    (hf : ∀ {c}, IsCusp c 𝒮ℒ → OnePoint.IsBoundedAt c f w)
    {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    OnePoint.IsBoundedAt c (f ∣[w] dilate i) w :=
  OnePoint.IsBoundedAt.smul_iff.mp
    (hf (CuspForm.isCusp_smul_of_rat hc _ (dilate_rat i)))

private noncomputable def etaAt (i : Fin 8) : ℍ → ℂ :=
  fun z => etaSquare (dilate i • z)

private lemma etaAt_holo (i : Fin 8) : MDiff (etaAt i) := by
  rw [show etaAt i = etaSquare ∣[(1 : ℤ)] dilate i by
    ext z; simp [dilate, slash_heckeDiagMatrix_apply _ (level_pos i).ne', etaAt]]
  apply MDifferentiable.slash
  rw [UpperHalfPlane.mdifferentiable_iff]
  have h : DifferentiableOn ℂ (fun z => η z ^ 2) upperHalfPlaneSet :=
    fun z hz => ((differentiableAt_eta_of_mem_upperHalfPlaneSet hz).pow 2).differentiableWithinAt
  exact h.congr (fun z hz => by simp [etaSquare, ofComplex_apply_of_im_pos hz])

private lemma etaAt_bdd (i : Fin 8) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    OnePoint.IsBoundedAt c (etaAt i) 1 := by
  have hΔ := bounded_dilate i 12 (f := ModularForm.discriminant)
    (fun {d} hd => ModularFormClass.bdd_at_cusps CuspForm.discriminant hd) hc
  rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
  intro γ hγ
  have hb := (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mp hΔ γ hγ
  have he : (etaAt i) ^ 12 = ((level i : ℂ) ^ 11)⁻¹ •
      (ModularForm.discriminant ∣[(12 : ℤ)] dilate i) := by
    ext z
    simp only [etaAt, etaSquare, Pi.pow_apply, Pi.smul_apply,
      smul_eq_mul, ← pow_mul, dilate]
    rw [slash_heckeDiagMatrix_apply _ (level_pos i).ne']
    have hd : (level i : ℂ) ≠ 0 := by exact_mod_cast (level_pos i).ne'
    norm_num
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hd), one_mul]
    rfl
  have hb' : IsBoundedAtImInfty ((etaAt i ∣[(1 : ℤ)] γ) ^ 12) := by
    rw [← ModularForm.pow_slash_SL2, he, ModularForm.SL_smul_slash]
    exact Filter.BoundedAtFilter.smul _ hb
  obtain ⟨M, A, hMA⟩ := isBoundedAtImInfty_iff.mp hb'
  refine isBoundedAtImInfty_iff.mpr ⟨max 1 M, A, fun z hz => ?_⟩
  have h := hMA z hz
  rw [Pi.pow_apply, norm_pow] at h
  by_cases hn : ‖(etaAt i ∣[(1 : ℤ)] γ) z‖ ≤ 1
  · exact hn.trans (le_max_left ..)
  · calc
      _ ≤ ‖(etaAt i ∣[(1 : ℤ)] γ) z‖ ^ 12 := by
        simpa only [pow_one] using pow_le_pow_right₀ (le_of_not_ge hn)
          (show 1 ≤ (12 : ℕ) by decide)
      _ ≤ _ := h.trans (le_max_right ..)

private lemma etaProduct_bdd (r : Fin 8 → ℕ) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    OnePoint.IsBoundedAt c (etaProduct r) ((∑ i, r i : ℕ) : ℤ) := by
  rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
  intro γ hγ
  have he : etaProduct r ∣[((∑ i, r i : ℕ) : ℤ)] γ =
      ∏ i, (etaAt i ∣[(1 : ℤ)] γ) ^ r i := by
    ext z
    simp only [SL_slash_apply, etaProduct, Finset.prod_apply, Pi.pow_apply, etaAt,
      mul_pow, Finset.prod_mul_distrib, zpow_neg, zpow_one, zpow_natCast,
      inv_pow, Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum]
  rw [he]
  refine Filter.BoundedAtFilter.prod _ fun i _ => ?_
  exact (UpperHalfPlane.boundedAtImInftySubalgebra ℂ).pow_mem
    ((OnePoint.isBoundedAt_iff_forall_SL2Z hc).mp (etaAt_bdd i hc) γ hγ) _

private noncomputable def etaForm (r : Fin 8 → ℕ) (w : ℤ) (hw : ((∑ i, r i : ℕ) : ℤ) = w)
    (hT : 12 ∣ ∑ i, level i * r i) (hS : 4 ∣ ∑ i, colevel i * r i)
    (hW : 2 ∣ ∑ i, r i) : ModularForm (CongruenceSubgroup.Gamma0 40) w where
  toFun := etaProduct r
  slash_action_eq' g hg := by
    obtain ⟨γ, hγ, rfl⟩ := hg
    rw [← hw]
    exact etaProduct_slash r hT hS hW hγ
  holo' := by
    change MDiff (etaProduct r)
    rw [show etaProduct r = ∏ i, etaAt i ^ r i by ext z; simp [etaProduct, etaAt]]
    exact MDifferentiable.prod fun i _ => (etaAt_holo i).pow _
  bdd_at_cusps' hc := hw ▸ etaProduct_bdd r (hc.mono (by
    rintro _ ⟨γ, _, rfl⟩
    exact ⟨γ, rfl⟩))

private def eisensteinWeights : Fin 8 → ℤ := ![1, -1, 2, 5, -8, -5, 10, -40]

private noncomputable def eCoeff (i : Fin 8) : ℂ := eisensteinWeights i

private noncomputable def eWeight (i : Fin 8) : ℂ := eCoeff i / (level i : ℂ)

private noncomputable def eAt (i : Fin 8) : ℍ → ℂ := E2 ∣[(2 : ℤ)] dilate i

private lemma eAt_apply (i : Fin 8) (z : ℍ) :
    eAt i z = (level i : ℂ) * E2 (dilate i • z) := by
  simp [eAt, dilate, slash_heckeDiagMatrix_apply _ (level_pos i).ne']

private lemma eAt_slash (i : Fin 8) (γ : SL(2, ℤ)) (k : ℤ) (hc : γ 1 0 = 40 * k) :
    eAt i ∣[(2 : ℤ)] γ = eAt i - (1 / (2 * riemannZeta 2)) • D2 γ := by
  ext z
  rw [SL_slash_apply, eAt_apply, ← rescale_smul i γ k hc, ← rescale_denom i γ k hc z,
    mul_assoc, ← SL_slash_apply, E2_slash_action]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, eAt_apply]
  rw [mul_sub]
  congr 1
  rw [D2, D2, rescale_denom]
  change _ * (_ * ((2 * π * I * ↑((colevel i : ℤ) * k)) / denom γ z)) =
    _ * ((2 * π * I * (γ 1 0 : ℂ)) / denom γ z)
  have hm : (level i : ℂ) * (colevel i : ℂ) = 40 := by
    exact_mod_cast (Nat.mul_div_cancel' (level_dvd i) : level i * colevel i = 40)
  rw [hc]
  push_cast
  linear_combination (((1 / (2 * riemannZeta 2)) * 2 * π * I * (k : ℂ)) / denom γ z) * hm

private lemma D2_bdd (γ : SL(2, ℤ)) : IsBoundedAtImInfty (D2 γ) := by
  by_cases hγ : γ 1 0 = 0
  · rw [show D2 γ = 0 by ext z; simp [D2, hγ]]
    exact zero_form_isBoundedAtImInfty
  refine isBoundedAtImInfty_iff.mpr ⟨2 * π, 1, fun z hz => ?_⟩
  rw [D2, norm_div, norm_mul, norm_mul, norm_mul, norm_I, mul_one, norm_ofNat,
    norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    div_le_iff₀ (norm_pos_iff.mpr (denom_ne_zero γ z))]
  have hden : ‖(γ 1 0 : ℂ)‖ ≤ ‖denom γ z‖ := by
    calc
      _ = |(γ 1 0 : ℝ)| := by rw [← ofReal_intCast, norm_real, Real.norm_eq_abs]
      _ ≤ |(γ 1 0 : ℝ)| * z.im := le_mul_of_one_le_right (abs_nonneg _) hz
      _ = |(denom γ z).im| := by
        simp [ModularGroup.denom_apply, ← ofReal_intCast, mul_im, abs_mul,
          abs_of_pos z.im_pos]
      _ ≤ _ := abs_im_le_norm _
  gcongr

private lemma E2_bdd_cusp {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    OnePoint.IsBoundedAt c E2 2 := by
  rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
  intro γ _
  rw [E2_slash_action]
  exact Asymptotics.IsBigO.sub isBoundedAtImInfty_E2
    (Filter.BoundedAtFilter.smul _ (D2_bdd γ))

private noncomputable def eForm : ModularForm (CongruenceSubgroup.Gamma0 40) 2 where
  toFun := ∑ i, eWeight i • eAt i
  slash_action_eq' g hg := by
    obtain ⟨γ, hγ, rfl⟩ := hg
    have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      (CongruenceSubgroup.Gamma0_mem.mp hγ)
    obtain ⟨k, hk⟩ := hc
    change (∑ i, eWeight i • eAt i) ∣[(2 : ℤ)] γ = _
    rw [SlashAction.sum_slash]
    simp only [SL_smul_slash, eAt_slash _ γ k hk, smul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_smul]
    have hz : ∑ i, eWeight i = 0 := by
      simp [eWeight, eCoeff, eisensteinWeights, level, Fin.sum_univ_succ]
      norm_num
    rw [hz, zero_smul, sub_zero]
  holo' := by
    change MDiff (∑ i, eWeight i • eAt i)
    exact MDifferentiable.sum fun i _ =>
      (E2_mdifferentiable.slash 2 (dilate i)).const_smul _
  bdd_at_cusps' hc g hg := by
    have hSL : IsCusp _ 𝒮ℒ := hc.mono (by
      rintro _ ⟨γ, _, rfl⟩
      exact ⟨γ, rfl⟩)
    rw [SlashAction.sum_slash]
    refine (boundedFilterSubmodule ℂ atImInfty).sum_mem fun i _ => ?_
    rw [ModularForm.smul_slash]
    exact Filter.BoundedAtFilter.smul _ (bounded_dilate i 2 E2_bdd_cusp hSL g hg)

-- Exponents of η(dz)², in the order of `level`. The final vector gives
-- the exponents of the square of the last cleared term.
private def denominatorPowers : Fin 8 → ℕ := ![2, 1, 2, 0, 2, 2, 1, 4]
private def thetaPowers : Fin 8 → ℕ := ![0, 6, 0, 0, 2, 0, 6, 2]
private def firstPowers : Fin 8 → ℕ := ![2, 2, 2, 0, 2, 3, 1, 4]
private def secondPowers : Fin 8 → ℕ := ![2, 1, 3, 0, 2, 2, 2, 4]
private def lastPowers : Fin 8 → ℕ := ![4, 1, 9, 0, 2, 5, 1, 10]

private noncomputable def combinedForm :
    ModularForm (CongruenceSubgroup.Gamma0 40) 16 :=
  let D := etaForm denominatorPowers 14 (by decide) (by decide) (by decide) (by decide)
  let A := etaForm thetaPowers 16 (by decide) (by decide) (by decide) (by decide)
  let B := etaForm firstPowers 16 (by decide) (by decide) (by decide) (by decide)
  let C := etaForm secondPowers 16 (by decide) (by decide) (by decide) (by decide)
  (36 : ℂ) • A + (D.mul eForm).mcast (by norm_num) rfl - (120 : ℂ) • B - (96 : ℂ) • C

private noncomputable def differenceForm :
    ModularForm (CongruenceSubgroup.Gamma0 40) 32 :=
  (combinedForm.mul combinedForm).mcast (by norm_num) rfl -
    ((144 : ℂ) ^ 2) • etaForm lastPowers 32 (by decide) (by decide) (by decide) (by decide)

-- Bound the index of Γ₀(40) using its cosets' first columns modulo 40.
private def reduction (γ : SL(2, ℤ)) : SL(2, ZMod 40) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 40)) γ

private lemma reduction_apply (γ : SL(2, ℤ)) (i j : Fin 2) :
    reduction γ i j = (γ i j : ZMod 40) := rfl

private lemma det_entries {R : Type*} [CommRing R] (A : SL(2, R)) :
    A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
  rw [← Matrix.det_fin_two]
  exact A.2

private def firstColumn (A : SL(2, ZMod 40)) : ProjectiveLine (ZMod 40) :=
  ⟦⟨(A 0 0, A 1 0), ⟨A 1 1, -A 0 1, by linear_combination det_entries A⟩⟩⟧

private lemma inv_mul_lower_entry {R : Type*} [CommRing R] (A B : SL(2, R)) :
    (A⁻¹ * B : SL(2, R)) 1 0 = A 0 0 * B 1 0 - A 1 0 * B 0 0 := by
  simp [SL2_inv_expl, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private lemma firstColumn_eq (A B : SL(2, ZMod 40)) :
    firstColumn A = firstColumn B ↔ (A⁻¹ * B : SL(2, ZMod 40)) 1 0 = 0 := by
  constructor
  · intro h
    obtain ⟨u, ha, hc⟩ := Quotient.exact h
    change (u : ZMod 40) * A 0 0 = B 0 0 at ha
    change (u : ZMod 40) * A 1 0 = B 1 0 at hc
    rw [inv_mul_lower_entry, ← ha, ← hc]
    ring
  · intro h
    let C := A⁻¹ * B
    change C 1 0 = 0 at h
    have hd := det_entries C
    rw [h, mul_zero, sub_zero] at hd
    have hAB : A * C = B := mul_inv_cancel_left A B
    have hC (i : Fin 2) : B i 0 = A i 0 * C 0 0 := by
      rw [← hAB]
      simp [Matrix.mul_apply, Fin.sum_univ_two, h]
    apply Quotient.sound
    refine ⟨⟨C 0 0, C 1 1, hd, (mul_comm (C 1 1) (C 0 0)).trans hd⟩, ?_, ?_⟩
    · change C 0 0 * A 0 0 = B 0 0
      rw [hC, mul_comm]
    · change C 0 0 * A 1 0 = B 1 0
      rw [hC, mul_comm]

private lemma index_bound : (CongruenceSubgroup.Gamma0 40).index ≤ 72 := by
  let K := CongruenceSubgroup.Gamma0 40
  have hrel (A B : SL(2, ℤ)) :
      firstColumn (reduction A) = firstColumn (reduction B) ↔ A⁻¹ * B ∈ K := by
    rw [firstColumn_eq, reduction, reduction, ← map_inv, ← map_mul]
    change reduction (A⁻¹ * B) 1 0 = 0 ↔ _
    rw [reduction_apply]
    exact CongruenceSubgroup.Gamma0_mem.symm
  let f : SL(2, ℤ) ⧸ K → ProjectiveLine (ZMod 40) :=
    Quotient.lift (fun A : SL(2, ℤ) => firstColumn (reduction A)) fun A B h =>
      (hrel A B).mpr (QuotientGroup.leftRel_apply.mp h)
  have hf : Function.Injective f := by
    intro a b
    induction a, b using Quotient.inductionOn₂ with
    | _ A B =>
      intro h
      exact Quotient.sound (QuotientGroup.leftRel_apply.mpr ((hrel A B).mp h))
  have hh := Nat.card_le_card_of_injective f hf
  rw [card_projectiveLine_zmod 40 (by decide)] at hh
  have hpsi : ArithmeticFunction.dedekindPsi 40 = 72 := by
    rw [show 40 = 2 ^ 3 * 5 by decide,
      ArithmeticFunction.isMultiplicative_dedekindPsi.map_mul_of_coprime (by decide),
      ArithmeticFunction.dedekindPsi_prime_pow (by decide) (by decide),
      show ArithmeticFunction.dedekindPsi 5 = 6 by
        simpa using ArithmeticFunction.dedekindPsi_prime_pow (p := 5) (k := 1)
          (by decide) (by decide)]
    norm_num
  rwa [hpsi] at hh

open scoped ArithmeticFunction.sigma

local notation "𝐗" => (PowerSeries.X : PowerSeries ℂ)
local notation "𝐂" => (PowerSeries.C : ℂ →+* PowerSeries ℂ)

private lemma euler_eq_raw (q : ℂ) (hq : ‖q‖ < 1) :
    eulerFunction q = 𝔣 q := by
  rw [eulerFunction_eq_tprod hq, QPochhammer.qPochhammerInfRaw]
  simp only [pow_succ']

private lemma euler_ne_zero (q : ℂ) (hq : ‖q‖ < 1) : eulerFunction q ≠ 0 := by
  rw [eulerFunction_eq_tprod hq]
  simp_rw [sub_eq_add_neg]
  refine tprod_one_add_ne_zero_of_summable (f := fun n : ℕ => -(q ^ (n + 1))) ?_ ?_
  · intro n
    rw [← sub_eq_add_neg, sub_ne_zero]
    have hn : ‖q ^ (n + 1)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hq (Nat.succ_ne_zero _)
    intro h
    simp [← h] at hn
  · have hs : Summable (fun n : ℕ => q ^ n) := summable_geometric_of_norm_lt_one hq
    exact ((summable_nat_add_iff (f := fun n : ℕ => q ^ n) 1).mpr hs).neg.norm

private lemma qparam_dilate (i : Fin 8) (z : ℍ) :
    𝕢 ((dilate i • z : ℍ) : ℂ) = 𝕢 (z : ℂ) ^ level i := by
  rw [dilate_apply]
  simp only [Function.Periodic.qParam, ofReal_one, div_one, ← exp_nat_mul]
  congr 1
  ring

private lemma norm_qparam (z : ℍ) : ‖𝕢 (z : ℂ)‖ < 1 :=
  Function.Periodic.norm_qParam_lt_one one_pos z.2

private lemma lambert_eq_e2 (z : ℍ) : 𝐏 (𝕢 (z : ℂ)) = E2 z := by
  rw [E2_eq_tsum_cexp]
  have h := tsum_pow_div_one_sub_eq_tsum_sigma (norm_qparam z) 1
  rw [tsum_pnat_eq_tsum_succ (f := fun m : ℕ =>
    (m : ℂ) ^ 1 * 𝕢 (z : ℂ) ^ m / (1 - 𝕢 (z : ℂ) ^ m))] at h
  have he : (∑' m : ℕ+, σ 1 m * cexp (2 * π * I * z) ^ (m : ℕ)) =
      ∑' m : ℕ+, ((σ 1 m : ℕ) : ℂ) * 𝕢 (z : ℂ) ^ (m : ℕ) := by
    simp [Function.Periodic.qParam]
  rw [he, ← h]
  simp only [pow_one]

private def HasQSeries (P : PowerSeries ℂ) (F : ℍ → ℂ) : Prop :=
  ∀ z : ℍ, HasSum (fun n : ℕ => P.coeff n * 𝕢 (z : ℂ) ^ n) (F z)

private lemma HasQSeries.mul {P Q : PowerSeries ℂ} {F G : ℍ → ℂ}
    (hP : HasQSeries P F) (hQ : HasQSeries Q G) :
    HasQSeries (P * Q) (F * G) :=
  ModularCurve.hasSum_qParam_mul 1 one_pos P Q F G hP hQ

private lemma HasQSeries.add {P Q : PowerSeries ℂ} {F G : ℍ → ℂ}
    (hP : HasQSeries P F) (hQ : HasQSeries Q G) :
    HasQSeries (P + Q) (F + G) := fun z => by simpa [add_mul] using (hP z).add (hQ z)

private lemma HasQSeries.sub {P Q : PowerSeries ℂ} {F G : ℍ → ℂ}
    (hP : HasQSeries P F) (hQ : HasQSeries Q G) :
    HasQSeries (P - Q) (F - G) := fun z => by simpa [sub_mul] using (hP z).sub (hQ z)

private lemma HasQSeries.monomial (m : ℕ) (c : ℂ) :
    HasQSeries (𝐂 c * 𝐗 ^ m) (fun z => c * 𝕢 (z : ℂ) ^ m) := fun z => by
  refine (hasSum_ite_eq m (c * 𝕢 (z : ℂ) ^ m)).congr_fun fun n => ?_
  by_cases h : n = m <;> simp [PowerSeries.coeff_X_pow, h]

private lemma HasQSeries.one : HasQSeries 1 (1 : ℍ → ℂ) := by
  change HasQSeries 1 (fun _ => (1 : ℂ))
  simpa only [pow_zero, map_one, mul_one] using HasQSeries.monomial 0 1

private lemma HasQSeries.smul (c : ℂ) {P : PowerSeries ℂ} {F : ℍ → ℂ}
    (hP : HasQSeries P F) : HasQSeries (𝐂 c * P) (c • F) := by
  have h := (HasQSeries.monomial 0 c).mul hP
  rw [show (fun z : ℍ => c * 𝕢 (z : ℂ) ^ 0) * F = c • F by ext z; simp] at h
  simpa only [pow_zero, mul_one] using h

private lemma HasQSeries.pow {P : PowerSeries ℂ} {F : ℍ → ℂ}
    (hP : HasQSeries P F) (n : ℕ) : HasQSeries (P ^ n) (F ^ n) := by
  induction n with
  | zero => simpa using HasQSeries.one
  | succ n ih => simpa only [pow_succ] using ih.mul hP

private lemma HasQSeries.prod {ι : Type*} (s : Finset ι)
    {P : ι → PowerSeries ℂ} {F : ι → ℍ → ℂ}
    (hP : ∀ i ∈ s, HasQSeries (P i) (F i)) :
    HasQSeries (∏ i ∈ s, P i) (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasQSeries.one
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (hP i (Finset.mem_insert_self _ _)).mul (ih
      fun j hj => hP j (Finset.mem_insert_of_mem hj))

private lemma HasQSeries.expand (i : Fin 8) {P : PowerSeries ℂ} {F : ℍ → ℂ}
    (hP : HasQSeries P F) :
    HasQSeries (P.expand (level i) (level_pos i).ne') (F ∘ (dilate i • ·)) := by
  intro z
  have hinj : Function.Injective (fun n : ℕ => level i * n) :=
    fun _ _ h => Nat.eq_of_mul_eq_mul_left (level_pos i) h
  refine (hinj.hasSum_iff fun n hn => ?_).mp ?_
  · rw [PowerSeries.coeff_expand_of_not_dvd _ _ _ (by
      rintro ⟨m, rfl⟩
      exact hn ⟨m, rfl⟩), zero_mul]
  · simpa only [Function.comp_def, PowerSeries.coeff_expand_mul, pow_mul, qparam_dilate]
      using hP (dilate i • z)

private noncomputable def eulerSeries (i : Fin 8) : PowerSeries ℂ :=
  (PowerSeries.pentagonalSeries ℂ).expand (level i) (level_pos i).ne'

private lemma eulerSeries_spec (i : Fin 8) :
    HasQSeries (eulerSeries i) (fun z => eulerFunction (𝕢 (z : ℂ) ^ level i)) := by
  have h : HasQSeries (PowerSeries.pentagonalSeries ℂ) (eulerFunction ∘ (𝕢 ∘ ((↑) : ℍ → ℂ))) :=
    fun z => hasSum_eulerFunction_pentagonalSeries (norm_qparam z)
  simpa only [eulerSeries, Function.comp_def, qparam_dilate] using h.expand i

private noncomputable def eisensteinBase : PowerSeries ℂ :=
  PowerSeries.mk fun n => if n = 0 then 1 else -24 * σ 1 n

private noncomputable def eisensteinSeries40 : PowerSeries ℂ :=
  ∑ i, 𝐂 (eCoeff i) * eisensteinBase.expand (level i) (level_pos i).ne'

private lemma eisensteinSeries40_spec : HasQSeries eisensteinSeries40 eForm := by
  intro z
  have h : HasQSeries eisensteinBase E2 := fun w => by
    simpa [eisensteinBase, smul_eq_mul, Function.Periodic.qParam] using hasSum_qExpansion_E2 w
  have hsum := hasSum_sum (s := Finset.univ) (fun i (_ : i ∈ (Finset.univ : Finset (Fin 8))) =>
    ((h.expand i).smul (eCoeff i)) z)
  convert hsum using 1
  · ext n
    simp [eisensteinSeries40, Finset.sum_mul, map_sum]
  · change (∑ i, (eWeight i • eAt i) z) = ∑ i, eCoeff i * E2 (dilate i • z)
    simp only [Pi.smul_apply, smul_eq_mul, eWeight, eAt_apply]
    apply Finset.sum_congr rfl
    intro i _
    have hd : (level i : ℂ) ≠ 0 := by exact_mod_cast (level_pos i).ne'
    field_simp

private noncomputable def etaSeries (s : Fin 8 → ℕ) : PowerSeries ℂ :=
  𝐗 ^ ((∑ i, level i * s i) / 24) * ∏ i, eulerSeries i ^ s i

private noncomputable def etaPowers (s : Fin 8 → ℕ) (z : ℍ) : ℂ :=
  ∏ i, η (dilate i • z : ℍ) ^ s i

private lemma etaPowers_even (r : Fin 8 → ℕ) :
    etaPowers (fun i => 2 * r i) = etaProduct r := by
  ext z
  simp only [etaPowers, etaProduct, etaSquare, pow_mul]

private lemma etaPowers_sq (s : Fin 8 → ℕ) :
    etaPowers s * etaPowers s = etaProduct s := by
  ext z
  simp only [Pi.mul_apply, etaPowers, etaProduct, etaSquare, ← pow_two, ← Finset.prod_pow,
    ← pow_mul, Nat.mul_comm]

private lemma etaPowers_eq (s : Fin 8 → ℕ) (hs : 24 ∣ ∑ i, level i * s i) (z : ℍ) :
    etaPowers s z = 𝕢 (z : ℂ) ^ ((∑ i, level i * s i) / 24) *
      ∏ i, eulerFunction (𝕢 (z : ℂ) ^ level i) ^ s i := by
  have h (i : Fin 8) : ‖𝕢 (z : ℂ) ^ level i‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (norm_qparam z) (level_pos i).ne'
  have he (i : Fin 8) : η (dilate i • z : ℍ) =
      Function.Periodic.qParam 24 (dilate i • z : ℍ) *
        eulerFunction (𝕢 (z : ℂ) ^ level i) := by
    rw [ModularForm.eta, eulerFunction_eq_tprod (h i)]
    simp only [eta_q, qparam_dilate]
  simp only [etaPowers, he, mul_pow, Finset.prod_mul_distrib]
  congr 1
  simp only [Function.Periodic.qParam, ofReal_ofNat, ofReal_one, div_one, dilate_apply,
    ← exp_nat_mul, ← exp_sum]
  congr 1
  have ht : ((↑((∑ i, level i * s i) / 24) : ℂ)) * 24 = ∑ i, (level i : ℂ) * s i := by
    exact_mod_cast Nat.div_mul_cancel hs
  calc
    _ = (2 * π * I * z / 24) * ∑ i, (level i : ℂ) * s i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [← ht]; ring

private lemma etaSeries_spec (s : Fin 8 → ℕ) (hs : 24 ∣ ∑ i, level i * s i) :
    HasQSeries (etaSeries s) (etaPowers s) := by
  have hh := (HasQSeries.monomial ((∑ i, level i * s i) / 24) 1).mul
    (HasQSeries.prod Finset.univ (fun i _ => (eulerSeries_spec i).pow (s i)))
  convert hh using 1
  · simp [etaSeries]
  · ext z
    simp only [etaPowers_eq s hs, Pi.mul_apply, one_mul, Finset.prod_apply, Pi.pow_apply]

-- The common factor q^19 means degrees below 174 suffice for degrees 0 through 192.
private def cutoff : ℕ := 174

private def eisensteinCoefficient (n : ℕ) : ℤ :=
  if n = 0 then 1 else -24 * (σ 1 n : ℕ)

private lemma eisensteinBase_coeff (n : ℕ) :
    eisensteinBase.coeff n = eisensteinCoefficient n := by
  by_cases h : n = 0 <;> simp [eisensteinBase, eisensteinCoefficient, h]

section CoefficientComputation

variable {R : Type*} [CommRing R]

private def cutMonomial (x : R) (n : ℕ) : R := if n < cutoff then x ^ n else 0

private def eulerApprox (x : R) (d : ℕ) : R :=
  ∑ j ∈ Finset.range 23, let k : ℤ := (j : ℤ) - 11
    (-1 : R) ^ k.natAbs * cutMonomial x (d * pentagonal k)

private def eisensteinApprox (x : R) : R :=
  ∑ i, (eisensteinWeights i : R) * ∑ n ∈ Finset.range (cutoff / level i + 1),
    (eisensteinCoefficient n : R) * cutMonomial x (level i * n)

private def productFactors (F : Fin 8 → R) (p : Fin 8 → ℕ) : R := ∏ i, F i ^ p i

private def combined (x : R) (F : Fin 8 → R) (E : R) : R :=
  36 * productFactors F (fun i => 2 * thetaPowers i) +
    productFactors F (fun i => 2 * denominatorPowers i) * E -
    120 * x * productFactors F (fun i => 2 * firstPowers i) -
    96 * x ^ 2 * productFactors F (fun i => 2 * secondPowers i)

private def lastTerm (x : R) (F : Fin 8 → R) : R :=
  144 * x ^ 3 * productFactors F lastPowers

private def differenceApprox (x : R) : R :=
  combined x (fun i => eulerApprox x (level i)) (eisensteinApprox x) -
    lastTerm x (fun i => eulerApprox x (level i))

private lemma map_differenceApprox {S : Type*} [CommRing S] (f : R →+* S) (x : R) :
    f (differenceApprox x) = differenceApprox (f x) := by
  simp only [differenceApprox, combined, lastTerm, productFactors, eulerApprox, eisensteinApprox,
    cutMonomial, map_add, map_mul, map_pow, map_sub, map_sum, map_prod, map_ofNat, map_intCast,
    map_neg, map_one, apply_ite f, map_zero]

end CoefficientComputation

-- Evaluate the truncated polynomials at a large integer radix. The
-- coefficient bound below allows the modular equality to be decoded
-- into individual coefficient equalities, even for signed coefficients.
private def radix : ℤ := 2 ^ 512

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Kernel evaluation of the integer polynomial requires an increased limit.
private lemma packed_coefficients : differenceApprox radix % radix ^ cutoff = 0 := by
  decide +kernel

private lemma coeff_cutMonomial {n : ℕ} (hn : n < cutoff) (m : ℕ) :
    (cutMonomial 𝐗 m).coeff n = if n = m then 1 else 0 := by
  by_cases hm : m < cutoff
  · simp [cutMonomial, hm, PowerSeries.coeff_X_pow]
  · have hne : n ≠ m := by omega
    simp [cutMonomial, hm, hne]

private lemma pentagonal_small {k : ℤ} (h : pentagonal k < cutoff) :
    -11 ≤ k ∧ k ≤ 11 := by
  constructor
  · by_contra! hk
    have hmono := pentagonal_strictAntiOn.antitoneOn
      (show k ∈ Set.Iic 0 from by simpa using (show k ≤ 0 by omega))
      (show (-12 : ℤ) ∈ Set.Iic 0 from by decide) (show k ≤ -12 by omega)
    exact (not_le_of_gt h) ((by decide : cutoff ≤ pentagonal (-12)).trans hmono)
  · by_contra! hk
    have hmono := pentagonal_strictMonoOn.monotoneOn
      (show (12 : ℤ) ∈ Set.Ici 0 from by decide)
      (show k ∈ Set.Ici 0 from by simpa using (show 0 ≤ k by omega)) (show 12 ≤ k by omega)
    exact (not_le_of_gt h) ((by decide : cutoff ≤ pentagonal 12).trans hmono)

private lemma eulerApprox_coeff (i : Fin 8) {n : ℕ} (hn : n < cutoff) :
    (eulerApprox 𝐗 (level i)).coeff n = (eulerSeries i).coeff n := by
  have hc (k : ℤ) : (PowerSeries.coeff n)
      ((-1 : PowerSeries ℂ) ^ k.natAbs * cutMonomial 𝐗 (level i * pentagonal k)) =
      if n = level i * pentagonal k then (-1 : ℂ) ^ k.natAbs else 0 := by
    rw [show (-1 : PowerSeries ℂ) ^ k.natAbs = 𝐂 ((-1 : ℂ) ^ k.natAbs) by simp]
    rw [PowerSeries.coeff_C_mul, coeff_cutMonomial hn]
    split_ifs <;> simp
  simp only [eulerApprox, map_sum, hc]
  by_cases h : ∃ k : ℤ, n = level i * pentagonal k
  · obtain ⟨k, rfl⟩ := h
    have hk := pentagonal_small ((Nat.le_mul_of_pos_left _ (level_pos i)).trans_lt hn)
    let j : ℕ := (k + 11).toNat
    have hj : (j : ℤ) - 11 = k := by omega
    have hj' : j ∈ Finset.range 23 := Finset.mem_range.mpr (by omega)
    rw [Finset.sum_eq_single_of_mem j hj']
    · rw [hj, ite_eq_left rfl, eulerSeries, PowerSeries.coeff_expand_mul,
        PowerSeries.coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow]
    · intro l hl hlj
      have hne : level i * pentagonal k ≠ level i * pentagonal ((l : ℤ) - 11) := by
        intro he
        have he' := pentagonal_injective (Nat.eq_of_mul_eq_mul_left (level_pos i) he)
        omega
      rw [ite_eq_right hne]
  · rw [Finset.sum_eq_zero]
    · symm
      rw [eulerSeries, PowerSeries.coeff_expand]
      split_ifs with hd
      · apply PowerSeries.coeff_pentagonalSeries_eq_zero
        rintro ⟨k, hk⟩
        exact h ⟨k, by rw [hk, Nat.mul_div_cancel' hd]⟩
      · rfl
    · intro j _
      exact ite_eq_right fun hj => h ⟨_, hj⟩

private lemma constant_mul_coeff (c : ℤ) (p : PowerSeries ℂ) (n : ℕ) :
    ((c : PowerSeries ℂ) * p).coeff n = (c : ℂ) * p.coeff n := by
  rw [show (c : PowerSeries ℂ) = 𝐂 (c : ℂ) by simp, PowerSeries.coeff_C_mul]

private lemma eisensteinApprox_coeff {n : ℕ} (hn : n < cutoff) :
    (eisensteinApprox 𝐗).coeff n = eisensteinSeries40.coeff n := by
  simp only [eisensteinApprox, eisensteinSeries40, map_sum, constant_mul_coeff,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_expand, eisensteinBase_coeff, eCoeff]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [coeff_cutMonomial hn, mul_ite, mul_one, mul_zero]
  by_cases hd : level i ∣ n
  · rw [ite_eq_left hd, Finset.sum_eq_single_of_mem (n / level i) (Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Nat.div_le_div_right hn.le)))]
    · simp [Nat.mul_div_cancel' hd]
    · intro j _ hj
      have he : n ≠ level i * j := by
        intro h
        apply hj
        rw [h, Nat.mul_div_cancel_left _ (level_pos i)]
      rw [ite_eq_right he]
  · rw [ite_eq_right hd]
    exact Finset.sum_eq_zero fun j _ => ite_eq_right fun hj => hd ⟨j, hj⟩

private def CoeffBound (p : Polynomial ℤ) (b : ℤ) : Prop :=
  ∀ n < cutoff, |p.coeff n| ≤ b

private lemma CoeffBound.nonneg {p : Polynomial ℤ} {b : ℤ} (h : CoeffBound p b) : 0 ≤ b :=
  (abs_nonneg _).trans (h 0 (by decide))

private lemma CoeffBound.weaken {p : Polynomial ℤ} {a b : ℤ}
    (h : CoeffBound p a) (hab : a ≤ b) : CoeffBound p b :=
  fun n hn => (h n hn).trans hab

private lemma CoeffBound.add {p q : Polynomial ℤ} {a b : ℤ}
    (hp : CoeffBound p a) (hq : CoeffBound q b) : CoeffBound (p + q) (a + b) := by
  intro n hn
  rw [Polynomial.coeff_add]
  exact (abs_add_le ..).trans (add_le_add (hp n hn) (hq n hn))

private lemma CoeffBound.sub {p q : Polynomial ℤ} {a b : ℤ}
    (hp : CoeffBound p a) (hq : CoeffBound q b) : CoeffBound (p - q) (a + b) := by
  intro n hn
  rw [Polynomial.coeff_sub, sub_eq_add_neg]
  exact (abs_add_le ..).trans (by simpa only [abs_neg] using add_le_add (hp n hn) (hq n hn))

private lemma CoeffBound.scale (c : ℤ) {p : Polynomial ℤ} {b : ℤ} (h : CoeffBound p b) :
    CoeffBound ((c : Polynomial ℤ) * p) (|c| * b) := by
  intro n hn
  rw [Polynomial.coeff_intCast_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (h n hn) (abs_nonneg _)

private lemma CoeffBound.mul {p q : Polynomial ℤ} {a b : ℤ}
    (hp : CoeffBound p a) (hq : CoeffBound q b) :
    CoeffBound (p * q) ((cutoff : ℤ) * (a * b)) := by
  intro n hn
  rw [Polynomial.coeff_mul]
  refine (Finset.abs_sum_le_sum_abs ..).trans ?_
  calc
    _ ≤ ∑ _ ∈ Finset.antidiagonal n, a * b := by
      refine Finset.sum_le_sum fun ij hij => ?_
      have hsum := Finset.mem_antidiagonal.mp hij
      rw [abs_mul]
      exact mul_le_mul (hp _ (by omega)) (hq _ (by omega)) (abs_nonneg _) hp.nonneg
    _ = ((n + 1 : ℕ) : ℤ) * (a * b) := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hp.nonneg hq.nonneg)
      exact_mod_cast Nat.succ_le_of_lt hn

private lemma CoeffBound.sum {ι : Type*} (s : Finset ι) (p : ι → Polynomial ℤ) (b : ℤ)
    (h : ∀ i ∈ s, CoeffBound (p i) b) : CoeffBound (∑ i ∈ s, p i) (s.card * b) := by
  intro n hn
  rw [Polynomial.finsetSum_coeff]
  refine (Finset.abs_sum_le_sum_abs ..).trans ?_
  simpa [nsmul_eq_mul] using Finset.sum_le_sum (fun i hi => h i hi n hn)

private lemma CoeffBound.X_pow (d : ℕ) : CoeffBound ((Polynomial.X : Polynomial ℤ) ^ d) 1 := by
  intro n _
  by_cases h : n = d <;> simp [Polynomial.coeff_X_pow, h]

private lemma CoeffBound.one : CoeffBound (1 : Polynomial ℤ) 1 := by
  simpa only [pow_zero] using CoeffBound.X_pow 0

private lemma CoeffBound.pow {p : Polynomial ℤ} {b : ℤ} (hp : CoeffBound p b) (k : ℕ) :
    CoeffBound (p ^ k) (((cutoff : ℤ) * b) ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using CoeffBound.one
  | succ k ih => simpa only [pow_succ, mul_left_comm] using ih.mul hp

private lemma CoeffBound.prod {ι : Type*} (s : Finset ι) (p : ι → Polynomial ℤ) (b : ι → ℤ)
    (h : ∀ i ∈ s, CoeffBound (p i) (b i)) :
    CoeffBound (∏ i ∈ s, p i) ((cutoff : ℤ) ^ s.card * ∏ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using CoeffBound.one
  | insert i s hi ih =>
    have h1 := h i (Finset.mem_insert_self ..)
    have h2 := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    simpa only [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, pow_succ, mul_assoc,
      mul_comm, mul_left_comm] using h1.mul h2

private lemma cutMonomial_bdd (m : ℕ) :
    CoeffBound (cutMonomial (Polynomial.X : Polynomial ℤ) m) 1 := by
  by_cases hm : m < cutoff
  · simpa only [cutMonomial, ite_eq_left hm] using CoeffBound.X_pow m
  · simp [cutMonomial, hm, CoeffBound]

private lemma eulerApprox_bdd (i : Fin 8) :
    CoeffBound (eulerApprox (Polynomial.X : Polynomial ℤ) (level i)) 23 := by
  unfold eulerApprox
  have hh := CoeffBound.sum (Finset.range 23)
    (fun j => let k : ℤ := (j : ℤ) - 11
      (-1 : Polynomial ℤ) ^ k.natAbs * cutMonomial Polynomial.X (level i * pentagonal k))
    1 (fun j _ => by
      let k : ℤ := (j : ℤ) - 11
      simpa [abs_pow] using (cutMonomial_bdd (level i * pentagonal k)).scale ((-1 : ℤ) ^ k.natAbs))
  simpa using hh

private lemma eisensteinCoefficient_bdd {n : ℕ} (hn : n ≤ cutoff) :
    |eisensteinCoefficient n| ≤ 1000000 := by
  have hc : (σ 1 n : ℕ) ≤ 174 ^ 2 := (ArithmeticFunction.sigma_le_pow_succ 1 n).trans
    (Nat.pow_le_pow_left hn 2)
  have hc' : ((σ 1 n : ℕ) : ℤ) ≤ 30276 := by exact_mod_cast hc
  by_cases h : n = 0
  · norm_num [eisensteinCoefficient, h]
  · rw [eisensteinCoefficient, ite_eq_right h, abs_mul, abs_of_nonneg (Int.natCast_nonneg _)]
    norm_num
    omega

private lemma eisensteinApprox_bdd :
    CoeffBound (eisensteinApprox (Polynomial.X : Polynomial ℤ)) 100000000000 := by
  unfold eisensteinApprox
  refine (CoeffBound.sum Finset.univ _ 7000000000 (fun i _ => ?_)).weaken (by decide)
  have h1 : cutoff / level i + 1 ≤ 175 := Nat.succ_le_succ (Nat.div_le_self _ _)
  have h2 : |eisensteinWeights i| ≤ 40 := by fin_cases i <;> decide
  refine ((CoeffBound.sum (Finset.range (cutoff / level i + 1)) _ 1000000 (fun n hn => ?_)).scale
    (eisensteinWeights i)).weaken ?_
  · have hn' := Finset.mem_range.mp hn
    exact ((cutMonomial_bdd (level i * n)).scale (eisensteinCoefficient n)).weaken (by
      simpa only [mul_one] using eisensteinCoefficient_bdd (n := n) (by
        have := Nat.div_le_self cutoff (level i)
        omega))
  · simp only [Finset.card_range]
    have h1' : ((cutoff / level i + 1 : ℕ) : ℤ) ≤ 175 := by exact_mod_cast h1
    nlinarith [mul_le_mul h2 h1' (Int.natCast_nonneg _) (by decide : (0 : ℤ) ≤ 40)]

private def etaBound (r : Fin 8 → ℕ) : ℤ :=
  (cutoff : ℤ) ^ 8 * ∏ i, ((cutoff : ℤ) * 23) ^ r i

private lemma etaApprox_bdd (r : Fin 8 → ℕ) :
    CoeffBound (productFactors (fun i => eulerApprox (Polynomial.X : Polynomial ℤ) (level i)) r)
      (etaBound r) := by
  simpa only [productFactors, etaBound, Finset.card_univ, Fintype.card_fin] using
    CoeffBound.prod Finset.univ _ _ fun i _ => (eulerApprox_bdd i).pow (r i)

set_option maxRecDepth 10000 in
private lemma differenceApprox_bdd (n : ℕ) (hn : n < cutoff) :
    |(differenceApprox (Polynomial.X : Polynomial ℤ)).coeff n| < radix := by
  have hA := (etaApprox_bdd (fun i => 2 * thetaPowers i)).scale 36
  have hD := (etaApprox_bdd (fun i => 2 * denominatorPowers i)).mul eisensteinApprox_bdd
  have hB := ((CoeffBound.X_pow 1).mul (etaApprox_bdd (fun i => 2 * firstPowers i))).scale 120
  have hC := ((CoeffBound.X_pow 2).mul (etaApprox_bdd (fun i => 2 * secondPowers i))).scale 96
  have hG := ((CoeffBound.X_pow 3).mul (etaApprox_bdd lastPowers)).scale 144
  have hh := (((hA.add hD).sub hB).sub hC).sub hG
  have hval := (hh n hn).trans_lt (by decide +kernel : _ < radix)
  simpa only [differenceApprox, combined, lastTerm, mul_assoc, pow_one, Int.cast_ofNat] using hval

private lemma polynomial_coeff_eq_zero_of_eval_dvd (x : ℤ) (hx : 0 < x) (m : ℕ)
    (p : Polynomial ℤ) (hdiv : x ^ m ∣ p.eval x)
    (hb : ∀ n < m, |p.coeff n| < x) :
    ∀ n < m, p.coeff n = 0 := by
  induction m generalizing p with
  | zero => simp
  | succ m ih =>
    have he : p.eval x = x * p.divX.eval x + p.coeff 0 := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
        using congrArg (Polynomial.eval x) (Polynomial.X_mul_divX_add p).symm
    have hd : x ∣ p.coeff 0 := by
      have h := (dvd_pow_self x (Nat.succ_ne_zero m)).trans hdiv
      rw [he] at h
      exact (dvd_add_left (dvd_mul_right x (p.divX.eval x))).mp (by rwa [add_comm])
    have hc : p.coeff 0 = 0 := by
      apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd
      have h := hb 0 (Nat.zero_lt_succ _)
      exact_mod_cast (show ((p.coeff 0).natAbs : ℤ) < (x.natAbs : ℤ) from by
        simpa [Int.natCast_natAbs, abs_of_pos hx] using h)
    intro n hn
    cases n with
    | zero => exact hc
    | succ n =>
      rw [← Polynomial.coeff_divX]
      apply ih p.divX _ (fun i hi => by simpa using hb (i + 1) (Nat.succ_lt_succ hi))
        n (Nat.lt_of_succ_lt_succ hn)
      rw [he, hc, add_zero, pow_succ', mul_dvd_mul_iff_left (ne_of_gt hx)] at hdiv
      exact hdiv

private lemma differenceApprox_zero (n : ℕ) (hn : n < cutoff) :
    (differenceApprox 𝐗).coeff n = 0 := by
  let f : Polynomial ℤ →+* PowerSeries ℂ :=
    (PowerSeries.map (Int.castRingHom ℂ)).comp Polynomial.coeToPowerSeries.ringHom
  have he : (differenceApprox (Polynomial.X : Polynomial ℤ)).eval radix =
      differenceApprox radix := by
    simpa using map_differenceApprox (Polynomial.evalRingHom radix) Polynomial.X
  have hd : radix ^ cutoff ∣ (differenceApprox (Polynomial.X : Polynomial ℤ)).eval radix := by
    rw [he]
    exact @Int.dvd_of_emod_eq_zero (radix ^ cutoff) (differenceApprox radix) packed_coefficients
  have hr : 0 < radix := by
    unfold radix
    exact pow_pos (by decide) _
  have h := polynomial_coeff_eq_zero_of_eval_dvd radix hr cutoff
    (differenceApprox (Polynomial.X : Polynomial ℤ)) hd differenceApprox_bdd n hn
  have hf : f Polynomial.X = 𝐗 := by
    simp only [f, RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_X, PowerSeries.map_X]
  have hm := map_differenceApprox f Polynomial.X
  rw [hf] at hm
  rw [← hm]
  simp only [f, RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply,
    PowerSeries.coeff_map, Polynomial.coeff_coe, h, map_zero]

private noncomputable def truncIdeal : Ideal (PowerSeries ℂ) := Ideal.span {𝐗 ^ cutoff}

private lemma trunc_eq {p q : PowerSeries ℂ} :
    Ideal.Quotient.mk truncIdeal p = Ideal.Quotient.mk truncIdeal q ↔
      ∀ n < cutoff, p.coeff n = q.coeff n := by
  rw [Ideal.Quotient.eq, truncIdeal, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
  simp only [map_sub, sub_eq_zero]

private lemma normalized_difference_dvd :
    𝐗 ^ cutoff ∣ combined 𝐗 eulerSeries eisensteinSeries40 - lastTerm 𝐗 eulerSeries := by
  rw [← Ideal.mem_span_singleton]
  change combined 𝐗 eulerSeries eisensteinSeries40 - lastTerm 𝐗 eulerSeries ∈ truncIdeal
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have hA (i : Fin 8) :
      Ideal.Quotient.mk truncIdeal (eulerApprox 𝐗 (level i)) =
        Ideal.Quotient.mk truncIdeal (eulerSeries i) :=
    trunc_eq.mpr fun _ hn => eulerApprox_coeff i hn
  have hE : Ideal.Quotient.mk truncIdeal (eisensteinApprox 𝐗) =
      Ideal.Quotient.mk truncIdeal eisensteinSeries40 :=
    trunc_eq.mpr fun _ hn => eisensteinApprox_coeff hn
  have hZ : Ideal.Quotient.mk truncIdeal (differenceApprox 𝐗) = 0 := by
    rw [← map_zero (Ideal.Quotient.mk truncIdeal)]
    exact trunc_eq.mpr fun n hn => by simpa using differenceApprox_zero n hn
  simpa only [differenceApprox, combined, lastTerm, productFactors, map_add, map_sub, map_pow,
    map_mul, map_prod, hA, hE] using hZ

private noncomputable def gSeries : PowerSeries ℂ :=
  𝐗 ^ 19 * combined 𝐗 eulerSeries eisensteinSeries40

private noncomputable def hSeries : PowerSeries ℂ :=
  𝐗 ^ 19 * lastTerm 𝐗 eulerSeries

private lemma gSeries_eq :
    gSeries = 𝐂 36 * etaSeries (fun i => 2 * thetaPowers i) +
      etaSeries (fun i => 2 * denominatorPowers i) * eisensteinSeries40 -
      𝐂 120 * etaSeries (fun i => 2 * firstPowers i) -
      𝐂 96 * etaSeries (fun i => 2 * secondPowers i) := by
  unfold gSeries combined etaSeries productFactors
  rw [show (∑ i, level i * (2 * thetaPowers i)) / 24 = 19 by decide,
    show (∑ i, level i * (2 * denominatorPowers i)) / 24 = 19 by decide,
    show (∑ i, level i * (2 * firstPowers i)) / 24 = 20 by decide,
    show (∑ i, level i * (2 * secondPowers i)) / 24 = 21 by decide]
  simp only [map_ofNat, show (20 : ℕ) = 19 + 1 by decide,
    show (21 : ℕ) = 19 + 2 by decide, pow_add, pow_one]
  ring

private lemma hSeries_eq : hSeries = 𝐂 144 * etaSeries lastPowers := by
  unfold hSeries lastTerm etaSeries productFactors
  rw [show (∑ i, level i * lastPowers i) / 24 = 19 + 3 by decide, pow_add]
  simp only [map_ofNat]
  ring

private lemma combinedForm_apply (z : ℍ) :
    combinedForm z = 36 * etaProduct thetaPowers z + etaProduct denominatorPowers z * eForm z -
      120 * etaProduct firstPowers z - 96 * etaProduct secondPowers z := rfl

private lemma gSeries_spec : HasQSeries gSeries combinedForm := by
  rw [gSeries_eq]
  have hA := (etaSeries_spec (fun i => 2 * thetaPowers i) (by decide)).smul 36
  have hD := (etaSeries_spec (fun i => 2 * denominatorPowers i) (by decide)).mul
    eisensteinSeries40_spec
  have hB := (etaSeries_spec (fun i => 2 * firstPowers i) (by decide)).smul 120
  have hC := (etaSeries_spec (fun i => 2 * secondPowers i) (by decide)).smul 96
  have hh := ((hA.add hD).sub hB).sub hC
  convert hh using 1
  ext z
  rw [combinedForm_apply]
  simp only [etaPowers_even, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]

private lemma hSeries_spec : HasQSeries hSeries ((144 : ℂ) • etaPowers lastPowers) := by
  rw [hSeries_eq]
  exact (etaSeries_spec lastPowers (by decide)).smul 144

private lemma differenceForm_apply (z : ℍ) :
    differenceForm z = combinedForm z * combinedForm z -
      (144 : ℂ) ^ 2 * etaProduct lastPowers z := by
  simp only [differenceForm, FunLike.coe_sub, ModularForm.mcast_apply, ModularForm.coe_mul,
    FunLike.coe_smul, Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  rfl

private lemma differenceSeries_spec :
    HasQSeries ((gSeries - hSeries) * (gSeries + hSeries)) differenceForm := by
  rw [show (gSeries - hSeries) * (gSeries + hSeries) =
    gSeries * gSeries - hSeries * hSeries by ring]
  have hh := (gSeries_spec.mul gSeries_spec).sub (hSeries_spec.mul hSeries_spec)
  convert hh using 1
  ext z
  have he := congrFun (etaPowers_sq lastPowers) z
  simp only [Pi.mul_apply] at he
  rw [differenceForm_apply, ← he]
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring

private lemma g_sub_h_dvd : 𝐗 ^ 193 ∣ gSeries - hSeries := by
  rw [gSeries, hSeries, ← mul_sub, show (193 : ℕ) = 19 + cutoff by decide, pow_add]
  exact mul_dvd_mul_left _ normalized_difference_dvd

private lemma period_one : (1 : ℝ) ∈
    (CongruenceSubgroup.Gamma0 40 : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp [CongruenceSubgroup.strictPeriods_Gamma0]

private lemma differenceForm_zero : differenceForm = 0 := by
  apply ModularForm.sturm_bound_Gamma0 40
  intro n hn
  have hi : (32 * ((CongruenceSubgroup.Gamma0 40).index : ℤ)).toNat ≤ 2304 := by
    have hh : ((CongruenceSubgroup.Gamma0 40).index : ℤ) ≤ 72 := by exact_mod_cast index_bound
    omega
  have hn' : n < 193 := by omega
  rw [← ModularFormClass.qExpansion_coeff_unique one_pos period_one
    (fun z => by simpa only [smul_eq_mul] using differenceSeries_spec z) n]
  exact (PowerSeries.X_pow_dvd_iff.mp (dvd_mul_of_dvd_left g_sub_h_dvd _)) n hn'

private lemma hSeries_coeff : hSeries.coeff 22 = 144 := by
  rw [hSeries_eq, PowerSeries.coeff_C_mul, etaSeries,
    show (∑ i, level i * lastPowers i) / 24 = 22 by decide,
    PowerSeries.coeff_X_pow_mul']
  have he : (PowerSeries.pentagonalSeries ℂ).constantCoeff = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [← show pentagonal 0 = 0 by norm_num [pentagonal_def],
      PowerSeries.coeff_pentagonalSeries_pentagonal]
    simp
  simp [eulerSeries, PowerSeries.coeff_zero_eq_constantCoeff_apply, he]

private lemma series_identity : gSeries = hSeries := by
  have hzero : (gSeries - hSeries) * (gSeries + hSeries) = 0 := by
    apply PowerSeries.ext
    intro n
    have he := ModularFormClass.qExpansion_coeff_unique (f := differenceForm)
      (c := fun m => ((gSeries - hSeries) * (gSeries + hSeries)).coeff m) one_pos period_one
      (fun z => by simpa only [smul_eq_mul] using differenceSeries_spec z) n
    rw [he]
    simp [differenceForm_zero, qExpansion_zero]
  rcases mul_eq_zero.mp hzero with h | h
  · exact sub_eq_zero.mp h
  · have hc := PowerSeries.X_pow_dvd_iff.mp g_sub_h_dvd 22 (by decide)
    have hh := congrArg (fun p : PowerSeries ℂ => p.coeff 22) h
    simp only [map_sub, map_add, hSeries_coeff, map_zero] at hc hh
    rw [sub_eq_zero.mp hc] at hh
    norm_num at hh

private lemma modular_identity (z : ℍ) : combinedForm z = (144 : ℂ) * etaPowers lastPowers z := by
  have h := gSeries_spec z
  rw [series_identity] at h
  exact h.unique (hSeries_spec z)

private lemma raw_ne_zero (q : ℂ) (hq : ‖q‖ < 1) : 𝔣 q ≠ 0 :=
  euler_eq_raw q hq ▸ euler_ne_zero q hq

private lemma norm_pow_lt_one {q : ℂ} (hq : ‖q‖ < 1) {n : ℕ} (hn : n ≠ 0) :
    ‖q ^ n‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) hq hn

private lemma square_term (q : ℂ) (n : ℤ) :
    ramanujanThetaTerm q q n = q ^ (n * n).toNat := by
  rw [ramanujanThetaTerm, ← pow_add]
  congr 1
  have hp : 0 ≤ n * (n + 1) := by
    rcases le_or_gt 0 n with hn | hn
    · exact mul_nonneg hn (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos hn.le (by omega)
  have hm : 0 ≤ n * (n - 1) := by
    rcases le_or_gt n 0 with hn | hn
    · exact mul_nonneg_of_nonpos_of_nonpos hn (by omega)
    · exact mul_nonneg hn.le (by omega)
  have hp' := Int.ediv_mul_cancel (Int.even_mul_succ_self n).two_dvd
  have hm' := Int.ediv_mul_cancel (Int.even_mul_pred_self n).two_dvd
  apply Int.ofNat_inj.mp
  rw [Nat.cast_add, Int.toNat_of_nonneg (Int.ediv_nonneg hp (by decide)),
    Int.toNat_of_nonneg (Int.ediv_nonneg hm (by decide)), Int.toNat_of_nonneg (mul_self_nonneg _)]
  linarith only [hp', hm']

private lemma phi_eq_products (q : ℂ) (hq : ‖q‖ < 1) :
    φ q = (𝔣 (q ^ 2)) ^ 5 / ((𝔣 q) ^ 2 * (𝔣 (q ^ 4)) ^ 2) := by
  have hq2 := norm_pow_lt_one hq two_ne_zero
  have hq4 := norm_pow_lt_one hq (by decide : (4 : ℕ) ≠ 0)
  have hTheta : φ q = 𝔣 (q ^ 2) * (QPochhammer.qPochhammerInfRaw (-q) (q ^ 2)) ^ 2 := by
    obtain ⟨_, _, h⟩ :=
      Analysis.SpecialFunctions.JacobiTripleProduct.jacobi_triple_product 1 q one_ne_zero hq
    simp only [one_zpow, one_mul, inv_one] at h
    simp only [ramanujanThetaRaw, square_term, h]
    have h1 := QPochhammer.hasProd_qPochhammerInf (q ^ 2) (q ^ 2) hq2
    have h2 := QPochhammer.hasProd_qPochhammerInf (-q) (q ^ 2) hq2
    have hp := (h1.mul h2).mul h2
    rw [pow_two (QPochhammer.qPochhammerInfRaw (-q) (q ^ 2)), ← mul_assoc]
    refine HasProd.tprod_eq (hp.congr_fun fun n => ?_)
    simp only [pow_mul, pow_add, neg_mul, sub_neg_eq_add]
    ring
  rw [hTheta, (ramanujan_psi_f_chi_eq_qPochhammer q hq).2.2.1]
  field_simp [raw_ne_zero q hq, raw_ne_zero _ hq4]

private lemma etaPowers_at (s : Fin 8 → ℕ) (hs : 24 ∣ ∑ i, level i * s i)
    (z : ℍ) {q : ℂ} (hQ : 𝕢 (z : ℂ) = q) (hq : ‖q‖ < 1) :
    etaPowers s z = q ^ ((∑ i, level i * s i) / 24) * ∏ i, (𝔣 (q ^ level i)) ^ s i := by
  rw [etaPowers_eq s hs z, hQ]
  simp_rw [euler_eq_raw _ (norm_pow_lt_one hq (level_pos _).ne')]

private lemma eisenstein_eq (z : ℍ) {q : ℂ} (hQ : 𝕢 (z : ℂ) = q) :
    eForm z = 𝐏 q - 𝐏 (q ^ 2) + 2 * 𝐏 (q ^ 4) + 5 * 𝐏 (q ^ 5) - 8 * 𝐏 (q ^ 8) -
      5 * 𝐏 (q ^ 10) + 10 * 𝐏 (q ^ 20) - 40 * 𝐏 (q ^ 40) := by
  change (∑ i, (eWeight i • eAt i) z) = _
  have he (i : Fin 8) : (eWeight i • eAt i) z = eCoeff i * 𝐏 (q ^ level i) := by
    simp only [Pi.smul_apply, smul_eq_mul, eWeight, eAt_apply, ← lambert_eq_e2, qparam_dilate, hQ]
    have hd : (level i : ℂ) ≠ 0 := by exact_mod_cast (level_pos i).ne'
    field_simp
  simp only [he, Fin.sum_univ_succ, eCoeff, eisensteinWeights, level, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Int.cast_one, Int.cast_neg, Int.cast_ofNat, Finset.univ_eq_empty,
    Finset.sum_empty, pow_one, one_mul, neg_mul, add_zero]
  ring

end phi_sq_mul_phi_sq_ten_eisenstein

open phi_sq_mul_phi_sq_ten_eisenstein in
/-- **Eisenstein-series formula for $\varphi(q)^2\varphi(q^{10})^2$.** Let $q$ be
a complex number with $|q| < 1$. Write $\varphi(x) = \sum_{n \in \mathbb{Z}} x^{n^2}$ for
Ramanujan's theta function, $f_k = \prod_{m \ge 1} (1 - q^{km})$, and $P_k = P(q^k)$, where
$P(x) = 1 - 24 \sum_{m \ge 1} m x^m / (1 - x^m)$ is the weight-two Eisenstein series. Then
$$
\varphi(q)^2\varphi(q^{10})^2 = -\tfrac{1}{36}(P_1 - P_2 + 2P_4 + 5P_5 - 8P_8 - 5P_{10} + 10P_{20} -
40P_{40}) + \tfrac{10}{3} q f_2^2 f_{10}^2 + \tfrac{8}{3} q^2 f_4^2 f_{20}^2 +
4q^3 \frac{f_4^5 f_{10} f_{40}^2}{f_2 f_8^2 f_{20}}.
$$

Source: K. R. Vasuki and P. Nagendra, *On Certain Quaternary Quadratic Forms*, INTEGERS 25
(2025), Article A24, Lemma 3.3, Equation (3.13). The printed (3.13) has $4q^2$ in the last term (as
do (3.14)–(3.16)); the exponent must be $3$, as stated here, since the $q$-expansions agree only
with $q^3$. -/
public theorem phi_sq_mul_phi_sq_ten_eisenstein (q : ℂ) (hq : ‖q‖ < 1) :
    (φ q) ^ 2 * (φ (q ^ 10)) ^ 2 =
      -(1 / 36) * (𝐏 q - 𝐏 (q ^ 2) + 2 * 𝐏 (q ^ 4) + 5 * 𝐏 (q ^ 5) - 8 * 𝐏 (q ^ 8)
          - 5 * 𝐏 (q ^ 10) + 10 * 𝐏 (q ^ 20) - 40 * 𝐏 (q ^ 40))
        + 10 / 3 * q * (𝔣 (q ^ 2)) ^ 2 * (𝔣 (q ^ 10)) ^ 2
        + 8 / 3 * q ^ 2 * (𝔣 (q ^ 4)) ^ 2 * (𝔣 (q ^ 20)) ^ 2
        + 4 * q ^ 3 * ((𝔣 (q ^ 4)) ^ 5 * 𝔣 (q ^ 10) * (𝔣 (q ^ 40)) ^ 2
          / (𝔣 (q ^ 2) * (𝔣 (q ^ 8)) ^ 2 * 𝔣 (q ^ 20))) := by
  by_cases hq0 : q = 0
  · subst q
    have hφ : φ (0 : ℂ) = 1 := by
      rw [phi_eq_products 0 hq]
      simp [QPochhammer.qPochhammerInfRaw]
    norm_num [hφ, zero_pow (Nat.succ_ne_zero _)]
  · let z : ℍ := ⟨Function.Periodic.invQParam 1 q,
      Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos hq hq0⟩
    have hz : 𝕢 (z : ℂ) = q := Function.Periodic.qParam_right_inv one_ne_zero hq0
    have hpow (n : ℕ) (hn : n ≠ 0) : 𝔣 (q ^ n) ≠ 0 := raw_ne_zero _ (norm_pow_lt_one hq hn)
    have hθ2 := phi_eq_products (q ^ 10) (norm_pow_lt_one hq (by decide))
    simp only [← pow_mul] at hθ2
    have hη (r : Fin 8 → ℕ) (hr : 24 ∣ ∑ i, level i * (2 * r i)) :
        etaProduct r z = q ^ ((∑ i, level i * (2 * r i)) / 24) *
          ∏ i, (𝔣 (q ^ level i)) ^ (2 * r i) := by
      rw [← etaPowers_even]
      exact etaPowers_at _ hr z hz hq
    have hD := hη denominatorPowers (by decide)
    have hA := hη thetaPowers (by decide)
    have hB := hη firstPowers (by decide)
    have hC := hη secondPowers (by decide)
    have hG := etaPowers_at lastPowers (by decide) z hz hq
    have hA' : etaProduct thetaPowers z =
        etaProduct denominatorPowers z * ((φ q) ^ 2 * (φ (q ^ 10)) ^ 2) := by
      rw [hA, hD, phi_eq_products q hq, hθ2]
      simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, level, thetaPowers, denominatorPowers,
        Matrix.cons_val_zero, Matrix.cons_val_succ, Finset.univ_eq_empty, Finset.prod_empty,
        Finset.sum_empty]
      norm_num
      field_simp [raw_ne_zero q hq, hpow 4 (by decide), hpow 10 (by decide), hpow 40 (by decide)]
    have hB' : etaProduct firstPowers z =
        etaProduct denominatorPowers z * (q * (𝔣 (q ^ 2)) ^ 2 * (𝔣 (q ^ 10)) ^ 2) := by
      rw [hB, hD]
      simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, level, firstPowers, denominatorPowers,
        Matrix.cons_val_zero, Matrix.cons_val_succ, Finset.univ_eq_empty, Finset.prod_empty,
        Finset.sum_empty]
      norm_num
      ring
    have hC' : etaProduct secondPowers z =
        etaProduct denominatorPowers z * (q ^ 2 * (𝔣 (q ^ 4)) ^ 2 * (𝔣 (q ^ 20)) ^ 2) := by
      rw [hC, hD]
      simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, level, secondPowers, denominatorPowers,
        Matrix.cons_val_zero, Matrix.cons_val_succ, Finset.univ_eq_empty, Finset.prod_empty,
        Finset.sum_empty]
      norm_num
      ring
    have hG' : etaPowers lastPowers z = etaProduct denominatorPowers z *
        (q ^ 3 * ((𝔣 (q ^ 4)) ^ 5 * 𝔣 (q ^ 10) * (𝔣 (q ^ 40)) ^ 2 /
          (𝔣 (q ^ 2) * (𝔣 (q ^ 8)) ^ 2 * 𝔣 (q ^ 20)))) := by
      rw [hG, hD]
      simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, level, lastPowers, denominatorPowers,
        Matrix.cons_val_zero, Matrix.cons_val_succ, Finset.univ_eq_empty, Finset.prod_empty,
        Finset.sum_empty]
      norm_num
      field_simp [hpow 2 (by decide), hpow 8 (by decide), hpow 20 (by decide)]
    have hDne : etaProduct denominatorPowers z ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ =>
        pow_ne_zero _ (pow_ne_zero _ (eta_ne_zero (dilate i • z : ℍ).2))
    have h := modular_identity z
    rw [combinedForm_apply, hA', hB', hC', hG', eisenstein_eq z hz] at h
    apply mul_left_cancel₀ hDne
    linear_combination h / 36

end MetaMathlibExt
