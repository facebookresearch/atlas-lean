/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
-/

/-
Adapted from:

`Theorems/Thm_ModularCurve_SerreImage_contains_SL2.lean`,
`P2M/Sol/S_ModularCurve_SerreImage_contains_SL2.lean`, and
`Definitions/Def_ModularCurve_SL2Elementary.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style. The source's elementary
matrices and its generation lemma for `SL(2, ZMod N)` are replaced by Mathlib's
`Matrix.SpecialLinearGroup.transvection` and `Matrix.SL2.transvection_induction`.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.Group
import Mathlib.Tactic.NoncommRing

/-!
# Irreducible subgroups of `GL(2, ZMod p)` with a nontrivial unipotent

For a prime `p`, a subgroup of `GL(2, ZMod p)` that leaves no line invariant and contains a
nontrivial square-zero unipotent contains the image of `SL(2, ZMod p)`. The proof finds a basis in
which the unipotent and its conjugate by an element of the subgroup are an upper and a lower
transvection with nonzero entries. Their powers give every transvection in that basis, and
Mathlib's `Matrix.SL2.transvection_induction` generates `SL(2, ZMod p)` from them.

## Main statement

* `SL2.range_toGL_le_of_irreducible_of_exists_unipotent`
-/

@[expose] public section

open Matrix MatrixGroups Subgroup

namespace SL2

private lemma transvection_pow {R : Type*} [CommRing R] {i j : Fin 2} (hij : i ≠ j) (a : R)
    (n : ℕ) :
    SpecialLinearGroup.transvection hij a ^ n =
      SpecialLinearGroup.transvection hij ((n : R) * a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, ← SpecialLinearGroup.transvection_add]
    congr 1
    push_cast
    ring

private lemma transvection_zero_one_coe {R : Type*} [CommRing R] (b : R) :
    ((SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) b : SL(2, R)) :
      Matrix (Fin 2) (Fin 2) R) = !![1, b; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.transvection_coe]

private lemma transvection_one_zero_coe {R : Type*} [CommRing R] (b : R) :
    ((SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) b : SL(2, R)) :
      Matrix (Fin 2) (Fin 2) R) = !![1, 0; b, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.transvection_coe]

section Generation

variable {p : ℕ} [Fact p.Prime]

private lemma exists_natCast_mul_eq {a : ZMod p} (ha : a ≠ 0) (c : ZMod p) :
    ∃ n : ℕ, (n : ZMod p) * a = c := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective (c * a⁻¹)
  refine ⟨n, ?_⟩
  rw [hn, mul_assoc, ZMod.inv_mul_of_unit a (isUnit_iff_ne_zero.mpr ha), mul_one]

private theorem range_toGL_le_of_conj_transvection (H : Subgroup (GL (Fin 2) (ZMod p)))
    (P : GL (Fin 2) (ZMod p)) {a b : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0)
    (hu : P * Matrix.SpecialLinearGroup.toGL
      (SpecialLinearGroup.transvection zero_ne_one a) * P⁻¹ ∈ H)
    (hl : P * Matrix.SpecialLinearGroup.toGL
      (SpecialLinearGroup.transvection one_ne_zero b) * P⁻¹ ∈ H) :
    (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := ZMod p)).range ≤ H := by
  set φ : SL(2, ZMod p) →* GL (Fin 2) (ZMod p) :=
    ((MulAut.conj P).toMonoidHom).comp (Matrix.SpecialLinearGroup.toGL) with hφdef
  have hφ : ∀ M : SL(2, ZMod p),
      φ M = P * Matrix.SpecialLinearGroup.toGL M * P⁻¹ := fun M => rfl
  have htrans : ∀ {i j : Fin 2} (hij : i ≠ j) {x : ZMod p}, x ≠ 0 →
      φ (SpecialLinearGroup.transvection hij x) ∈ H →
        ∀ c, φ (SpecialLinearGroup.transvection hij c) ∈ H := by
    intro i j hij x hx hmem c
    obtain ⟨n, hn⟩ := exists_natCast_mul_eq hx c
    rw [← hn, ← transvection_pow, map_pow]
    exact pow_mem hmem n
  have hrange : φ.range ≤ H := by
    rintro _ ⟨A, rfl⟩
    refine Matrix.SL2.transvection_induction (fun A => φ A ∈ H) (fun i j hij c => ?_)
      (fun A B hA hB => by rw [map_mul]; exact mul_mem hA hB) A
    have hi : i = 0 ∨ i = 1 := by omega
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (hij rfl).elim
    · exact htrans hij ha (by rw [hφ]; exact hu) c
    · exact htrans hij hb (by rw [hφ]; exact hl) c
    · exact (hij rfl).elim
  intro g hg
  obtain ⟨M, rfl⟩ := MonoidHom.mem_range.mp hg
  have hker : P⁻¹ * Matrix.SpecialLinearGroup.toGL M * P ∈
      (Matrix.GeneralLinearGroup.det : GL (Fin 2) (ZMod p) →* (ZMod p)ˣ).ker := by
    simp
  obtain ⟨N, hN⟩ := Matrix.SpecialLinearGroup.range_toGL_eq_ker_det.ge hker
  have hgoal : Matrix.SpecialLinearGroup.toGL M = φ N := by
    rw [hφ, hN]
    group
  rw [hgoal]
  exact hrange ⟨N, rfl⟩

end Generation

section Unipotent

variable {F : Type*} [Field F]

private lemma funext_fin_two {α : Type*} {f g : Fin 2 → α} (h0 : f 0 = g 0) (h1 : f 1 = g 1) :
    f = g := by
  funext i
  fin_cases i
  · exact h0
  · exact h1

private lemma mulVec_e0 (M : Matrix (Fin 2) (Fin 2) F) : M.mulVec ![1, 0] = ![M 0 0, M 1 0] := by
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private lemma mulVec_e1 (M : Matrix (Fin 2) (Fin 2) F) : M.mulVec ![0, 1] = ![M 0 1, M 1 1] := by
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private lemma exists_fixed_vec {M : Matrix (Fin 2) (Fin 2) F} (h : (M - 1) ^ 2 = 0) :
    ∃ v : Fin 2 → F, v ≠ 0 ∧ M.mulVec v = v := by
  have hdet : Matrix.det (M - 1) = 0 := by
    have h2 : Matrix.det (M - 1) ^ 2 = 0 := by
      rw [← Matrix.det_pow, h, Matrix.det_zero]
    exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h2
  obtain ⟨v, hv, hMv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  refine ⟨v, hv, ?_⟩
  have h1 : (M - 1).mulVec v = M.mulVec v - (1 : Matrix (Fin 2) (Fin 2) F).mulVec v :=
    Matrix.sub_mulVec M 1 v
  rw [Matrix.one_mulVec, hMv] at h1
  exact sub_eq_zero.mp h1.symm

private lemma exists_smul_eq_of_cross_eq_zero {v w : Fin 2 → F} (hv : v ≠ 0)
    (hD : v 0 * w 1 - v 1 * w 0 = 0) : ∃ c : F, w = c • v := by
  have hkey : v 0 * w 1 = v 1 * w 0 := sub_eq_zero.mp hD
  have hv' : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra hc
    simp only [not_or, not_not] at hc
    exact hv (funext_fin_two hc.1 hc.2)
  rcases eq_or_ne (v 0) 0 with h0 | h0
  · have hv1 : v 1 ≠ 0 := by
      rcases hv' with h | h
      · exact absurd h0 h
      · exact h
    have hw0 : w 0 = 0 := by
      have hmul : v 1 * w 0 = 0 := by
        have h' := hD
        rw [h0, zero_mul, zero_sub, neg_eq_zero] at h'
        exact h'
      exact (mul_eq_zero.mp hmul).resolve_left hv1
    refine ⟨w 1 / v 1, funext_fin_two ?_ ?_⟩
    · change w 0 = w 1 / v 1 * v 0
      rw [hw0, h0, mul_zero]
    · change w 1 = w 1 / v 1 * v 1
      rw [div_mul_cancel₀ _ hv1]
  · refine ⟨w 0 / v 0, funext_fin_two ?_ ?_⟩
    · change w 0 = w 0 / v 0 * v 0
      rw [div_mul_cancel₀ _ h0]
    · change w 1 = w 0 / v 0 * v 1
      rw [div_mul_eq_mul_div, eq_div_iff h0]
      linear_combination hkey

private lemma eq_upper_of_fixes_e0 {Q : Matrix (Fin 2) (Fin 2) F} (hQ : (Q - 1) ^ 2 = 0)
    (hfix : Q.mulVec ![1, 0] = ![1, 0]) : Q = !![1, Q 0 1; 0, 1] := by
  rw [mulVec_e0] at hfix
  have e00 : Q 0 0 = 1 := congrFun hfix 0
  have e10 : Q 1 0 = 0 := congrFun hfix 1
  have key : (Q 1 1 - 1) * (Q 1 1 - 1) = 0 := by
    have h11 := (Matrix.ext_iff.mpr hQ) 1 1
    rw [Matrix.zero_apply, pow_two, Matrix.mul_apply, Fin.sum_univ_two] at h11
    simp only [Matrix.sub_apply, Matrix.one_apply_eq,
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), e10, sub_zero, zero_mul,
      zero_add] at h11
    exact h11
  have e11 : Q 1 1 = 1 := sub_eq_zero.mp (mul_self_eq_zero.mp key)
  conv_lhs => rw [Matrix.eta_fin_two Q]
  rw [e00, e10, e11]

private lemma eq_lower_of_fixes_e1 {Q : Matrix (Fin 2) (Fin 2) F} (hQ : (Q - 1) ^ 2 = 0)
    (hfix : Q.mulVec ![0, 1] = ![0, 1]) : Q = !![1, 0; Q 1 0, 1] := by
  rw [mulVec_e1] at hfix
  have e01 : Q 0 1 = 0 := congrFun hfix 0
  have e11 : Q 1 1 = 1 := congrFun hfix 1
  have key : (Q 0 0 - 1) * (Q 0 0 - 1) = 0 := by
    have h00 := (Matrix.ext_iff.mpr hQ) 0 0
    rw [Matrix.zero_apply, pow_two, Matrix.mul_apply, Fin.sum_univ_two] at h00
    simp only [Matrix.sub_apply, Matrix.one_apply_eq,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), e01, sub_zero, zero_mul,
      add_zero] at h00
    exact h00
  have e00 : Q 0 0 = 1 := sub_eq_zero.mp (mul_self_eq_zero.mp key)
  conv_lhs => rw [Matrix.eta_fin_two Q]
  rw [e00, e01, e11]

end Unipotent


variable {p : ℕ} [Fact p.Prime]

local notation "𝕄" => Matrix (Fin 2) (Fin 2) (ZMod p)

private lemma conj_unipotent {g : GL (Fin 2) (ZMod p)} (h : GL (Fin 2) (ZMod p))
    (hg : ((g : 𝕄) - 1) ^ 2 = 0) :
    (((h * g * h⁻¹ : GL (Fin 2) (ZMod p)) : 𝕄) - 1) ^ 2 = 0 := by
  have hinv : (h : 𝕄) * ((h⁻¹ : GL (Fin 2) (ZMod p)) : 𝕄) = 1 := Units.mul_inv h
  have hinv' : ((h⁻¹ : GL (Fin 2) (ZMod p)) : 𝕄) * (h : 𝕄) = 1 := Units.inv_mul h
  have key : ((h * g * h⁻¹ : GL (Fin 2) (ZMod p)) : 𝕄) - 1 =
      (h : 𝕄) * ((g : 𝕄) - 1) * ((h⁻¹ : GL (Fin 2) (ZMod p)) : 𝕄) := by
    have hexpand : (h : 𝕄) * ((g : 𝕄) - 1) * ((h⁻¹ : GL (Fin 2) (ZMod p)) : 𝕄) =
        (h : 𝕄) * (g : 𝕄) * ((h⁻¹ : GL (Fin 2) (ZMod p)) : 𝕄) -
          (h : 𝕄) * ((h⁻¹ : GL (Fin 2) (ZMod p)) : 𝕄) := by
      noncomm_ring
    rw [hexpand, hinv, Units.val_mul, Units.val_mul]
  have hsq : ((h : 𝕄) * ((g : 𝕄) - 1) * ((h⁻¹ : GL (Fin 2) (ZMod p)) : 𝕄)) ^ 2 =
      (h : 𝕄) * (((g : 𝕄) - 1) * (((h⁻¹ : GL (Fin 2) (ZMod p)) : 𝕄) * (h : 𝕄)) *
        ((g : 𝕄) - 1)) * ((h⁻¹ : GL (Fin 2) (ZMod p)) : 𝕄) := by
    rw [pow_two]
    noncomm_ring
  rw [key, hsq, hinv', mul_one, ← pow_two, hg, mul_zero, zero_mul]

/-- **Irreducible subgroups with a nontrivial unipotent contain `SL(2, ZMod p)`.** For a prime `p`,
a subgroup of `GL(2, ZMod p)` that leaves no line invariant (an irreducible subgroup) and contains
a nontrivial square-zero unipotent contains the image of `SL(2, ZMod p)`. -/
theorem range_toGL_le_of_irreducible_of_exists_unipotent (H : Subgroup (GL (Fin 2) (ZMod p)))
    (hirr : ∀ v : Fin 2 → ZMod p, v ≠ 0 → ∃ g ∈ H, ∀ c : ZMod p,
      ((g : GL (Fin 2) (ZMod p)) : 𝕄).mulVec v ≠ c • v)
    (hunip : ∃ u ∈ H, ((u : 𝕄) - 1) ^ 2 = 0 ∧ u ≠ 1) :
    (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := ZMod p)).range ≤ H := by
  classical
  obtain ⟨u, huH, hu2, hu1⟩ := hunip
  obtain ⟨v, hv0, hv⟩ := exists_fixed_vec hu2
  obtain ⟨h, hhH, hmove⟩ := hirr v hv0
  have hu'H : h * u * h⁻¹ ∈ H := mul_mem (mul_mem hhH huH) (inv_mem hhH)
  have hu'2 : (((h * u * h⁻¹ : GL (Fin 2) (ZMod p)) : 𝕄) - 1) ^ 2 = 0 :=
    conj_unipotent h hu2
  set w : Fin 2 → ZMod p := ((h : GL (Fin 2) (ZMod p)) : 𝕄).mulVec v with hwdef
  have hinvh : ((h⁻¹ : GL (Fin 2) (ZMod p)) : 𝕄) * (h : 𝕄) = 1 := Units.inv_mul h
  have hw : ((h * u * h⁻¹ : GL (Fin 2) (ZMod p)) : 𝕄).mulVec w = w := by
    rw [hwdef, Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec,
      mul_assoc ((h : 𝕄) * (u : 𝕄)), hinvh, mul_one, ← Matrix.mulVec_mulVec, hv]
  have hD : v 0 * w 1 - v 1 * w 0 ≠ 0 := by
    intro hD0
    obtain ⟨c, hc⟩ := exists_smul_eq_of_cross_eq_zero hv0 hD0
    exact hmove c hc
  have hdetP : Matrix.det (!![v 0, w 0; v 1, w 1] : 𝕄) ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    intro hc
    apply hD
    linear_combination hc
  set P : GL (Fin 2) (ZMod p) := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdetP with hPdef
  have hPcoe : (P : 𝕄) = !![v 0, w 0; v 1, w 1] := rfl
  have hPinv : ((P⁻¹ : GL (Fin 2) (ZMod p)) : 𝕄) * (P : 𝕄) = 1 := Units.inv_mul P
  have hPinv' : (P : 𝕄) * ((P⁻¹ : GL (Fin 2) (ZMod p)) : 𝕄) = 1 := Units.mul_inv P
  have hPe0 : (P : 𝕄).mulVec ![1, 0] = v := by
    rw [hPcoe, mulVec_e0]
    funext i
    fin_cases i <;> simp
  have hPe1 : (P : 𝕄).mulVec ![0, 1] = w := by
    rw [hPcoe, mulVec_e1]
    funext i
    fin_cases i <;> simp
  have hPiv : ((P⁻¹ : GL (Fin 2) (ZMod p)) : 𝕄).mulVec v = ![1, 0] := by
    rw [← hPe0, Matrix.mulVec_mulVec, hPinv, Matrix.one_mulVec]
  have hPiw : ((P⁻¹ : GL (Fin 2) (ZMod p)) : 𝕄).mulVec w = ![0, 1] := by
    rw [← hPe1, Matrix.mulVec_mulVec, hPinv, Matrix.one_mulVec]
  have hconjfix : ∀ (g : GL (Fin 2) (ZMod p)) (x : Fin 2 → ZMod p),
      (g : 𝕄).mulVec x = x →
      ((P⁻¹ * g * P : GL (Fin 2) (ZMod p)) : 𝕄).mulVec
        (((P⁻¹ : GL (Fin 2) (ZMod p)) : 𝕄).mulVec x) =
        ((P⁻¹ : GL (Fin 2) (ZMod p)) : 𝕄).mulVec x := by
    intro g x hx
    rw [Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec,
      mul_assoc (((P⁻¹ : GL (Fin 2) (ZMod p)) : 𝕄) * (g : 𝕄)), hPinv', mul_one,
      ← Matrix.mulVec_mulVec, hx]
  have hQ2 : (((P⁻¹ * u * P : GL (Fin 2) (ZMod p)) : 𝕄) - 1) ^ 2 = 0 := by
    have hc := conj_unipotent (g := u) P⁻¹ hu2
    rwa [inv_inv] at hc
  have hQfix : ((P⁻¹ * u * P : GL (Fin 2) (ZMod p)) : 𝕄).mulVec ![1, 0] = ![1, 0] := by
    have hc := hconjfix u v hv
    rwa [hPiv] at hc
  have hQform : ((P⁻¹ * u * P : GL (Fin 2) (ZMod p)) : 𝕄) =
      !![1, ((P⁻¹ * u * P : GL (Fin 2) (ZMod p)) : 𝕄) 0 1; 0, 1] :=
    eq_upper_of_fixes_e0 hQ2 hQfix
  have hQ'2 : (((P⁻¹ * (h * u * h⁻¹) * P : GL (Fin 2) (ZMod p)) : 𝕄) - 1) ^ 2 = 0 := by
    have hc := conj_unipotent (g := h * u * h⁻¹) P⁻¹ hu'2
    rwa [inv_inv] at hc
  have hQ'fix : ((P⁻¹ * (h * u * h⁻¹) * P : GL (Fin 2) (ZMod p)) : 𝕄).mulVec ![0, 1] =
      ![0, 1] := by
    have hc := hconjfix (h * u * h⁻¹) w hw
    rwa [hPiw] at hc
  have hQ'form : ((P⁻¹ * (h * u * h⁻¹) * P : GL (Fin 2) (ZMod p)) : 𝕄) =
      !![1, 0; ((P⁻¹ * (h * u * h⁻¹) * P : GL (Fin 2) (ZMod p)) : 𝕄) 1 0, 1] :=
    eq_lower_of_fixes_e1 hQ'2 hQ'fix
  have hQeq : P⁻¹ * u * P = Matrix.SpecialLinearGroup.toGL
      (SpecialLinearGroup.transvection zero_ne_one
        (((P⁻¹ * u * P : GL (Fin 2) (ZMod p)) : 𝕄) 0 1)) := by
    apply Units.ext
    exact hQform.trans (transvection_zero_one_coe _).symm
  have hQ'eq : P⁻¹ * (h * u * h⁻¹) * P = Matrix.SpecialLinearGroup.toGL
      (SpecialLinearGroup.transvection one_ne_zero
        (((P⁻¹ * (h * u * h⁻¹) * P : GL (Fin 2) (ZMod p)) : 𝕄) 1 0)) := by
    apply Units.ext
    exact hQ'form.trans (transvection_one_zero_coe _).symm
  have ha : ((P⁻¹ * u * P : GL (Fin 2) (ZMod p)) : 𝕄) 0 1 ≠ 0 := by
    intro ha0
    apply hu1
    have h1 : P⁻¹ * u * P = 1 := by
      rw [hQeq, ha0, SpecialLinearGroup.transvection_coeff_zero]
      exact map_one _
    calc u = P * (P⁻¹ * u * P) * P⁻¹ := by group
    _ = P * 1 * P⁻¹ := by rw [h1]
    _ = 1 := by group
  have hb : ((P⁻¹ * (h * u * h⁻¹) * P : GL (Fin 2) (ZMod p)) : 𝕄) 1 0 ≠ 0 := by
    intro hb0
    have hu'1 : h * u * h⁻¹ = 1 := by
      have h1 : P⁻¹ * (h * u * h⁻¹) * P = 1 := by
        rw [hQ'eq, hb0, SpecialLinearGroup.transvection_coeff_zero]
        exact map_one _
      calc h * u * h⁻¹ = P * (P⁻¹ * (h * u * h⁻¹) * P) * P⁻¹ := by group
      _ = P * 1 * P⁻¹ := by rw [h1]
      _ = 1 := by group
    apply hu1
    calc u = h⁻¹ * (h * u * h⁻¹) * h := by group
    _ = h⁻¹ * 1 * h := by rw [hu'1]
    _ = 1 := by group
  refine range_toGL_le_of_conj_transvection H P ha hb ?_ ?_
  · rw [← hQeq]
    have hPQ : P * (P⁻¹ * u * P) * P⁻¹ = u := by group
    rw [hPQ]
    exact huH
  · rw [← hQ'eq]
    have hPQ : P * (P⁻¹ * (h * u * h⁻¹) * P) * P⁻¹ = h * u * h⁻¹ := by group
    rw [hPQ]
    exact hu'H


end SL2
