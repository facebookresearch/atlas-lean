/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularCurve_SerreImage_contains_SL2.lean`,
`P2M/Sol/S_ModularCurve_SerreImage_contains_SL2.lean`,
`Definitions/Def_ModularCurve_SL2Elementary.lean`,
`Theorems/Thm_ModularCurve_closure_elemSet_eq_top.lean`,
`P2M/Sol/S_ModularCurve_closure_elemSet_eq_top.lean`,
`Theorems/Thm_ModularCurve_surjective_specialLinearGroup_map_zmod.lean`, and
`P2M/Sol/S_ModularCurve_surjective_specialLinearGroup_map_zmod.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.Int.GCD
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Tactic.Group
import Mathlib.Tactic.NoncommRing

@[expose] public section

open Matrix MatrixGroups Subgroup

namespace SL2

variable {R : Type*} [CommRing R]

/-- The upper elementary matrix with entry `c` in `SL(2, R)`. -/
def upperElem (c : R) : SL(2, R) :=
  ⟨!![1, c; 0, 1], by simp [Matrix.det_fin_two_of]⟩

/-- The lower elementary matrix with entry `c` in `SL(2, R)`. -/
def lowerElem (c : R) : SL(2, R) :=
  ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two_of]⟩

@[simp] lemma upperElem_coe (c : R) :
    (upperElem c : Matrix (Fin 2) (Fin 2) R) = !![1, c; 0, 1] := rfl

@[simp] lemma lowerElem_coe (c : R) :
    (lowerElem c : Matrix (Fin 2) (Fin 2) R) = !![1, 0; c, 1] := rfl

lemma upperElem_mul (a b : R) : upperElem a * upperElem b = upperElem (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

lemma lowerElem_mul (a b : R) : lowerElem a * lowerElem b = lowerElem (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma upperElem_zero : upperElem (0 : R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[simp] lemma lowerElem_zero : lowerElem (0 : R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma upperElem_pow (a : R) (n : ℕ) : upperElem a ^ n = upperElem ((n : R) * a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, upperElem_mul]
    congr 1
    push_cast
    ring

lemma lowerElem_pow (a : R) (n : ℕ) : lowerElem a ^ n = lowerElem ((n : R) * a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, lowerElem_mul]
    congr 1
    push_cast
    ring

/-- The set of upper and lower elementary matrices in `SL(2, R)`. -/
def elemSet (R : Type*) [CommRing R] : Set SL(2, R) :=
  Set.range upperElem ∪ Set.range lowerElem

private lemma upperElem_mem_closure_elemSet {R : Type*} [CommRing R] (c : R) :
    upperElem c ∈ closure (elemSet R) :=
  subset_closure (Or.inl ⟨c, rfl⟩)

private lemma lowerElem_mem_closure_elemSet {R : Type*} [CommRing R] (c : R) :
    lowerElem c ∈ closure (elemSet R) :=
  subset_closure (Or.inr ⟨c, rfl⟩)


section SurjectiveLift


private lemma natCast_dvd_int {p : ℕ} {z : ℤ} : (p : ℤ) ∣ z ↔ p ∣ z.natAbs :=
  Int.natCast_dvd

private def primeSel (c d : ℤ) : ℕ :=
  ∏ p ∈ c.natAbs.primeFactors, if p ∣ d.natAbs then 1 else p

private lemma dvd_primeSel {c d : ℤ} {p : ℕ} (hc : c ≠ 0) (hp : p.Prime)
    (hpc : (p : ℤ) ∣ c) (hpd : ¬(p : ℤ) ∣ d) : p ∣ primeSel c d := by
  have hmem : p ∈ c.natAbs.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, natCast_dvd_int.mp hpc, Int.natAbs_ne_zero.mpr hc⟩
  have h := Finset.dvd_prod_of_mem (fun q : ℕ => if q ∣ d.natAbs then 1 else q) hmem
  simp only [if_neg (fun hcontra => hpd (natCast_dvd_int.mpr hcontra))] at h
  exact h

private lemma not_dvd_primeSel {c d : ℤ} {p : ℕ} (hp : p.Prime) (hpd : (p : ℤ) ∣ d) :
    ¬p ∣ primeSel c d := by
  intro hdvd
  obtain ⟨q, hq, hpq⟩ := (Nat.Prime.prime hp).dvd_finsetProd_iff _ |>.mp hdvd
  by_cases hqd : q ∣ d.natAbs
  · rw [if_pos hqd] at hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpq)
  · rw [if_neg hqd] at hpq
    have hq' : q.Prime := (Nat.mem_primeFactors.mp hq).1
    exact hqd (((Nat.prime_dvd_prime_iff_eq hp hq').mp hpq) ▸ natCast_dvd_int.mp hpd)

private theorem exists_coprime_lift (N : ℕ) [NeZero N] {c₀ d₀ : ℤ}
    (H : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c₀ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ)) :
    ∃ γ δ : ℤ, Int.gcd γ δ = 1 ∧
      (γ : ZMod N) = (c₀ : ZMod N) ∧ (δ : ZMod N) = (d₀ : ZMod N) := by
  set γ : ℤ := if c₀ = 0 then (N : ℤ) else c₀ with hγ_def
  have hγ0 : γ ≠ 0 := by
    rw [hγ_def]
    split
    · exact_mod_cast NeZero.ne N
    · assumption
  have hγc : (γ : ZMod N) = (c₀ : ZMod N) := by
    rw [hγ_def]
    split
    · next h => simp [h]
    · rfl
  have Hγ : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ γ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ) := by
    intro p pp hpγ hpd
    refine H p pp ?_ hpd
    rw [hγ_def] at hpγ
    by_cases h : c₀ = 0
    · simp [h]
    · rwa [if_neg h] at hpγ
  refine ⟨γ, d₀ + (primeSel γ d₀ : ℤ) * (N : ℤ), ?_, hγc, ?_⟩
  · by_contra hne
    obtain ⟨p, pp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have h1 : (p : ℤ) ∣ γ :=
      natCast_dvd_int.mpr (hpdvd.trans (Nat.gcd_dvd_left _ _))
    have h2 : (p : ℤ) ∣ d₀ + (primeSel γ d₀ : ℤ) * (N : ℤ) :=
      natCast_dvd_int.mpr (hpdvd.trans (Nat.gcd_dvd_right _ _))
    by_cases hpd : (p : ℤ) ∣ d₀
    · have h3 : (p : ℤ) ∣ (primeSel γ d₀ : ℤ) * (N : ℤ) := by
        have := h2.sub hpd
        rwa [add_sub_cancel_left] at this
      have h3' : p ∣ primeSel γ d₀ * N := by
        have heq : (primeSel γ d₀ : ℤ) * (N : ℤ) = ((primeSel γ d₀ * N : ℕ) : ℤ) := by
          push_cast; ring
        rw [heq] at h3
        exact natCast_dvd_int.mp h3
      rcases (Nat.Prime.dvd_mul pp).mp h3' with h4 | h4
      · exact not_dvd_primeSel pp hpd h4
      · exact Hγ p pp h1 hpd (natCast_dvd_int.mpr h4)
    · have h3 : (p : ℤ) ∣ (primeSel γ d₀ : ℤ) :=
        natCast_dvd_int.mpr (dvd_primeSel hγ0 pp h1 hpd)
      refine hpd ?_
      have := h2.sub (h3.mul_right (N : ℤ))
      rwa [add_sub_cancel_right] at this
  · push_cast
    simp

private theorem exists_sl2_int_lift {N : ℕ} [NeZero N] {a b c d : ZMod N}
    (h : a * d - b * c = 1) :
    ∃ α β γ δ : ℤ, α * δ - β * γ = 1 ∧
      (α : ZMod N) = a ∧ (β : ZMod N) = b ∧ (γ : ZMod N) = c ∧ (δ : ZMod N) = d := by
  set a₀ : ℤ := ZMod.cast a with ha₀
  set b₀ : ℤ := ZMod.cast b with hb₀
  set c₀ : ℤ := ZMod.cast c with hc₀
  set d₀ : ℤ := ZMod.cast d with hd₀
  have hcasta : ((a₀ : ℤ) : ZMod N) = a := ZMod.intCast_zmod_cast a
  have hcastb : ((b₀ : ℤ) : ZMod N) = b := ZMod.intCast_zmod_cast b
  have hcastc : ((c₀ : ℤ) : ZMod N) = c := ZMod.intCast_zmod_cast c
  have hcastd : ((d₀ : ℤ) : ZMod N) = d := ZMod.intCast_zmod_cast d
  have hdvd : (N : ℤ) ∣ a₀ * d₀ - b₀ * c₀ - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hcasta, hcastb, hcastc, hcastd]
    rw [sub_eq_zero]
    exact h
  have H : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c₀ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ) := by
    intro p pp hpc hpd hpN
    have hone : (p : ℤ) ∣ 1 := by
      have h1 : (p : ℤ) ∣ a₀ * d₀ - b₀ * c₀ - 1 := hpN.trans hdvd
      have h2 : (p : ℤ) ∣ a₀ * d₀ := hpd.mul_left a₀
      have h3 : (p : ℤ) ∣ b₀ * c₀ := hpc.mul_left b₀
      have key : (1 : ℤ) = a₀ * d₀ - b₀ * c₀ - (a₀ * d₀ - b₀ * c₀ - 1) := by ring
      rw [key]
      exact (h2.sub h3).sub h1
    exact pp.one_lt.ne' (Nat.dvd_one.mp (by exact_mod_cast hone))
  obtain ⟨γ, δ, hγδ, hγ, hδ⟩ := exists_coprime_lift N H
  rw [hcastc] at hγ
  rw [hcastd] at hδ
  set α₀ : ℤ := Int.gcdB γ δ with hα₀
  set β₀ : ℤ := -Int.gcdA γ δ with hβ₀
  have hdet₀ : α₀ * δ - β₀ * γ = 1 := by
    have hbez := Int.gcd_eq_gcd_ab γ δ
    rw [hγδ] at hbez
    push_cast at hbez
    rw [hα₀, hβ₀]
    linear_combination -hbez
  have hdet₀' : (α₀ : ZMod N) * d - (β₀ : ZMod N) * c = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod N)) hdet₀
    push_cast at this
    rwa [hγ, hδ] at this
  set lam : ZMod N := b * (α₀ : ZMod N) - a * (β₀ : ZMod N) with hlam
  set l : ℤ := ZMod.cast lam with hl
  have hcastl : ((l : ℤ) : ZMod N) = lam := ZMod.intCast_zmod_cast lam
  refine ⟨α₀ + l * γ, β₀ + l * δ, γ, δ, ?_, ?_, ?_, hγ, hδ⟩
  · linear_combination hdet₀
  · push_cast
    rw [hcastl, hγ, hlam]
    linear_combination (-(α₀ : ZMod N)) * h + a * hdet₀'
  · push_cast
    rw [hcastl, hδ, hlam]
    linear_combination (-(β₀ : ZMod N)) * h + b * hdet₀'

private theorem surjective_specialLinearGroup_map_zmod (N : ℕ) [NeZero N] :
    Function.Surjective
      (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N))) := by
  intro M
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have hM := M.prop
    rwa [Matrix.det_fin_two] at hM
  obtain ⟨α, β, γ, δ, h1, ha, hb, hc, hd⟩ := exists_sl2_int_lift hdet
  refine ⟨⟨!![α, β; γ, δ], by rw [Matrix.det_fin_two_of]; exact h1⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simpa [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
      using ‹_›

end SurjectiveLift

section ClosureElemSet

private theorem closure_elemSet_eq_top (N : ℕ) [NeZero N] :
    Subgroup.closure (elemSet (ZMod N)) = ⊤ := by
  set φ : SL(2, ℤ) →* SL(2, ZMod N) :=
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) with hφ
  have hT : φ ModularGroup.T = upperElem (1 : ZMod N) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hφ, ModularGroup.coe_T]
  have hS : φ ModularGroup.S =
      upperElem (-1 : ZMod N) * lowerElem 1 * upperElem (-1) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hφ, ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two]
  have hsurj : Function.Surjective φ :=
    surjective_specialLinearGroup_map_zmod N
  rw [eq_top_iff, ← Subgroup.map_top_of_surjective φ hsurj,
    ← SpecialLinearGroup.SL2Z_generators, MonoidHom.map_closure]
  refine (closure_le _).mpr ?_
  rintro x ⟨y, hy, rfl⟩
  rcases hy with rfl | rfl
  · rw [hS]
    exact mul_mem (mul_mem (upperElem_mem_closure_elemSet _)
      (lowerElem_mem_closure_elemSet _)) (upperElem_mem_closure_elemSet _)
  · rw [hT]
    exact upperElem_mem_closure_elemSet (1 : ZMod N)

end ClosureElemSet

section Generation

variable {p : ℕ} [Fact p.Prime]

private lemma exists_natCast_mul_eq {a : ZMod p} (ha : a ≠ 0) (c : ZMod p) :
    ∃ n : ℕ, (n : ZMod p) * a = c := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective (c * a⁻¹)
  refine ⟨n, ?_⟩
  rw [hn, mul_assoc, ZMod.inv_mul_of_unit a (isUnit_iff_ne_zero.mpr ha), mul_one]

private lemma mem_range_toGL_of_det_eq_one {n : Type*} [DecidableEq n] [Fintype n] {R : Type*}
    [CommRing R] {g : GL n R} (hg : Matrix.det (g : Matrix n n R) = 1) :
    g ∈ (Matrix.SpecialLinearGroup.toGL (n := n) (R := R)).range :=
  ⟨⟨(g : Matrix n n R), hg⟩, Units.ext rfl⟩

private theorem range_toGL_le_of_conj_elem (H : Subgroup (GL (Fin 2) (ZMod p)))
    (P : GL (Fin 2) (ZMod p)) {a b : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0)
    (hu : P * Matrix.SpecialLinearGroup.toGL (upperElem a) * P⁻¹ ∈ H)
    (hl : P * Matrix.SpecialLinearGroup.toGL (lowerElem b) * P⁻¹ ∈ H) :
    (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := ZMod p)).range ≤ H := by

  set φ : SL(2, ZMod p) →* GL (Fin 2) (ZMod p) :=
    ((MulAut.conj P).toMonoidHom).comp (Matrix.SpecialLinearGroup.toGL) with hφdef
  have hφ : ∀ M : SL(2, ZMod p),
      φ M = P * Matrix.SpecialLinearGroup.toGL M * P⁻¹ := fun M => rfl

  have hupper : ∀ c : ZMod p, φ (upperElem c) ∈ H := by
    intro c
    obtain ⟨n, hn⟩ := exists_natCast_mul_eq ha c
    rw [show upperElem c = (upperElem a) ^ n by rw [upperElem_pow, hn], map_pow]
    exact pow_mem (by rw [hφ]; exact hu) n
  have hlower : ∀ c : ZMod p, φ (lowerElem c) ∈ H := by
    intro c
    obtain ⟨n, hn⟩ := exists_natCast_mul_eq hb c
    rw [show lowerElem c = (lowerElem b) ^ n by rw [lowerElem_pow, hn], map_pow]
    exact pow_mem (by rw [hφ]; exact hl) n

  have hrange : φ.range ≤ H := by
    rw [MonoidHom.range_eq_map, ← closure_elemSet_eq_top p, MonoidHom.map_closure,
      closure_le]
    rintro x ⟨y, hy, rfl⟩
    rcases hy with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact hupper c
    · exact hlower c

  intro g hg
  obtain ⟨M, rfl⟩ := MonoidHom.mem_range.mp hg
  have hdet : Matrix.det ((P⁻¹ * Matrix.SpecialLinearGroup.toGL M * P :
      GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) = 1 := by
    have h1 : ((P⁻¹ * Matrix.SpecialLinearGroup.toGL M * P : GL (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p)) =
        ((P⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *
          ((Matrix.SpecialLinearGroup.toGL M : GL (Fin 2) (ZMod p)) :
            Matrix (Fin 2) (Fin 2) (ZMod p)) *
          ((P : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
      rw [Units.val_mul, Units.val_mul]
    have h2 : Matrix.det ((P⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *
        Matrix.det ((P : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel P, Units.val_one,
        Matrix.det_one]
    have h3 : Matrix.det ((Matrix.SpecialLinearGroup.toGL M : GL (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p)) = 1 := M.2
    rw [h1, Matrix.det_mul, Matrix.det_mul, h3, mul_one, h2]
  obtain ⟨N, hN⟩ := mem_range_toGL_of_det_eq_one hdet
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

private lemma eq_one_of_fixes_two {M : Matrix (Fin 2) (Fin 2) F} {v w : Fin 2 → F}
    (hv : M.mulVec v = v) (hw : M.mulVec w = w) (hD : v 0 * w 1 - v 1 * w 0 ≠ 0) :
    M = 1 := by
  set D := v 0 * w 1 - v 1 * w 0 with hDdef

  have hcancel : ∀ x y : Fin 2 → F, D • x = D • y → x = y := by
    intro x y hxy
    funext i
    have hi := congrFun hxy i
    simp only [Pi.smul_apply, smul_eq_mul] at hi
    exact mul_left_cancel₀ hD hi

  have hfix : ∀ x y : F, M.mulVec (x • v + y • w) = x • v + y • w := by
    intro x y
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hv, hw]

  have he0 : (w 1 : F) • v + (-(v 1)) • w = D • ![1, 0] := by
    funext i
    fin_cases i <;> simp [hDdef] <;> try ring
  have he1 : (-(w 0) : F) • v + (v 0) • w = D • ![0, 1] := by
    funext i
    fin_cases i <;> simp [hDdef] <;> try ring
  have h0 : D • M.mulVec ![1, 0] = D • ![1, 0] := by
    rw [← Matrix.mulVec_smul, ← he0, hfix, he0]
  have h1 : D • M.mulVec ![0, 1] = D • ![0, 1] := by
    rw [← Matrix.mulVec_smul, ← he1, hfix, he1]
  have h0' := hcancel _ _ h0
  have h1' := hcancel _ _ h1
  rw [mulVec_e0] at h0'
  rw [mulVec_e1] at h1'
  have e00 : M 0 0 = 1 := congrFun h0' 0
  have e10 : M 1 0 = 0 := congrFun h0' 1
  have e01 : M 0 1 = 0 := congrFun h1' 0
  have e11 : M 1 1 = 1 := congrFun h1' 1
  rw [Matrix.eta_fin_two M, e00, e10, e01, e11, ← Matrix.one_fin_two]

private lemma exists_smul_eq_of_cross_eq_zero {v w : Fin 2 → F} (hv : v ≠ 0)
    (hD : v 0 * w 1 - v 1 * w 0 = 0) : ∃ c : F, w = c • v := by
  have hkey : v 0 * w 1 = v 1 * w 0 := sub_eq_zero.mp hD
  have hv' : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra hc
    simp only [not_or, not_not] at hc
    exact hv (funext_fin_two hc.1 hc.2)
  rcases eq_or_ne (v 0) 0 with h0 | h0
  ·
    have hv1 : v 1 ≠ 0 := by
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
    · show w 0 = w 1 / v 1 * v 0
      rw [hw0, h0, mul_zero]
    · show w 1 = w 1 / v 1 * v 1
      rw [div_mul_cancel₀ _ hv1]
  ·
    refine ⟨w 0 / v 0, funext_fin_two ?_ ?_⟩
    · show w 0 = w 0 / v 0 * v 0
      rw [div_mul_cancel₀ _ h0]
    · show w 1 = w 0 / v 0 * v 1
      rw [div_mul_eq_mul_div, eq_div_iff h0]
      linear_combination hkey

private lemma eq_upperElem_of_fixes_e0 {Q : Matrix (Fin 2) (Fin 2) F} (hQ : (Q - 1) ^ 2 = 0)
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

private lemma eq_lowerElem_of_fixes_e1 {Q : Matrix (Fin 2) (Fin 2) F} (hQ : (Q - 1) ^ 2 = 0)
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
  have hinv : (h : 𝕄) * ((h⁻¹ : GL (Fin 2) (ZMod p)) : 𝕄) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel h, Units.val_one]
  have hinv' : ((h⁻¹ : GL (Fin 2) (ZMod p)) : 𝕄) * (h : 𝕄) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel h, Units.val_one]
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

/-- An irreducible subgroup of `GL(2, ZMod p)` containing a nontrivial
square-zero unipotent contains the image of `SL(2, ZMod p)`. -/
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
  have hinvh : ((h⁻¹ : GL (Fin 2) (ZMod p)) : 𝕄) * (h : 𝕄) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel h, Units.val_one]
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
  have hPinv : ((P⁻¹ : GL (Fin 2) (ZMod p)) : 𝕄) * (P : 𝕄) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel P, Units.val_one]
  have hPinv' : (P : 𝕄) * ((P⁻¹ : GL (Fin 2) (ZMod p)) : 𝕄) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel P, Units.val_one]

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
    eq_upperElem_of_fixes_e0 hQ2 hQfix

  have hQ'2 : (((P⁻¹ * (h * u * h⁻¹) * P : GL (Fin 2) (ZMod p)) : 𝕄) - 1) ^ 2 = 0 := by
    have hc := conj_unipotent (g := h * u * h⁻¹) P⁻¹ hu'2
    rwa [inv_inv] at hc
  have hQ'fix : ((P⁻¹ * (h * u * h⁻¹) * P : GL (Fin 2) (ZMod p)) : 𝕄).mulVec ![0, 1] =
      ![0, 1] := by
    have hc := hconjfix (h * u * h⁻¹) w hw
    rwa [hPiw] at hc
  have hQ'form : ((P⁻¹ * (h * u * h⁻¹) * P : GL (Fin 2) (ZMod p)) : 𝕄) =
      !![1, 0; ((P⁻¹ * (h * u * h⁻¹) * P : GL (Fin 2) (ZMod p)) : 𝕄) 1 0, 1] :=
    eq_lowerElem_of_fixes_e1 hQ'2 hQ'fix

  have hQeq : P⁻¹ * u * P = Matrix.SpecialLinearGroup.toGL
      (upperElem (((P⁻¹ * u * P : GL (Fin 2) (ZMod p)) : 𝕄) 0 1)) := by
    apply Units.ext
    exact hQform
  have hQ'eq : P⁻¹ * (h * u * h⁻¹) * P = Matrix.SpecialLinearGroup.toGL
      (lowerElem (((P⁻¹ * (h * u * h⁻¹) * P : GL (Fin 2) (ZMod p)) : 𝕄) 1 0)) := by
    apply Units.ext
    exact hQ'form

  have ha : ((P⁻¹ * u * P : GL (Fin 2) (ZMod p)) : 𝕄) 0 1 ≠ 0 := by
    intro ha0
    apply hu1
    have h1 : P⁻¹ * u * P = 1 := by
      rw [hQeq, ha0, upperElem_zero]
      exact map_one _
    calc u = P * (P⁻¹ * u * P) * P⁻¹ := by group
    _ = P * 1 * P⁻¹ := by rw [h1]
    _ = 1 := by group
  have hb : ((P⁻¹ * (h * u * h⁻¹) * P : GL (Fin 2) (ZMod p)) : 𝕄) 1 0 ≠ 0 := by
    intro hb0
    have hu'1 : h * u * h⁻¹ = 1 := by
      have h1 : P⁻¹ * (h * u * h⁻¹) * P = 1 := by
        rw [hQ'eq, hb0, lowerElem_zero]
        exact map_one _
      calc h * u * h⁻¹ = P * (P⁻¹ * (h * u * h⁻¹) * P) * P⁻¹ := by group
      _ = P * 1 * P⁻¹ := by rw [h1]
      _ = 1 := by group
    apply hu1
    calc u = h⁻¹ * (h * u * h⁻¹) * h := by group
    _ = h⁻¹ * 1 * h := by rw [hu'1]
    _ = 1 := by group

  refine range_toGL_le_of_conj_elem H P ha hb ?_ ?_
  · rw [← hQeq]
    have hPQ : P * (P⁻¹ * u * P) * P⁻¹ = u := by group
    rw [hPQ]
    exact huH
  · rw [← hQ'eq]
    have hPQ : P * (P⁻¹ * (h * u * h⁻¹) * P) * P⁻¹ = h * u * h⁻¹ := by group
    rw [hPQ]
    exact hu'H


end SL2
