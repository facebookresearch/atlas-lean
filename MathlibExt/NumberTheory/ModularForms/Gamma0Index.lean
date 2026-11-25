/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_ModularCurve_ProjectiveLine.lean`,
`Theorems/Thm_ModularCurve_Gamma0_index.lean`,
`Theorems/Thm_ModularCurve_card_quotient_gamma0_eq_index.lean`,
`Theorems/Thm_ModularCurve_card_projectiveLine_zmod.lean`,
`P2M/Sol/S_ModularCurve_Gamma0_index.lean`,
`P2M/Sol/S_ModularCurve_card_quotient_gamma0_eq_index.lean` and
`P2M/Sol/S_ModularCurve_card_projectiveLine_zmod.lean`
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
framework; the statements and arguments are reused here with that machinery
removed, the names restated in Mathlib style, and the proofs rewritten to use
Mathlib APIs directly. The Dedekind psi value is the arithmetic function
`ArithmeticFunction.dedekindPsi` already in this repository.
-/

module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.GroupTheory.Index
public import MathlibExt.NumberTheory.ArithmeticFunction.DedekindPsi

import MathlibExt.GroupTheory.CyclicSubgroupsZModSquare
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Index of the congruence subgroup Gamma0

The index of `Gamma0 N` in `SL(2, Z)` is the Dedekind psi value `psi(N)`.
The proof identifies the quotient by the Borel subgroup of upper-triangular
matrices with the projective line `ProjectiveLine (ZMod N)`, whose points are
counted by `card_projectiveLine_zmod`, and lifts surjectivity of reduction
modulo `N` from `Z` to `ZMod N`.
-/

@[expose] public section

namespace ModularCurve

open Matrix CongruenceSubgroup
open scoped MatrixGroups

section Borel

variable {R : Type*} [CommRing R]

def borel (R : Type*) [CommRing R] : Subgroup (SpecialLinearGroup (Fin 2) R) where
  carrier := { M | M.1 1 0 = 0 }
  one_mem' := by simp
  mul_mem' := by
    intro A B hA hB
    change (A * B).1 1 0 = 0
    rw [SpecialLinearGroup.coe_mul, (Matrix.two_mul_expl A.1 B.1).2.2.1, hA, hB]
    ring
  inv_mem' := by
    intro A hA
    change (A⁻¹).1 1 0 = 0
    have h : (A⁻¹).1 = !![A.1 1 1, -A.1 0 1; -A.1 1 0, A.1 0 0] :=
      congrArg Subtype.val (SpecialLinearGroup.SL2_inv_expl A)
    rw [h]
    exact neg_eq_zero.mpr hA

theorem mem_borel_iff {A : SpecialLinearGroup (Fin 2) R} : A ∈ borel R ↔ A.1 1 0 = 0 :=
  Iff.rfl

end Borel

section ArithmeticLemmas

private lemma natCast_dvd_int {p : ℕ} {z : ℤ} : (p : ℤ) ∣ z ↔ p ∣ z.natAbs :=
  Int.natCast_dvd

private def primeSel (c d : ℤ) : ℕ :=
  ∏ p ∈ c.natAbs.primeFactors, if p ∣ d.natAbs then 1 else p

private lemma dvd_primeSel {c d : ℤ} {p : ℕ} (hc : c ≠ 0) (hp : p.Prime)
    (hpc : (p : ℤ) ∣ c) (hpd : ¬(p : ℤ) ∣ d) : p ∣ primeSel c d := by
  have hmem : p ∈ c.natAbs.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, natCast_dvd_int.mp hpc, Int.natAbs_ne_zero.mpr hc⟩
  have h := Finset.dvd_prod_of_mem (fun q : ℕ => if q ∣ d.natAbs then 1 else q) hmem
  simp only [ite_eq_right (fun hcontra => hpd (natCast_dvd_int.mpr hcontra))] at h
  exact h

private lemma not_dvd_primeSel {c d : ℤ} {p : ℕ} (hp : p.Prime) (hpd : (p : ℤ) ∣ d) :
    ¬p ∣ primeSel c d := by
  intro hdvd
  obtain ⟨q, hq, hpq⟩ := (Nat.Prime.prime hp).dvd_finsetProd_iff _ |>.mp hdvd
  by_cases hqd : q ∣ d.natAbs
  · rw [ite_eq_left hqd] at hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpq)
  · rw [ite_eq_right hqd] at hpq
    have hq' : q.Prime := (Nat.mem_primeFactors.mp hq).1
    exact hqd (((Nat.prime_dvd_prime_iff_eq hp hq').mp hpq) ▸ natCast_dvd_int.mp hpd)

private theorem exists_coprime_lift (N : ℕ) [NeZero N] {c₀ d₀ : ℤ}
    (H : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c₀ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ)) :
    ∃ γ δ : ℤ, Int.gcd γ δ = 1 ∧
      (γ : ZMod N) = (c₀ : ZMod N) ∧ (δ : ZMod N) = (d₀ : ZMod N) := by
  set γ : ℤ := if c₀ = 0 then (N : ℤ) else c₀ with hγ_def
  have hγ0 : γ ≠ 0 := by
    rw [hγ_def]; split
    · exact_mod_cast NeZero.ne N
    · assumption
  have hγc : (γ : ZMod N) = (c₀ : ZMod N) := by
    rw [hγ_def]; split
    · next h => simp [h]
    · rfl
  have Hγ : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ γ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ) := by
    intro p pp hpγ hpd
    refine H p pp ?_ hpd
    rw [hγ_def] at hpγ
    by_cases h : c₀ = 0
    · simp [h]
    · rwa [ite_eq_right h] at hpγ
  refine ⟨γ, d₀ + (primeSel γ d₀ : ℤ) * (N : ℤ), ?_, hγc, ?_⟩
  · by_contra hne
    obtain ⟨p, pp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have h1 : (p : ℤ) ∣ γ :=
      natCast_dvd_int.mpr (hpdvd.trans (Nat.gcd_dvd_left _ _))
    have h2 : (p : ℤ) ∣ d₀ + (primeSel γ d₀ : ℤ) * (N : ℤ) :=
      natCast_dvd_int.mpr (hpdvd.trans (Nat.gcd_dvd_right _ _))
    by_cases hpd : (p : ℤ) ∣ d₀
    · have h3 : (p : ℤ) ∣ (primeSel γ d₀ : ℤ) * (N : ℤ) := by
        have := h2.sub hpd; rwa [add_sub_cancel_left] at this
      have h3' : p ∣ primeSel γ d₀ * N := by
        have : (p : ℤ) ∣ ((primeSel γ d₀ * N : ℕ) : ℤ) := by push_cast; exact h3
        exact_mod_cast this
      rcases (pp.prime.dvd_mul.mp h3') with h4 | h4
      · exact not_dvd_primeSel pp hpd h4
      · exact Hγ p pp h1 hpd (by exact_mod_cast h4)
    · have h3 : (p : ℤ) ∣ (primeSel γ d₀ : ℤ) :=
        natCast_dvd_int.mpr (dvd_primeSel hγ0 pp h1 hpd)
      refine hpd ?_
      have := h2.sub (h3.mul_right (N : ℤ)); rwa [add_sub_cancel_right] at this
  · push_cast; simp

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
    rw [sub_eq_zero]; exact h
  have H : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c₀ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ) := by
    intro p pp hpc hpd hpN
    have hone : (p : ℤ) ∣ 1 := by
      have h1 : (p : ℤ) ∣ a₀ * d₀ - b₀ * c₀ - 1 := hpN.trans hdvd
      have h2 : (p : ℤ) ∣ a₀ * d₀ := hpd.mul_left a₀
      have h3 : (p : ℤ) ∣ b₀ * c₀ := hpc.mul_left b₀
      have key : (1 : ℤ) = a₀ * d₀ - b₀ * c₀ - (a₀ * d₀ - b₀ * c₀ - 1) := by ring
      rw [key]; exact (h2.sub h3).sub h1
    exact pp.one_lt.ne' (Nat.dvd_one.mp (by exact_mod_cast hone))
  obtain ⟨γ, δ, hγδ, hγ, hδ⟩ := exists_coprime_lift N H
  rw [hcastc] at hγ; rw [hcastd] at hδ
  set α₀ : ℤ := Int.gcdB γ δ with hα₀
  set β₀ : ℤ := -Int.gcdA γ δ with hβ₀
  have hdet₀ : α₀ * δ - β₀ * γ = 1 := by
    have hbez := Int.gcd_eq_gcd_ab γ δ
    rw [hγδ] at hbez; push_cast at hbez
    rw [hα₀, hβ₀]; linear_combination -hbez
  have hdet₀' : (α₀ : ZMod N) * d - (β₀ : ZMod N) * c = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod N)) hdet₀
    push_cast at this; rwa [hγ, hδ] at this
  set lam : ZMod N := b * (α₀ : ZMod N) - a * (β₀ : ZMod N) with hlam
  set l : ℤ := ZMod.cast lam with hl
  have hcastl : ((l : ℤ) : ZMod N) = lam := ZMod.intCast_zmod_cast lam
  refine ⟨α₀ + l * γ, β₀ + l * δ, γ, δ, ?_, ?_, ?_, hγ, hδ⟩
  · linear_combination hdet₀
  · push_cast; rw [hcastl, hγ, hlam]
    linear_combination (-(α₀ : ZMod N)) * h + a * hdet₀'
  · push_cast; rw [hcastl, hδ, hlam]
    linear_combination (-(β₀ : ZMod N)) * h + b * hdet₀'

end ArithmeticLemmas

private theorem sl2_surj (N : ℕ) [NeZero N] :
    Function.Surjective
      (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N))) := by
  intro M
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have hM := M.prop; rwa [Matrix.det_fin_two] at hM
  obtain ⟨α, β, γ, δ, h1, ha, hb, hc, hd⟩ := exists_sl2_int_lift hdet
  refine ⟨⟨!![α, β; γ, δ], by rw [Matrix.det_fin_two_of]; exact h1⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simpa [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
      using ‹_›

section QuotientBorel
variable {R : Type*} [CommRing R]

private theorem isUnimodularRow_firstCol (A : SpecialLinearGroup (Fin 2) R) :
    IsUnimodularRow (A.1 0 0) (A.1 1 0) := by
  refine ⟨A.1 1 1, -A.1 0 1, ?_⟩
  have hdet : A.1 0 0 * A.1 1 1 - A.1 0 1 * A.1 1 0 = 1 := by
    have h := A.2; rwa [Matrix.det_fin_two] at h
  linear_combination hdet

private def firstColumnClass (A : SpecialLinearGroup (Fin 2) R) : ProjectiveLine R :=
  ⟦⟨(A.1 0 0, A.1 1 0), isUnimodularRow_firstCol A⟩⟧

private theorem firstColumnClass_eq_iff (A B : SpecialLinearGroup (Fin 2) R) :
    firstColumnClass A = firstColumnClass B ↔ A⁻¹ * B ∈ borel R := by
  constructor
  · intro hAB
    obtain ⟨u, h1, h2⟩ := Quotient.exact hAB
    have h1' : (u : R) * A.1 0 0 = B.1 0 0 := h1
    have h2' : (u : R) * A.1 1 0 = B.1 1 0 := h2
    change (A⁻¹ * B).1 1 0 = 0
    have hinv : (A⁻¹).1 = !![A.1 1 1, -A.1 0 1; -A.1 1 0, A.1 0 0] :=
      congrArg Subtype.val (SpecialLinearGroup.SL2_inv_expl A)
    have e10 : (A⁻¹).1 1 0 = -A.1 1 0 := by simp [hinv]
    have e11 : (A⁻¹).1 1 1 = A.1 0 0 := by simp [hinv]
    have hentry : (A⁻¹ * B).1 1 0 = -A.1 1 0 * B.1 0 0 + A.1 0 0 * B.1 1 0 := by
      rw [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, e10, e11]
    rw [hentry, ← h1', ← h2']; ring
  · intro hAB
    have hB : B = A * (A⁻¹ * B) := (mul_inv_cancel_left A B).symm
    have hC10 : (A⁻¹ * B).1 1 0 = 0 := hAB
    have hCdet : (A⁻¹ * B).1 0 0 * (A⁻¹ * B).1 1 1 = 1 := by
      have h := (A⁻¹ * B).2; rw [Matrix.det_fin_two, hC10] at h; linear_combination h
    have hB00 : B.1 0 0 = A.1 0 0 * (A⁻¹ * B).1 0 0 + A.1 0 1 * (A⁻¹ * B).1 1 0 := by
      conv_lhs => rw [hB, SpecialLinearGroup.coe_mul]
      exact (Matrix.two_mul_expl A.1 (A⁻¹ * B).1).1
    have hB10 : B.1 1 0 = A.1 1 0 * (A⁻¹ * B).1 0 0 + A.1 1 1 * (A⁻¹ * B).1 1 0 := by
      conv_lhs => rw [hB, SpecialLinearGroup.coe_mul]
      exact (Matrix.two_mul_expl A.1 (A⁻¹ * B).1).2.2.1
    refine Quotient.sound ⟨⟨(A⁻¹ * B).1 0 0, (A⁻¹ * B).1 1 1, hCdet,
      (mul_comm _ _).trans hCdet⟩, ?_, ?_⟩
    · change (A⁻¹ * B).1 0 0 * A.1 0 0 = B.1 0 0; rw [hB00, hC10]; ring
    · change (A⁻¹ * B).1 0 0 * A.1 1 0 = B.1 1 0; rw [hB10, hC10]; ring

private theorem card_quotient_borel (R : Type*) [CommRing R] :
    Nat.card (SpecialLinearGroup (Fin 2) R ⧸ borel R) = Nat.card (ProjectiveLine R) := by
  have hwd : ∀ A B : SpecialLinearGroup (Fin 2) R, QuotientGroup.leftRel (borel R) A B →
      firstColumnClass A = firstColumnClass B := by
    intro A B hAB
    rw [QuotientGroup.leftRel_apply] at hAB
    exact (firstColumnClass_eq_iff A B).mpr hAB
  refine Nat.card_eq_of_bijective (fun q => Quotient.liftOn' q firstColumnClass hwd) ⟨?_, ?_⟩
  · intro q q'
    refine Quotient.inductionOn₂' q q' ?_
    intro A B hAB
    have hAB' : firstColumnClass A = firstColumnClass B := hAB
    exact (QuotientGroup.eq).mpr ((firstColumnClass_eq_iff A B).mp hAB')
  · intro q
    obtain ⟨v, rfl⟩ := Quotient.exists_rep q
    obtain ⟨x, y, hxy⟩ := v.2
    refine ⟨QuotientGroup.mk ⟨!![v.1.1, -y; v.1.2, x], by
      rw [Matrix.det_fin_two_of]; linear_combination hxy⟩, ?_⟩
    change firstColumnClass _ = ⟦v⟧
    refine Quotient.sound ⟨1, ?_, ?_⟩
    · change (1 : R) * !![v.1.1, -y; v.1.2, x] 0 0 = v.1.1; simp
    · change (1 : R) * !![v.1.1, -y; v.1.2, x] 1 0 = v.1.2; simp

end QuotientBorel

private theorem Gamma0_eq_comap_borel (N : ℕ) :
    Gamma0 N = (borel (ZMod N)).comap
      (SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N))) := by
  ext A
  rw [Gamma0_mem, Subgroup.mem_comap, mem_borel_iff]
  constructor
  · intro hA
    change (Int.castRingHom (ZMod N)).mapMatrix A.1 1 0 = 0; simpa using hA
  · intro hA
    have hA' : (Int.castRingHom (ZMod N)).mapMatrix A.1 1 0 = 0 := hA; simpa using hA'



/-- The index of `Gamma0 N` in `SL(2, Z)` equals the Dedekind psi value. -/
theorem Gamma0_index (N : ℕ) [NeZero N] :
    (CongruenceSubgroup.Gamma0 N).index = ArithmeticFunction.dedekindPsi N := by
  have h1 : (CongruenceSubgroup.Gamma0 N).index = (borel (ZMod N)).index := by
    rw [Gamma0_eq_comap_borel]
    exact Subgroup.index_comap_of_surjective _ (sl2_surj N)
  rw [h1, Subgroup.index_eq_card, card_quotient_borel,
    card_projectiveLine_zmod N (NeZero.ne N)]

end ModularCurve

open scoped MatrixGroups in
/-- The cardinality of the quotient of the modular group by the image of
`Gamma0 N` equals the index of `Gamma0 N`. -/
theorem ModularCurve.card_quotient_gamma0_eq_index (N : ℕ) :
    Nat.card (𝒮ℒ ⧸ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
      (CongruenceSubgroup.Gamma0 N)).subgroupOf 𝒮ℒ) =
      (CongruenceSubgroup.Gamma0 N).index := by
  rw [← Subgroup.index_eq_card]
  change Subgroup.relIndex _ _ = _
  rw [MonoidHom.range_eq_map,
    Subgroup.relIndex_map_map_of_injective _ _
      Matrix.SpecialLinearGroup.mapGL_injective,
    Subgroup.relIndex_top_right]
