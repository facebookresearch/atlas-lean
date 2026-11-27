/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

private lemma trisect_monic : (Polynomial.X ^ 3 - Polynomial.C (3 / 4 : ℚ) * Polynomial.X
    - Polynomial.C (1 / 8 : ℚ)).Monic := by
  rw [sub_sub]
  apply Polynomial.monic_X_pow_sub
  compute_degree
  decide

private lemma trisect_natDegree : (Polynomial.X ^ 3 - Polynomial.C (3 / 4 : ℚ) * Polynomial.X
    - Polynomial.C (1 / 8 : ℚ)).natDegree = 3 := by
  compute_degree <;> norm_num

private lemma trisect_noRoot : ∀ x : ℚ, ¬ (Polynomial.X ^ 3 - Polynomial.C (3 / 4 : ℚ) *
    Polynomial.X - Polynomial.C (1 / 8 : ℚ)).IsRoot x := by
  intro x hx
  have heval0 : (Polynomial.X ^ 3 - Polynomial.C (3 / 4 : ℚ) * Polynomial.X
      - Polynomial.C (1 / 8 : ℚ)).eval x = 0 := hx
  have heval : x ^ 3 - 3 / 4 * x - 1 / 8 = (0 : ℚ) := by
    simpa only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C] using heval0
  have h8x : 8 * x ^ 3 - 6 * x - 1 = (0 : ℚ) := by linear_combination 8 * heval
  rw [← Rat.num_div_den x] at h8x
  have hdn0 : ((x.den : ℚ)) ≠ 0 := by exact_mod_cast Rat.den_nz x
  field_simp at h8x
  have key : 8 * (x.num : ℚ) ^ 3 - 6 * (x.num : ℚ) * (x.den : ℚ) ^ 2
      - (x.den : ℚ) ^ 3 = 0 := by
    linear_combination h8x
  have hint : 8 * x.num ^ 3 - 6 * x.num * (x.den : ℤ) ^ 2 - (x.den : ℤ) ^ 3 = 0 := by
    have hcast : ((8 * x.num ^ 3 - 6 * x.num * (x.den : ℤ) ^ 2
        - (x.den : ℤ) ^ 3 : ℤ) : ℚ) = 0 := by
      push_cast
      linear_combination key
    exact_mod_cast hcast
  have hden8 : x.den ∣ 8 * x.num.natAbs ^ 3 := by
    have h1 : (x.den : ℤ) ∣ 8 * x.num ^ 3 :=
      ⟨6 * x.num * (x.den : ℤ) + (x.den : ℤ) ^ 2, by linear_combination hint⟩
    have h2 : ((x.den : ℤ)).natAbs ∣ (8 * x.num ^ 3).natAbs :=
      Int.natAbs_dvd_natAbs.mpr h1
    rwa [Int.natAbs_mul, Int.natAbs_pow] at h2
  have hnum1 : x.num.natAbs ∣ 1 := by
    have h1 : (x.num : ℤ) ∣ ((x.den : ℤ)) ^ 3 :=
      ⟨8 * x.num ^ 2 - 6 * (x.den : ℤ) ^ 2, by linear_combination -hint⟩
    have h2 : x.num.natAbs ∣ (((x.den : ℤ)) ^ 3).natAbs :=
      Int.natAbs_dvd_natAbs.mpr h1
    rw [Int.natAbs_pow] at h2
    have hdd : (((x.den : ℤ))).natAbs = x.den := rfl
    rw [hdd] at h2
    have hc : Nat.Coprime x.num.natAbs x.den := Rat.reduced x
    have e1 : x.num.natAbs ∣ x.den ^ 2 := by
      have h : x.num.natAbs ∣ x.den ^ 2 * x.den := by rwa [← pow_succ]
      exact Nat.Coprime.dvd_of_dvd_mul_right hc h
    have e2 : x.num.natAbs ∣ x.den := by
      have h : x.num.natAbs ∣ x.den * x.den := by rwa [← pow_two]
      exact Nat.Coprime.dvd_of_dvd_mul_right hc h
    have h : x.num.natAbs ∣ 1 * x.den := by rwa [one_mul]
    exact Nat.Coprime.dvd_of_dvd_mul_right hc h
  have hna1 : x.num.natAbs = 1 := Nat.dvd_one.mp hnum1
  have hden8' : x.den ∣ 8 := by simpa [hna1] using hden8
  have hnum_pm : x.num = 1 ∨ x.num = -1 := by
    have h := Int.natAbs_eq_iff.mp hna1
    simpa using h
  have hden478 : x.den = 1 ∨ x.den = 2 ∨ x.den = 4 ∨ x.den = 8 := by
    have hmem : x.den ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hden8', by norm_num⟩
    have hdiv : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [hdiv] at hmem
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  rcases hnum_pm with h1 | h1 <;> rcases hden478 with h2 | h2 | h2 | h2 <;>
    rw [← Rat.num_div_den x, h1, h2] at heval <;> norm_num at heval

private lemma trisect_roots : (Polynomial.X ^ 3 - Polynomial.C (3 / 4 : ℚ) * Polynomial.X
    - Polynomial.C (1 / 8 : ℚ)).roots = 0 := by
  by_contra hne
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
  rw [Polynomial.mem_roots trisect_monic.ne_zero] at hx
  exact trisect_noRoot x hx

private lemma trisect_q_irreducible : Irreducible (Polynomial.X ^ 3
    - Polynomial.C (3 / 4 : ℚ) * Polynomial.X - Polynomial.C (1 / 8 : ℚ)) := by
  apply (Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three
    trisect_monic _ _).mpr trisect_roots
  · rw [trisect_natDegree]; norm_num
  · rw [trisect_natDegree]

private lemma trisect_eq : (8 * (Polynomial.X : Polynomial ℚ) ^ 3 -
    6 * (Polynomial.X : Polynomial ℚ) - 1)
    = Polynomial.C 8 * (Polynomial.X ^ 3 - Polynomial.C (3 / 4 : ℚ) *
      Polynomial.X - Polynomial.C (1 / 8 : ℚ)) := by
  simp only [mul_sub, ← mul_assoc, ← map_mul, ← Polynomial.C_ofNat]
  norm_num

private lemma trisect_assoc : Associated (8 * (Polynomial.X : Polynomial ℚ) ^ 3 -
    6 * (Polynomial.X : Polynomial ℚ) - 1)
    (Polynomial.X ^ 3 - Polynomial.C (3 / 4 : ℚ) * Polynomial.X
      - Polynomial.C (1 / 8 : ℚ)) := by
  have h8u : IsUnit (Polynomial.C (8 : ℚ) : Polynomial ℚ) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by norm_num))
  rw [trisect_eq, mul_comm]
  exact associated_mul_unit_left _ _ h8u

private lemma trisect_irreducible : Irreducible (8 * (Polynomial.X : Polynomial ℚ) ^ 3 -
    6 * (Polynomial.X : Polynomial ℚ) - 1) :=
  trisect_assoc.symm.irreducible trisect_q_irreducible

private lemma trisect_root : Polynomial.aeval (Real.cos (Real.pi / 9))
    (8 * (Polynomial.X : Polynomial ℚ) ^ 3 -
      6 * (Polynomial.X : Polynomial ℚ) - 1) = 0 := by
  have htri : Real.cos (3 * (Real.pi / 9))
      = 4 * (Real.cos (Real.pi / 9)) ^ 3 - 3 * Real.cos (Real.pi / 9) :=
    Real.cos_three_mul _
  have hpi : 3 * (Real.pi / 9) = Real.pi / 3 := by ring
  rw [hpi, Real.cos_pi_div_three] at htri
  have hae : Polynomial.aeval (Real.cos (Real.pi / 9))
      (8 * (Polynomial.X : Polynomial ℚ) ^ 3 -
        6 * (Polynomial.X : Polynomial ℚ) - 1)
      = 8 * (Real.cos (Real.pi / 9)) ^ 3 - 6 * Real.cos (Real.pi / 9) - 1 := by
    simp only [map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_one,
      map_ofNat]
  rw [hae]
  linarith

private lemma tower_mul (E F : IntermediateField ℚ ℝ) [Algebra ↥E ↥F]
    [IsScalarTower ℚ ↥E ↥F] :
    Module.finrank ℚ ↥E * Module.finrank ↥E ↥F = Module.finrank ℚ ↥F := by
  have := Module.Free.of_divisionRing ℚ ↥E
  have := Module.Free.of_divisionRing ↥E ↥F
  exact Module.finrank_mul_finrank ℚ ↥E ↥F

private lemma step_dvd (E F : IntermediateField ℚ ℝ) [Algebra ↥E ↥F]
    (b : ℝ) (hb : b ∈ F)
    (hval : ∀ a : ↥E, ((algebraMap ↥E ↥F a : ↥F) : ℝ) = (a : ℝ))
    (hspan : ∀ y : ℝ, y ∈ F → ∃ u v : ℝ, u ∈ E ∧ v ∈ E ∧ y = u + b * v) :
    Module.finrank ↥E ↥F ∣ 2 := by
  let φ : ↥E × ↥E →ₗ[↥E] ↥F :=
    { toFun := fun p => algebraMap ↥E ↥F p.1
          + ⟨b, hb⟩ * algebraMap ↥E ↥F p.2
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, map_add]
        ring
      map_smul' := fun r p => by
        simp only [Prod.smul_fst, Prod.smul_snd]
        simp only [Algebra.smul_def, map_mul,
          Algebra.algebraMap_self, RingHom.id_apply]
        ring }
  have hsurj : Function.Surjective φ := by
    intro w
    obtain ⟨u, v, hu, hv, heq⟩ := hspan (w : ℝ) w.2
    refine ⟨(⟨u, hu⟩, ⟨v, hv⟩), ?_⟩
    have hφ : φ (⟨u, hu⟩, ⟨v, hv⟩)
        = algebraMap ↥E ↥F ⟨u, hu⟩ + ⟨b, hb⟩ * algebraMap ↥E ↥F ⟨v, hv⟩ := rfl
    apply Subtype.ext
    rw [hφ, IntermediateField.coe_add F, IntermediateField.coe_mul F, hval, hval]
    exact heq.symm
  have := Module.Free.of_divisionRing ↥E ↥E
  have hfin : Module.Finite ↥E (↥E × ↥E) := inferInstance
  have hle2 : Module.finrank ↥E ↥F ≤ 2 := by
    have h := LinearMap.finrank_le_finrank_of_surjective hsurj
    rw [Module.finrank_prod, Module.finrank_self] at h
    omega
  have := Module.Finite.of_surjective φ hsurj
  have hpos : 0 < Module.finrank ↥E ↥F := Module.finrank_pos
  have h12 : Module.finrank ↥E ↥F = 1 ∨ Module.finrank ↥E ↥F = 2 := by omega
  rcases h12 with h1 | h1 <;> rw [h1]
  norm_num

private lemma tower_two_pow (n : ℕ) (F : Fin (n + 1) → IntermediateField ℚ ℝ)
    (hF0 : F 0 = ⊥)
    (hstep : ∀ i : Fin n, F i.castSucc ≤ F i.succ ∧
      ∃ b : ℝ, b ∈ F i.succ ∧ b ^ 2 ∈ F i.castSucc ∧
        ∀ y : ℝ, y ∈ F i.succ →
          ∃ u v : ℝ, u ∈ F i.castSucc ∧ v ∈ F i.castSucc ∧ y = u + b * v) :
    Module.finrank ℚ ↥(F (Fin.last n)) ∣ 2 ^ n := by
  have motive : ∀ i : Fin (n + 1), Module.finrank ℚ ↥(F i) ∣ 2 ^ i.val := by
    intro i
    induction i using Fin.induction with
    | zero =>
      refine ⟨1, ?_⟩
      have hv0 : (0 : Fin (n + 1)).val = 0 := rfl
      rw [hv0, hF0, pow_zero, mul_one]
      exact IntermediateField.finrank_bot.symm
    | succ j ih =>
      obtain ⟨hle, b, hb, hb2, hspan⟩ := hstep j
      let : Algebra ↥(F j.castSucc) ↥(F j.succ) :=
        RingHom.toAlgebra (IntermediateField.inclusion hle).toRingHom
      have hval : ∀ a : ↥(F j.castSucc),
          ((algebraMap ↥(F j.castSucc) ↥(F j.succ) a : ↥(F j.succ)) : ℝ)
          = (a : ℝ) := by
        intro a
        exact IntermediateField.coe_inclusion hle a
      have hcompat : ∀ x : ℚ, algebraMap ↥(F j.castSucc) ↥(F j.succ)
          (algebraMap ℚ ↥(F j.castSucc) x) = algebraMap ℚ ↥(F j.succ) x := by
        intro x
        apply Subtype.val_injective
        rw [hval]
        simp
      have htower : IsScalarTower ℚ ↥(F j.castSucc) ↥(F j.succ) := by
        constructor
        intro x y z
        simp only [Algebra.smul_def]
        rw [map_mul, hcompat]
        ring
      have := htower
      have hdvd : Module.finrank ↥(F j.castSucc) ↥(F j.succ) ∣ 2 :=
        step_dvd _ _ b hb hval hspan
      have hmul : Module.finrank ℚ ↥(F j.succ)
          = Module.finrank ℚ ↥(F j.castSucc)
            * Module.finrank ↥(F j.castSucc) ↥(F j.succ) :=
        (tower_mul _ _).symm
      have hcs : j.castSucc.val = j.val := rfl
      have hsc : (j.succ).val = j.val + 1 := rfl
      rw [hmul, hsc, pow_succ]
      rw [hcs] at ih
      exact mul_dvd_mul ih hdvd
  exact motive (Fin.last n)

private lemma toIF_le : ∀ {S T : Subfield ℝ} {hS : ∀ x : ℚ, algebraMap ℚ ℝ x ∈ S}
    {hT : ∀ x : ℚ, algebraMap ℚ ℝ x ∈ T},
    S ≤ T → Subfield.toIntermediateField S hS
      ≤ Subfield.toIntermediateField T hT := by
  intro S T hS hT h
  exact SetLike.coe_subset_coe.mp h

private lemma subfield_bot_eq : (⊥ : Subfield ℝ) = (Rat.castHom ℝ).fieldRange := by
  symm
  apply bot_unique
  rw [← sInf_univ]
  apply le_sInf
  intro S _
  apply SetLike.coe_subset_coe.mpr
  intro y hy
  obtain ⟨q, rfl⟩ := hy
  exact SubfieldClass.ratCast_mem S q

private lemma intermediate_bot_toSubfield :
    (⊥ : IntermediateField ℚ ℝ).toSubfield = ⊥ := by
  rw [subfield_bot_eq]
  ext x
  rw [IntermediateField.mem_toSubfield, IntermediateField.mem_bot,
    RingHom.mem_fieldRange]
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q, rfl⟩
  · rintro ⟨q, rfl⟩
    exact ⟨q, rfl⟩

private lemma trisect_pow_contradiction (Flast : IntermediateField ℚ ℝ) (n : ℕ)
    (hdeg3 : (minpoly ℚ (Real.cos (Real.pi / 9))).natDegree = 3)
    (hInt : IsIntegral ℚ (Real.cos (Real.pi / 9)))
    (hcF : Real.cos (Real.pi / 9) ∈ Flast)
    (hpow : Module.finrank ℚ ↥Flast ∣ 2 ^ n) :
    False := by
  have hfr3 : Module.finrank ℚ
      ↥(IntermediateField.adjoin ℚ {Real.cos (Real.pi / 9)}) = 3 := by
    rw [IntermediateField.adjoin.finrank hInt, hdeg3]
  have hadj_le : IntermediateField.adjoin ℚ {Real.cos (Real.pi / 9)} ≤ Flast :=
    IntermediateField.adjoin_le_iff.mpr
      (Set.singleton_subset_iff.mpr hcF)
  let : Algebra ↥(IntermediateField.adjoin ℚ {Real.cos (Real.pi / 9)}) ↥Flast :=
    RingHom.toAlgebra (IntermediateField.inclusion hadj_le).toRingHom
  have hval : ∀ a : ↥(IntermediateField.adjoin ℚ {Real.cos (Real.pi / 9)}),
      ((algebraMap ↥(IntermediateField.adjoin ℚ {Real.cos (Real.pi / 9)}) ↥Flast a
        : ↥Flast) : ℝ) = (a : ℝ) := by
    intro a
    exact IntermediateField.coe_inclusion hadj_le a
  have hcompat : ∀ x : ℚ, algebraMap
      ↥(IntermediateField.adjoin ℚ {Real.cos (Real.pi / 9)}) ↥Flast
      (algebraMap ℚ ↥(IntermediateField.adjoin ℚ {Real.cos (Real.pi / 9)}) x)
      = algebraMap ℚ ↥Flast x := by
    intro x
    apply Subtype.val_injective
    rw [hval]
    simp
  have htower : IsScalarTower ℚ
      ↥(IntermediateField.adjoin ℚ {Real.cos (Real.pi / 9)}) ↥Flast := by
    constructor
    intro x y z
    simp only [Algebra.smul_def]
    rw [map_mul, hcompat]
    ring
  have := htower
  have : Module ↥(IntermediateField.adjoin ℚ {Real.cos (Real.pi / 9)}) ↥Flast :=
    Algebra.toModule
  have := Module.Free.of_divisionRing ℚ
    ↥(IntermediateField.adjoin ℚ {Real.cos (Real.pi / 9)})
  have := Module.Free.of_divisionRing
    ↥(IntermediateField.adjoin ℚ {Real.cos (Real.pi / 9)}) ↥Flast
  have hmul : Module.finrank ℚ
      ↥(IntermediateField.adjoin ℚ {Real.cos (Real.pi / 9)})
      * Module.finrank ↥(IntermediateField.adjoin ℚ {Real.cos (Real.pi / 9)})
        ↥Flast
      = Module.finrank ℚ ↥Flast :=
    Module.finrank_mul_finrank ℚ
      ↥(IntermediateField.adjoin ℚ {Real.cos (Real.pi / 9)}) ↥Flast
  rw [hfr3] at hmul
  have h3dvd : 3 ∣ Module.finrank ℚ ↥Flast := ⟨_, hmul.symm⟩
  have h32 : (3 : ℕ) ∣ 2 ^ n := h3dvd.trans hpow
  have h32' : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) h32
  norm_num at h32'

private lemma trisect_not_constructible (IsConstructible : ℝ → Prop)
    (hChar : ∀ x : ℝ, IsConstructible x ↔
      ∃ (n : ℕ) (K : Fin (n + 1) → Subfield ℝ),
        K 0 = ⊥ ∧
        x ∈ K (Fin.last n) ∧
        ∀ i : Fin n, K i.castSucc ≤ K i.succ ∧
          ∃ b : ℝ, b ∈ K i.succ ∧ b ^ 2 ∈ K i.castSucc ∧
          ∀ y : ℝ, y ∈ K i.succ →
            ∃ u v : ℝ, u ∈ K i.castSucc ∧ v ∈ K i.castSucc ∧ y = u + b * v)
    (hirr : Irreducible (8 * (Polynomial.X : Polynomial ℚ) ^ 3 -
      6 * (Polynomial.X : Polynomial ℚ) - 1))
    (hroot : Polynomial.aeval (Real.cos (Real.pi / 9))
      (8 * (Polynomial.X : Polynomial ℚ) ^ 3 -
        6 * (Polynomial.X : Polynomial ℚ) - 1) = 0) :
    ¬ IsConstructible (Real.cos (Real.pi / 9)) := by
  intro hcon
  obtain ⟨n, K, hK0, hmem, hstep⟩ := (hChar _).mp hcon
  have hae8 : Polynomial.aeval (Real.cos (Real.pi / 9))
      (Polynomial.C (8 : ℚ)) = 8 := by simp
  have hroot_q : Polynomial.aeval (Real.cos (Real.pi / 9))
      (Polynomial.X ^ 3 - Polynomial.C (3 / 4 : ℚ) * Polynomial.X
        - Polynomial.C (1 / 8 : ℚ)) = 0 := by
    have h := hroot
    rw [trisect_eq, map_mul, hae8] at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  have hInt : IsIntegral ℚ (Real.cos (Real.pi / 9)) :=
    ⟨_, trisect_monic, hroot_q⟩
  have hdeg3 : (minpoly ℚ (Real.cos (Real.pi / 9))).natDegree = 3 := by
    have hmin_irr : Irreducible (minpoly ℚ (Real.cos (Real.pi / 9))) :=
      minpoly.irreducible hInt
    have hmin_dvd : minpoly ℚ (Real.cos (Real.pi / 9)) ∣
        (Polynomial.X ^ 3 - Polynomial.C (3 / 4 : ℚ) * Polynomial.X
          - Polynomial.C (1 / 8 : ℚ)) :=
      minpoly.dvd ℚ _ hroot_q
    have hassoc : Associated (minpoly ℚ (Real.cos (Real.pi / 9)))
        (Polynomial.X ^ 3 - Polynomial.C (3 / 4 : ℚ) * Polynomial.X
          - Polynomial.C (1 / 8 : ℚ)) :=
      Irreducible.associated_of_dvd hmin_irr
        (trisect_assoc.irreducible hirr) hmin_dvd
    have hle1 : (minpoly ℚ (Real.cos (Real.pi / 9))).natDegree ≤ 3 := by
      have h := Polynomial.natDegree_le_of_dvd hassoc.dvd trisect_monic.ne_zero
      rwa [trisect_natDegree] at h
    have hle2 : 3 ≤ (minpoly ℚ (Real.cos (Real.pi / 9))).natDegree := by
      have h := Polynomial.natDegree_le_of_dvd hassoc.symm.dvd
        (minpoly.ne_zero hInt)
      rwa [trisect_natDegree] at h
    omega
  have hmemQ : ∀ (i : Fin (n + 1)) (q : ℚ), algebraMap ℚ ℝ q ∈ K i :=
    fun i q => by simp
  have hF0 : (fun i => Subfield.toIntermediateField (K i) (hmemQ i)) 0 = ⊥ := by
    change Subfield.toIntermediateField (K 0) (hmemQ 0) = ⊥
    apply IntermediateField.toSubfield_injective
    have e1 : (Subfield.toIntermediateField (K 0) (hmemQ 0)).toSubfield
        = K 0 := rfl
    rw [e1, hK0]
    exact intermediate_bot_toSubfield.symm
  have hstepF : ∀ i : Fin n,
      (fun i => Subfield.toIntermediateField (K i) (hmemQ i)) i.castSucc
        ≤ (fun i => Subfield.toIntermediateField (K i) (hmemQ i)) i.succ ∧
      ∃ b : ℝ, b ∈ (fun i => Subfield.toIntermediateField (K i) (hmemQ i)) i.succ
        ∧ b ^ 2 ∈ (fun i => Subfield.toIntermediateField (K i) (hmemQ i)) i.castSucc
        ∧ ∀ y : ℝ, y ∈ (fun i => Subfield.toIntermediateField (K i) (hmemQ i)) i.succ
          → ∃ u v : ℝ, u ∈ (fun i => Subfield.toIntermediateField (K i) (hmemQ i)) i.castSucc
            ∧ v ∈ (fun i => Subfield.toIntermediateField (K i) (hmemQ i)) i.castSucc
            ∧ y = u + b * v := by
    intro i
    obtain ⟨hle, b, hb, hb2, hspan⟩ := hstep i
    change Subfield.toIntermediateField (K i.castSucc) _
        ≤ Subfield.toIntermediateField (K i.succ) _ ∧ _
    refine ⟨toIF_le hle, b, hb, hb2, ?_⟩
    intro y hy
    obtain ⟨u, v, hu, hv, rfl⟩ := hspan y hy
    exact ⟨u, v, hu, hv, rfl⟩
  have hpow := tower_two_pow n
    (fun i => Subfield.toIntermediateField (K i) (hmemQ i)) hF0 hstepF
  have hcF : Real.cos (Real.pi / 9)
      ∈ (fun i => Subfield.toIntermediateField (K i) (hmemQ i)) (Fin.last n) :=
    hmem
  exact trisect_pow_contradiction _ n hdeg3 hInt hcF hpow

/-- **Impossibility of angle trisection.** Let "constructible" be any property of real numbers such
that a real number $x$ is constructible exactly when there are $n \ge 0$ and subfields
$K_0 \subseteq K_1 \subseteq \dots \subseteq K_n$ of $\mathbb{R}$ with $K_0 = \mathbb{Q}$ (the
smallest subfield of $\mathbb{R}$), $x \in K_n$, and, for each $i < n$, some $b \in K_{i+1}$ with
$b^2 \in K_i$ such that every element of $K_{i+1}$ equals $u + bv$ for some $u, v \in K_i$. Let
an angle $\theta$ be constructible exactly when $\cos \theta$ is constructible. Then the polynomial
$8X^3 - 6X - 1$ is irreducible over $\mathbb{Q}$, $\cos(\pi/9)$ is a root of it, $\cos(\pi/9)$ is
not constructible, and it is not true that $\theta / 3$ is a constructible angle for every
constructible angle $\theta$.

In particular the $60^\circ$ angle, whose cosine $1/2$ is constructible, cannot be trisected: by
the triple-angle formula, $\cos 20^\circ = \cos(\pi/9)$ is a root of $8X^3 - 6X - 1$.

Source: https://en.wikipedia.org/wiki/Angle_trisection.

Proves `Wanted` entry `angle_trisection_impossible`.
-/
theorem angle_trisection_impossible :
    ∀ (IsConstructible : ℝ → Prop) (IsConstructibleAngle : ℝ → Prop),
      (∀ x : ℝ, IsConstructible x ↔
        ∃ (n : ℕ) (K : Fin (n + 1) → Subfield ℝ),
          K 0 = ⊥ ∧
          x ∈ K (Fin.last n) ∧
          ∀ i : Fin n, K i.castSucc ≤ K i.succ ∧
            ∃ b : ℝ, b ∈ K i.succ ∧ b ^ 2 ∈ K i.castSucc ∧
            ∀ y : ℝ, y ∈ K i.succ →
              ∃ u v : ℝ, u ∈ K i.castSucc ∧ v ∈ K i.castSucc ∧ y = u + b * v) →
      (∀ θ : ℝ, IsConstructibleAngle θ ↔ IsConstructible (Real.cos θ)) →
      Irreducible (8 * (Polynomial.X : Polynomial ℚ) ^ 3 -
        6 * (Polynomial.X : Polynomial ℚ) - 1) ∧
      Polynomial.aeval (Real.cos (Real.pi / 9))
        (8 * (Polynomial.X : Polynomial ℚ) ^ 3 -
          6 * (Polynomial.X : Polynomial ℚ) - 1) = 0 ∧
      ¬ IsConstructible (Real.cos (Real.pi / 9)) ∧
      ¬ ∀ θ : ℝ, IsConstructibleAngle θ → IsConstructibleAngle (θ / 3) := by
  intro IsConstructible IsConstructibleAngle hChar hAngle
  have hnc : ¬ IsConstructible (Real.cos (Real.pi / 9)) :=
    trisect_not_constructible IsConstructible hChar
      trisect_irreducible trisect_root
  refine ⟨trisect_irreducible, trisect_root, hnc, ?_⟩
  intro hall
  have h12 : IsConstructible (1 / 2 : ℝ) := by
    rw [hChar]
    refine ⟨0, fun _ => ⊥, rfl, ?_, ?_⟩
    · change (1 / 2 : ℝ) ∈ (⊥ : Subfield ℝ)
      have hcast : ((1 / 2 : ℚ) : ℝ) = (1 / 2 : ℝ) := by norm_num
      rw [← hcast]
      exact SubfieldClass.ratCast_mem _ _
    · intro i
      exact Fin.elim0 i
  have h13 : IsConstructibleAngle (Real.pi / 3) := by
    rw [hAngle, Real.cos_pi_div_three]
    exact h12
  have h19 : IsConstructibleAngle (Real.pi / 3 / 3) := hall _ h13
  have heq : Real.pi / 3 / 3 = Real.pi / 9 := by ring
  rw [heq, hAngle] at h19
  exact hnc h19

end MetaMathlibExt
