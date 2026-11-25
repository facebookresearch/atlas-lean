/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_PadicAlgCl_CyclotomicTower.lean`,
`Definitions/Def_PadicComplex_GaloisAction.lean`,
`Definitions/Def_PadicComplex_TateTrace.lean`,
`Theorems/Thm_PadicComplex_eq_zero_of_forall_mem_fixingSubgroup_smul_eq_
cyclotomicCharacter_zpow_mul.lean`,
`P2M/Sol/S_PadicAlgCl_finrank_cyclotomicTower_and_pow_mem_fixingSubgroup.lean`,
`P2M/Sol/S_PadicAlgCl_norm_sum_pow_apply_le_of_mem_cyclotomicTower.lean`,
`P2M/Sol/S_PadicComplex_exists_isTateTrace_cyclotomicTower.lean`,
`P2M/Sol/S_PadicComplex_exists_isTateTrace_of_norm_sum_pow_apply_le.lean`,
`P2M/Sol/S_PadicComplex_exists_forall_pow_eq_one_of_isTateTrace_of_tmul_eq_mul.lean`,
`P2M/Sol/S_PadicComplex_forall_smul_eq_self_iff_mem_closure.lean`,
`P2M/Sol/S_PadicComplex_eq_zero_of_forall_smul_eq_cyclotomicCharacter_zpow_mul.lean`
and
`P2M/Sol/S_PadicComplex_eq_zero_of_forall_mem_fixingSubgroup_smul_eq_
cyclotomicCharacter_zpow_mul.lean`
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

public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import MathlibExt.NumberTheory.Padics.DecompositionSubgroup

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.Topology.Algebra.Module.Basic

open UniformSpace

open scoped NNReal TensorProduct

noncomputable section


namespace PadicAlgCl


@[expose] public def cyclotomicTower (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IntermediateField ℚ_[p] (PadicAlgCl p) :=
  IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ (p ^ n) = 1}

public theorem mem_cyclotomicTower_of_pow_eq_one (p : ℕ) [Fact p.Prime] {n : ℕ} {ζ : PadicAlgCl p}
    (h : ζ ^ (p ^ n) = 1) : ζ ∈ cyclotomicTower p n :=
  IntermediateField.subset_adjoin ℚ_[p] _ h

public theorem cyclotomicTower_mono (p : ℕ) [Fact p.Prime] : Monotone (cyclotomicTower p) := by
  intro m n hmn
  refine IntermediateField.adjoin.mono ℚ_[p] _ _ fun ζ (hζ : ζ ^ (p ^ m) = 1) => ?_
  show ζ ^ (p ^ n) = 1
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [pow_add, pow_mul, hζ, one_pow]

end PadicAlgCl

namespace PadicComplex


variable (p : ℕ) [Fact p.Prime]

public abbrev Gal : Type := PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p

public theorem isometry_algEquiv (σ : Gal p) : Isometry σ := by
  refine AddMonoidHomClass.isometry_of_norm σ fun x => ?_
  exact (spectralNorm_eq_of_equiv σ x).symm

public instance uniformContinuousConstSMul_gal :
    UniformContinuousConstSMul (Gal p) (PadicAlgCl p) :=
  ⟨fun σ => (isometry_algEquiv p σ).uniformContinuous⟩

@[simp]
public theorem smul_coe (σ : Gal p) (x : PadicAlgCl p) :
    σ • ((x : ℂ_[p])) = ((σ x : PadicAlgCl p) : ℂ_[p]) :=
  (Completion.coe_smul σ x).symm

public theorem continuous_smul_left (σ : Gal p) : Continuous fun x : ℂ_[p] => σ • x :=
  continuous_const_smul σ

public theorem uniformContinuous_smul_left (σ : Gal p) : UniformContinuous fun x : ℂ_[p] => σ • x :=
  uniformContinuous_const_smul σ

public instance mulSemiringAction : MulSemiringAction (Gal p) ℂ_[p] :=
  { (inferInstance : DistribMulAction (Gal p) ℂ_[p]) with
    smul_one := fun σ => by
      rw [← Completion.coe_one, smul_coe, map_one]
    smul_mul := fun σ x y => by
      refine Completion.induction_on₂ x y ?_ ?_
      · exact isClosed_eq ((continuous_fst.mul continuous_snd).const_smul σ)
          ((continuous_fst.const_smul σ).mul (continuous_snd.const_smul σ))
      · intro a b
        rw [← Completion.coe_mul, smul_coe, smul_coe, smul_coe, map_mul, Completion.coe_mul] }

@[simp]
public theorem norm_smul_eq (σ : Gal p) (x : ℂ_[p]) : ‖σ • x‖ = ‖x‖ := by
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq ((continuous_norm).comp (continuous_const_smul σ)) continuous_norm
  · intro a
    rw [smul_coe, norm_extends, norm_extends]
    exact (spectralNorm_eq_of_equiv σ a).symm

@[simp]
public theorem nnnorm_smul_eq (σ : Gal p) (x : ℂ_[p]) : ‖σ • x‖₊ = ‖x‖₊ :=
  NNReal.eq (norm_smul_eq p σ x)

public theorem isometry_smul (σ : Gal p) : Isometry fun x : ℂ_[p] => σ • x :=
  AddMonoidHomClass.isometry_of_norm (MulSemiringAction.toRingHom (Gal p) ℂ_[p] σ)
    (norm_smul_eq p σ)

public instance smulCommClass_gal_padic : SMulCommClass (Gal p) ℚ_[p] ℂ_[p] :=
  inferInstance

public instance smulCommClass_padic_gal : SMulCommClass ℚ_[p] (Gal p) ℂ_[p] :=
  SMulCommClass.symm _ _ _

@[simp]
public theorem smul_algebraMap (σ : Gal p) (q : ℚ_[p]) :
    σ • (algebraMap ℚ_[p] ℂ_[p] q) = algebraMap ℚ_[p] ℂ_[p] q := by
  rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]

public abbrev galAlgHom (σ : Gal p) : ℂ_[p] →ₐ[ℚ_[p]] ℂ_[p] :=
  MulSemiringAction.toAlgHom ℚ_[p] ℂ_[p] σ

@[simp]
public theorem galAlgHom_apply (σ : Gal p) (x : ℂ_[p]) : galAlgHom p σ x = σ • x := rfl




variable (p : ℕ) [Fact p.Prime]

@[expose] public def towerClosure (Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)) : Set ℂ_[p] :=
  closure (⋃ m : ℕ, Set.range fun k : Km m => ((k : PadicAlgCl p) : ℂ_[p]))

public structure IsTateTrace (Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)) (m : ℕ) (d : ℝ)
    (R : ℂ_[p] → ℂ_[p]) : Prop where
  map_add : ∀ x ∈ towerClosure p Km, ∀ y ∈ towerClosure p Km, R (x + y) = R x + R y
  map_mul_left : ∀ (k : Km m), ∀ x ∈ towerClosure p Km,
    R (((k : PadicAlgCl p) : ℂ_[p]) * x) = ((k : PadicAlgCl p) : ℂ_[p]) * R x
  apply_coe : ∀ k : Km m, R ((k : PadicAlgCl p) : ℂ_[p]) = ((k : PadicAlgCl p) : ℂ_[p])
  exists_eq_coe : ∀ x ∈ towerClosure p Km, ∃ k : Km m, R x = ((k : PadicAlgCl p) : ℂ_[p])
  apply_smul : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (Km m).fixingSubgroup →
    ∀ x ∈ towerClosure p Km, R (σ • x) = R x
  norm_sub_apply_le : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (Km m).fixingSubgroup →
    σ ∉ (Km (m + 1)).fixingSubgroup → ∀ x ∈ towerClosure p Km, ‖x - R x‖ ≤ d * ‖σ • x - x‖

end PadicComplex

namespace CycTowerFinrank


open Polynomial

variable (p : ℕ) [Fact p.Prime]

local notation "Ω" => PadicAlgCl p
local notation "Γ" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)

private lemma exists_isPrimitiveRoot (n : ℕ) : ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ n) := by
  have hne : p ^ n ≠ 0 := pow_ne_zero n (Fact.out : p.Prime).ne_zero
  haveI : NeZero ((p ^ n : ℕ) : Ω) := ⟨by exact_mod_cast hne⟩
  haveI : IsCyclotomicExtension {p ^ n} Ω Ω := IsSepClosedOfCharZero.isCyclotomicExtension _ _
  exact IsCyclotomicExtension.exists_isPrimitiveRoot Ω Ω (S := {p ^ n}) rfl hne


lemma cyclotomicTower_eq_adjoin (n : ℕ) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ n)) :
    PadicAlgCl.cyclotomicTower p n = IntermediateField.adjoin ℚ_[p] {ζ} := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  apply le_antisymm
  · unfold PadicAlgCl.cyclotomicTower
    rw [IntermediateField.adjoin_le_iff]
    intro ξ (hξ : ξ ^ (p ^ n) = 1)
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ_[p] ζ) i
  · exact IntermediateField.adjoin.mono ℚ_[p] _ _ (Set.singleton_subset_iff.mpr hζ.pow_eq_one)

private lemma mem_fixingSubgroup_iff (n : ℕ) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ n)) (σ : Γ) :
    σ ∈ (PadicAlgCl.cyclotomicTower p n).fixingSubgroup ↔ σ ζ = ζ := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h
    exact h ζ (PadicAlgCl.mem_cyclotomicTower_of_pow_eq_one p hζ.pow_eq_one)
  · intro h x hx
    rw [cyclotomicTower_eq_adjoin p n hζ] at hx

    have hle : IntermediateField.adjoin ℚ_[p] {ζ} ≤
        IntermediateField.fixedField (Subgroup.zpowers σ) := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe,
        IntermediateField.mem_fixedField_iff]
      intro f hf
      obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf

      have hnat : ∀ k : ℕ, (σ ^ k) ζ = ζ := by
        intro k
        induction k with
        | zero => simp
        | succ k ih => rw [pow_succ, AlgEquiv.mul_apply, h, ih]
      rcases Int.eq_nat_or_neg z with ⟨k, rfl | rfl⟩
      · rw [zpow_natCast]; exact hnat k
      · rw [zpow_neg, zpow_natCast]
        have h1 := hnat k
        calc (σ ^ k)⁻¹ ζ = (σ ^ k)⁻¹ ((σ ^ k) ζ) := by rw [h1]
          _ = ζ := by rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    have hx' := hle hx
    rw [IntermediateField.mem_fixedField_iff] at hx'
    exact hx' σ (Subgroup.mem_zpowers σ)


lemma pow_apply_eq_pow_pow (σ : Γ) {ζ : Ω} {a : ℕ} (h : σ ζ = ζ ^ a) (j : ℕ) :
    (σ ^ j) ζ = ζ ^ (a ^ j) := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, h, map_pow, ih, ← pow_mul, ← pow_succ]

lemma mem_fixingSubgroup_iff_dvd {N n : ℕ} (hn : n ≤ N) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ N))
    (τ : Γ) {b : ℕ} (hb : 1 ≤ b) (hτ : τ ζ = ζ ^ b) :
    τ ∈ (PadicAlgCl.cyclotomicTower p n).fixingSubgroup ↔ p ^ n ∣ b - 1 := by
  have hpos : 0 < p ^ N := pow_pos (Fact.out : p.Prime).pos N

  have hζn : IsPrimitiveRoot (ζ ^ (p ^ (N - n))) (p ^ n) :=
    hζ.pow hpos (by rw [← pow_add, Nat.sub_add_cancel hn])
  rw [mem_fixingSubgroup_iff p n hζn, map_pow, hτ, ← pow_mul, mul_comm, pow_mul]
  set η : Ω := ζ ^ p ^ (N - n) with hη
  have hη0 : η ≠ 0 := hζn.ne_zero (pow_ne_zero n (Fact.out : p.Prime).ne_zero)
  have hsplit : η ^ b = η ^ (b - 1) * η := by rw [← pow_succ, Nat.sub_add_cancel hb]
  rw [hsplit]
  constructor
  · intro h
    have h1 : η ^ (b - 1) = 1 := by
      have h2 : η ^ (b - 1) * η = 1 * η := by rw [one_mul]; exact h
      exact mul_right_cancel₀ hη0 h2
    exact (hζn.pow_eq_one_iff_dvd _).mp h1
  · intro h
    rw [(hζn.pow_eq_one_iff_dvd _).mpr h, one_mul]

lemma pow_p_sub_one_of_dvd {a k : ℕ} (hk : 2 ≤ k) (ha : 1 ≤ a) (h1 : p ^ k ∣ a - 1)
    (h2 : ¬ p ^ (k + 1) ∣ a - 1) : p ^ (k + 1) ∣ a ^ p - 1 ∧ ¬ p ^ (k + 2) ∣ a ^ p - 1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨u, hu⟩ := h1
  have hpu : ¬ p ∣ u := by
    rintro ⟨v, rfl⟩
    apply h2
    refine ⟨v, ?_⟩
    rw [hu]; ring
  have ha' : a = p ^ k * u + 1 := by omega

  have hexp : a ^ p = ∑ i ∈ Finset.range (p + 1), (p ^ k * u) ^ i * (p.choose i) := by
    rw [ha', add_pow]
    simp

  have hp1 : p + 1 = (p - 1) + 1 + 1 := by have := hp.one_lt; omega
  have hsplit : ∑ i ∈ Finset.range (p + 1), (p ^ k * u) ^ i * (p.choose i) =
      1 + p ^ k * u * p + ∑ i ∈ Finset.range (p - 1), (p ^ k * u) ^ (i + 2) * (p.choose (i + 2))
        := by
    rw [hp1, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [pow_zero, Nat.choose_zero_right, mul_one, zero_add, pow_one,
      Nat.choose_one_right]
    ring

  have htail : p ^ (k + 2) ∣ ∑ i ∈ Finset.range (p - 1), (p ^ k * u) ^ (i + 2) * (p.choose (i +
    2)) := by
    apply Finset.dvd_sum
    intro i _
    apply Dvd.dvd.mul_right
    rw [mul_pow, ← pow_mul]
    apply Dvd.dvd.mul_right
    exact pow_dvd_pow p (by nlinarith)
  obtain ⟨M, hM⟩ := htail
  have hkey : a ^ p - 1 = p ^ (k + 1) * u + p ^ (k + 2) * M := by
    rw [hexp, hsplit, hM]
    have : p ^ k * u * p = p ^ (k + 1) * u := by ring
    rw [this]
    omega
  refine ⟨?_, ?_⟩
  · rw [hkey]
    exact dvd_add (dvd_mul_right _ _) (Dvd.dvd.mul_right (pow_dvd_pow p (by omega)) _)
  · rw [hkey]
    intro hdvd
    have h3 : p ^ (k + 2) ∣ p ^ (k + 1) * u :=
      (Nat.dvd_add_left (dvd_mul_right (p ^ (k + 2)) M)).mp hdvd
    rw [pow_succ] at h3
    exact hpu (Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos _) h3)

theorem pow_mem_and_not_mem (m : ℕ) (σ : Γ)
    (hσ : σ ∈ (PadicAlgCl.cyclotomicTower p (m + 2)).fixingSubgroup)
    (hσ' : σ ∉ (PadicAlgCl.cyclotomicTower p (m + 3)).fixingSubgroup) :
    σ ^ p ∈ (PadicAlgCl.cyclotomicTower p (m + 3)).fixingSubgroup ∧
      σ ^ p ∉ (PadicAlgCl.cyclotomicTower p (m + 4)).fixingSubgroup := by
  have hp : p.Prime := Fact.out
  set N := m + 4 with hN
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot p N
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N hp.ne_zero⟩

  obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one (ξ := σ ζ) (by rw [← map_pow, hζ.pow_eq_one,
    map_one])
  have ha' : σ ζ = ζ ^ a := ha.symm

  have ha1 : 1 ≤ a := by
    by_contra h0
    have : a = 0 := by omega
    subst this
    rw [pow_zero] at ha'

    have h1 : ζ = 1 := by
      have := congrArg σ.symm ha'
      simpa using this
    have hone : (p ^ N : ℕ) = 1 := by
      have := hζ.eq_orderOf
      rw [h1, orderOf_one] at this
      exact this
    have : 1 < p ^ N := Nat.one_lt_pow (by omega) hp.one_lt
    omega
  have hσp : (σ ^ p) ζ = ζ ^ (a ^ p) := pow_apply_eq_pow_pow p σ ha' p
  have hap1 : 1 ≤ a ^ p := Nat.one_le_pow _ _ ha1
  rw [mem_fixingSubgroup_iff_dvd p (by omega) hζ σ ha1 ha'] at hσ hσ'
  rw [mem_fixingSubgroup_iff_dvd p (by omega) hζ (σ ^ p) hap1 hσp,
    mem_fixingSubgroup_iff_dvd p (le_refl N) hζ (σ ^ p) hap1 hσp]
  exact pow_p_sub_one_of_dvd p (by omega) ha1 hσ hσ'

lemma isEisensteinAt_padicInt (k : ℕ) :
    (((cyclotomic (p ^ (k + 1)) ℤ).comp (X + 1)).map (Int.castRingHom ℤ_[p])).IsEisensteinAt
      (Ideal.span {(p : ℤ_[p])}) := by
  have hp : p.Prime := Fact.out
  set g : ℤ[X] := (cyclotomic (p ^ (k + 1)) ℤ).comp (X + 1) with hg
  have hZ : g.IsEisensteinAt (Ideal.span {(p : ℤ)}) :=
    cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p k
  have hgm : g.Monic := by
    have : (X + 1 : ℤ[X]) = X + C 1 := by rw [C_1]
    rw [hg, this]
    exact (cyclotomic.monic _ ℤ).comp_X_add_C 1
  have hg'm : (g.map (Int.castRingHom ℤ_[p])).Monic := hgm.map _
  have hdeg : (g.map (Int.castRingHom ℤ_[p])).natDegree = g.natDegree := hgm.natDegree_map _
  have hprime : (Ideal.span {(p : ℤ_[p])}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr PadicInt.prime_p
  refine hg'm.isEisensteinAt_of_mem_of_notMem hprime.ne_top ?_ ?_
  · intro n hn
    rw [hdeg] at hn
    rw [Polynomial.coeff_map, Ideal.mem_span_singleton]
    have h1 := hZ.mem hn
    rw [Ideal.mem_span_singleton] at h1
    exact map_dvd (Int.castRingHom ℤ_[p]) h1
  · intro hmem
    apply hZ.notMem
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem ⊢
    rw [Polynomial.coeff_map, eq_intCast] at hmem
    exact_mod_cast (PadicInt.pow_p_dvd_int_iff 2 (g.coeff 0)).mp hmem

lemma irreducible_cyclotomic (k : ℕ) : Irreducible (cyclotomic (p ^ (k + 1)) ℚ_[p]) := by
  have hp : p.Prime := Fact.out
  have hE := isEisensteinAt_padicInt p k
  have hmap : ((cyclotomic (p ^ (k + 1)) ℤ).comp (X + 1)).map (Int.castRingHom ℤ_[p]) =
      (cyclotomic (p ^ (k + 1)) ℤ_[p]).comp (X + 1) := by
    rw [Polynomial.map_comp, map_cyclotomic, Polynomial.map_add, map_X, Polynomial.map_one]
  rw [hmap] at hE
  have hmon : ((cyclotomic (p ^ (k + 1)) ℤ_[p]).comp (X + 1)).Monic := by
    have : (X + 1 : ℤ_[p][X]) = X + C 1 := by rw [C_1]
    rw [this]
    exact (cyclotomic.monic _ ℤ_[p]).comp_X_add_C 1
  have hprime : (Ideal.span {(p : ℤ_[p])}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr PadicInt.prime_p
  have hdeg : 0 < ((cyclotomic (p ^ (k + 1)) ℤ_[p]).comp (X + 1)).natDegree := by
    rw [natDegree_comp, natDegree_cyclotomic]
    have : (X + 1 : ℤ_[p][X]).natDegree = 1 := by
      have : (X + 1 : ℤ_[p][X]) = X + C 1 := by rw [C_1]
      rw [this, natDegree_X_add_C]
    rw [this, mul_one]
    exact Nat.totient_pos.mpr (pow_pos hp.pos _)
  have hirrZ : Irreducible ((cyclotomic (p ^ (k + 1)) ℤ_[p]).comp (X + 1)) :=
    hE.irreducible hprime hmon.isPrimitive hdeg
  have hirrQ : Irreducible ((cyclotomic (p ^ (k + 1)) ℚ_[p]).comp (X + 1)) := by
    have h := (hmon.irreducible_iff_irreducible_map_fraction_map (K := ℚ_[p])).mp hirrZ
    rwa [Polynomial.map_comp, map_cyclotomic, Polynomial.map_add, map_X, Polynomial.map_one] at h

  have hcomp : (algEquivAevalXAddC (1 : ℚ_[p])) (cyclotomic (p ^ (k + 1)) ℚ_[p]) =
      (cyclotomic (p ^ (k + 1)) ℚ_[p]).comp (X + 1) := by
    simp [algEquivAevalXAddC, comp_eq_aeval]
  rw [← hcomp] at hirrQ
  exact (MulEquiv.irreducible_iff (algEquivAevalXAddC (1 : ℚ_[p])).toMulEquiv).mp hirrQ

theorem finrank_cyclotomicTower (n : ℕ) (hn : 0 < n) :
    Module.finrank ℚ_[p] (PadicAlgCl.cyclotomicTower p n) = (p - 1) * p ^ (n - 1) := by
  have hp : p.Prime := Fact.out
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot p (k + 1)
  haveI : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI := hζ.intermediateField_adjoin_isCyclotomicExtension (K := ℚ_[p])
  rw [cyclotomicTower_eq_adjoin p (k + 1) hζ,
    IsCyclotomicExtension.finrank (IntermediateField.adjoin ℚ_[p] {ζ}) (irreducible_cyclotomic p k),
    Nat.totient_prime_pow hp (Nat.succ_pos k), mul_comm]

end CycTowerFinrank

namespace PadicAlgCl

/-- The finrank of the `p`-power cyclotomic tower over `ℚ_[p]`, and the
behaviour of automorphisms just outside a tower level under taking
`p`-th powers. -/
public theorem finrank_cyclotomicTower_and_pow_mem_fixingSubgroup (p : ℕ) [Fact p.Prime] :
    (∀ n : ℕ, 0 < n →
      Module.finrank ℚ_[p] (PadicAlgCl.cyclotomicTower p n) = (p - 1) * p ^ (n - 1)) ∧
    (∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
      σ ∈ (PadicAlgCl.cyclotomicTower p (m + 2)).fixingSubgroup →
      σ ∉ (PadicAlgCl.cyclotomicTower p (m + 3)).fixingSubgroup →
        σ ^ p ∈ (PadicAlgCl.cyclotomicTower p (m + 3)).fixingSubgroup ∧
          σ ^ p ∉ (PadicAlgCl.cyclotomicTower p (m + 4)).fixingSubgroup) :=
  ⟨CycTowerFinrank.finrank_cyclotomicTower p, CycTowerFinrank.pow_mem_and_not_mem p⟩

end PadicAlgCl

namespace CycTowerTraceBound


open Polynomial

variable (p : ℕ) [Fact p.Prime]

local notation "Ω" => PadicAlgCl p
local notation "Γ" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
local notation "L" => PadicAlgCl.cyclotomicTower p

lemma p_pos : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
lemma one_lt_p : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt

lemma norm_natCast_p : ‖(p : Ω)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] Ω) p, norm_algebraMap', Padic.norm_p]

lemma natCast_p_ne_zero : (p : Ω) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

lemma rpow_p_injective : Function.Injective fun x : ℝ => (p : ℝ) ^ x :=
  (Real.strictMono_rpow_of_base_gt_one (one_lt_p p)).injective

private lemma exists_isPrimitiveRoot (n : ℕ) : ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ n) := by
  have hne : p ^ n ≠ 0 := pow_ne_zero n (Fact.out : p.Prime).ne_zero
  haveI : NeZero ((p ^ n : ℕ) : Ω) := ⟨by exact_mod_cast hne⟩
  haveI : IsCyclotomicExtension {p ^ n} Ω Ω := IsSepClosedOfCharZero.isCyclotomicExtension _ _
  exact IsCyclotomicExtension.exists_isPrimitiveRoot Ω Ω (S := {p ^ n}) rfl hne

lemma cyclotomicTower_eq_adjoin (n : ℕ) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ n)) :
    L n = IntermediateField.adjoin ℚ_[p] {ζ} := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  apply le_antisymm
  · unfold PadicAlgCl.cyclotomicTower
    rw [IntermediateField.adjoin_le_iff]
    intro ξ (hξ : ξ ^ (p ^ n) = 1)
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ_[p] ζ) i
  · exact IntermediateField.adjoin.mono ℚ_[p] _ _ (Set.singleton_subset_iff.mpr hζ.pow_eq_one)

lemma mem_of_isPrimitiveRoot (n : ℕ) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ n)) : ζ ∈ L n :=
  PadicAlgCl.mem_cyclotomicTower_of_pow_eq_one p hζ.pow_eq_one

private lemma mem_fixingSubgroup_iff (n : ℕ) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ n)) (σ : Γ) :
    σ ∈ (L n).fixingSubgroup ↔ σ ζ = ζ := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h
    exact h ζ (mem_of_isPrimitiveRoot p n hζ)
  · intro h x hx
    rw [cyclotomicTower_eq_adjoin p n hζ] at hx
    have hle : IntermediateField.adjoin ℚ_[p] {ζ} ≤
        IntermediateField.fixedField (Subgroup.zpowers σ) := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe,
        IntermediateField.mem_fixedField_iff]
      intro f hf
      obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
      have hnat : ∀ k : ℕ, (σ ^ k) ζ = ζ := by
        intro k
        induction k with
        | zero => simp
        | succ k ih => rw [pow_succ, AlgEquiv.mul_apply, h, ih]
      rcases Int.eq_nat_or_neg z with ⟨k, rfl | rfl⟩
      · rw [zpow_natCast]; exact hnat k
      · rw [zpow_neg, zpow_natCast]
        have h1 := hnat k
        calc (σ ^ k)⁻¹ ζ = (σ ^ k)⁻¹ ((σ ^ k) ζ) := by rw [h1]
          _ = ζ := by rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    have hx' := hle hx
    rw [IntermediateField.mem_fixedField_iff] at hx'
    exact hx' σ (Subgroup.mem_zpowers σ)

lemma pow_apply_eq_pow_pow (σ : Γ) {ζ : Ω} {a : ℕ} (h : σ ζ = ζ ^ a) (j : ℕ) :
    (σ ^ j) ζ = ζ ^ (a ^ j) := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, h, map_pow, ih, ← pow_mul, ← pow_succ]

lemma mem_fixingSubgroup_iff_dvd {N n : ℕ} (hn : n ≤ N) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ N))
    (τ : Γ) {b : ℕ} (hb : 1 ≤ b) (hτ : τ ζ = ζ ^ b) :
    τ ∈ (L n).fixingSubgroup ↔ p ^ n ∣ b - 1 := by
  have hpos : 0 < p ^ N := pow_pos (Fact.out : p.Prime).pos N
  have hζn : IsPrimitiveRoot (ζ ^ (p ^ (N - n))) (p ^ n) :=
    hζ.pow hpos (by rw [← pow_add, Nat.sub_add_cancel hn])
  rw [mem_fixingSubgroup_iff p n hζn, map_pow, hτ, ← pow_mul, mul_comm, pow_mul]
  set η : Ω := ζ ^ p ^ (N - n) with hη
  have hη0 : η ≠ 0 := hζn.ne_zero (pow_ne_zero n (Fact.out : p.Prime).ne_zero)
  have hsplit : η ^ b = η ^ (b - 1) * η := by rw [← pow_succ, Nat.sub_add_cancel hb]
  rw [hsplit]
  constructor
  · intro h
    have h1 : η ^ (b - 1) = 1 := by
      have h2 : η ^ (b - 1) * η = 1 * η := by rw [one_mul]; exact h
      exact mul_right_cancel₀ hη0 h2
    exact (hζn.pow_eq_one_iff_dvd _).mp h1
  · intro h
    rw [(hζn.pow_eq_one_iff_dvd _).mpr h, one_mul]

lemma norm_eq_one_of_pow_eq_one {ζ : Ω} {k : ℕ} (h : ζ ^ k = 1) (hk : k ≠ 0) : ‖ζ‖ = 1 := by
  have h1 : ‖ζ‖ ^ k = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk).mp h1

lemma norm_one_sub_pow_le {ζ : Ω} {N : ℕ} (hζ : ζ ^ N = 1) (hN : N ≠ 0) (a : ℕ) :
    ‖1 - ζ ^ a‖ ≤ ‖1 - ζ‖ := by
  have h1 : 1 - ζ ^ a = (∑ i ∈ Finset.range a, ζ ^ i) * (1 - ζ) := by
    have := geom_sum_mul ζ a
    linear_combination this
  rw [h1, norm_mul]
  have h2 : ‖∑ i ∈ Finset.range a, ζ ^ i‖ ≤ 1 := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_pow, norm_eq_one_of_pow_eq_one p hζ hN, one_pow]
  calc ‖∑ i ∈ Finset.range a, ζ ^ i‖ * ‖1 - ζ‖ ≤ 1 * ‖1 - ζ‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ = ‖1 - ζ‖ := one_mul _

lemma norm_one_sub_eq_of_isPrimitiveRoot {n : ℕ} {ζ μ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ n))
    (hμ : IsPrimitiveRoot μ (p ^ n)) : ‖1 - μ‖ = ‖1 - ζ‖ := by
  have hne : p ^ n ≠ 0 := pow_ne_zero n (Fact.out : p.Prime).ne_zero
  haveI : NeZero (p ^ n) := ⟨hne⟩
  obtain ⟨a, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ.pow_eq_one
  obtain ⟨b, -, hb⟩ := hμ.eq_pow_of_pow_eq_one hζ.pow_eq_one
  apply le_antisymm (norm_one_sub_pow_le p hζ.pow_eq_one hne a)
  have := norm_one_sub_pow_le p hμ.pow_eq_one hne b
  rwa [hb] at this

theorem norm_sub_one_of_isPrimitiveRoot {n : ℕ} (hn : 0 < n) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^
  n)) :
    ‖ζ - 1‖ = (p : ℝ) ^ (-(1 : ℝ) / ((p ^ n).totient : ℝ)) := by
  have hp : p.Prime := Fact.out
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩

  have hprod : (p : Ω) = ∏ μ ∈ primitiveRoots (p ^ (k + 1)) Ω, (1 - μ) := by
    have h1 := eval_one_cyclotomic_prime_pow (R := Ω) (p := p) k
    rw [cyclotomic_eq_prod_X_sub_primitiveRoots hζ, eval_prod] at h1
    rw [← h1]
    refine Finset.prod_congr rfl fun μ _ => ?_
    simp
  have hnorm : (p : ℝ)⁻¹ = ‖ζ - 1‖ ^ (p ^ (k + 1)).totient := by
    rw [← norm_natCast_p p, hprod, norm_prod, ← hζ.card_primitiveRoots, ← Finset.prod_const]
    refine Finset.prod_congr rfl fun μ hμ => ?_
    rw [mem_primitiveRoots (pow_pos hp.pos _)] at hμ
    rw [norm_one_sub_eq_of_isPrimitiveRoot p hζ hμ, norm_sub_rev]
  have htot : (p ^ (k + 1)).totient ≠ 0 := (Nat.totient_pos.mpr (pow_pos hp.pos _)).ne'
  have h2 : ‖ζ - 1‖ = ((p : ℝ)⁻¹) ^ (((p ^ (k + 1)).totient : ℝ)⁻¹) := by
    rw [hnorm, Real.pow_rpow_inv_natCast (norm_nonneg _) htot]
  rw [h2, Real.inv_rpow (p_pos p).le, ← Real.rpow_neg (p_pos p).le]
  congr 1
  rw [neg_div, one_div]

def e (n : ℕ) : ℕ := (p ^ n).totient

lemma e_pos (n : ℕ) : 0 < e p n := Nat.totient_pos.mpr (pow_pos (Fact.out : p.Prime).pos n)

def d (n : ℕ) : ℕ := if n = 0 then p - 1 else p

lemma d_pos (n : ℕ) : 0 < d p n := by
  unfold d; split_ifs
  · have := (Fact.out : p.Prime).one_lt; omega
  · exact (Fact.out : p.Prime).pos

lemma e_succ (n : ℕ) : e p (n + 1) = d p n * e p n := by
  have hp : p.Prime := Fact.out
  unfold e d
  split_ifs with h
  · subst h; simp [Nat.totient_prime hp]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Nat.totient_prime_pow_succ hp, Nat.totient_prime_pow_succ hp]
    ring

lemma cyclotomicTower_zero : L 0 = ⊥ := by
  apply le_antisymm _ bot_le
  unfold PadicAlgCl.cyclotomicTower
  rw [IntermediateField.adjoin_le_iff]
  intro x (hx : x ^ p ^ 0 = 1)
  rw [pow_zero, pow_one] at hx
  rw [hx]
  exact (⊥ : IntermediateField ℚ_[p] Ω).one_mem

lemma finrank_eq_e (n : ℕ) : Module.finrank ℚ_[p] (L n) = e p n := by
  have hp : p.Prime := Fact.out
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [cyclotomicTower_zero, IntermediateField.finrank_bot]
    simp [e]
  · rw [(PadicAlgCl.finrank_cyclotomicTower_and_pow_mem_fixingSubgroup p).1 n hn]
    unfold e
    rw [Nat.totient_prime_pow hp hn, mul_comm]

scoped instance finiteDimensional_L (n : ℕ) : FiniteDimensional ℚ_[p] (L n) :=
  Module.finite_of_finrank_pos (by rw [finrank_eq_e]; exact e_pos p n)

def VG (n : ℕ) : Prop :=
  ∀ c : Ω, c ∈ L n → c ≠ 0 → ∃ k : ℤ, ‖c‖ = (p : ℝ) ^ ((k : ℝ) / (e p n : ℝ))

lemma VG_zero : VG p 0 := by
  intro c hc hc0
  rw [cyclotomicTower_zero, IntermediateField.mem_bot] at hc
  obtain ⟨q, rfl⟩ := hc
  have hq : q ≠ 0 := by rintro rfl; exact hc0 (map_zero _)
  refine ⟨-q.valuation, ?_⟩
  rw [norm_algebraMap', Padic.norm_eq_zpow_neg_valuation hq]
  simp only [e, pow_zero, Nat.totient_one, Nat.cast_one, div_one]
  rw [← Real.rpow_intCast, Int.cast_neg]

lemma norm_term {n : ℕ} (hVG : VG p n) {π : Ω}
    (hπ : ‖π‖ = (p : ℝ) ^ (-(1 : ℝ) / (e p (n + 1) : ℝ)))
    {c : Ω} (hc : c ∈ L n) (hc0 : c ≠ 0) (i : ℕ) :
    ∃ k : ℤ, ‖c * π ^ i‖ = (p : ℝ) ^ (((k * (d p n : ℤ) - (i : ℤ) : ℤ) : ℝ) / (e p (n + 1) : ℝ))
      := by
  obtain ⟨k, hk⟩ := hVG c hc hc0
  refine ⟨k, ?_⟩
  rw [norm_mul, norm_pow, hk, hπ, ← Real.rpow_natCast, ← Real.rpow_mul (p_pos p).le,
    ← Real.rpow_add (p_pos p)]
  congr 1
  have he : (e p (n + 1) : ℝ) = (d p n : ℝ) * (e p n : ℝ) := by exact_mod_cast e_succ p n
  have hen : (e p n : ℝ) ≠ 0 := by exact_mod_cast (e_pos p n).ne'
  have hd : (d p n : ℝ) ≠ 0 := by exact_mod_cast (d_pos p n).ne'
  rw [he]
  push_cast
  field_simp
  ring

lemma exponent_ne {n : ℕ} {i j : ℕ} (hi : i < d p n) (hj : j < d p n) (hij : i ≠ j) (k k' : ℤ) :
    (((k * (d p n : ℤ) - (i : ℤ) : ℤ) : ℝ) / (e p (n + 1) : ℝ)) ≠
      (((k' * (d p n : ℤ) - (j : ℤ) : ℤ) : ℝ) / (e p (n + 1) : ℝ)) := by
  intro h
  have hen : (e p (n + 1) : ℝ) ≠ 0 := by exact_mod_cast (e_pos p (n + 1)).ne'
  rw [div_left_inj' hen] at h
  have h2 : (k * (d p n : ℤ) - (i : ℤ) : ℤ) = k' * (d p n : ℤ) - (j : ℤ) := by exact_mod_cast h
  have h3 : ((d p n : ℤ)) ∣ ((j : ℤ) - (i : ℤ)) := ⟨k' - k, by linarith⟩
  have h4 : ((j : ℤ) - (i : ℤ)) = 0 := by
    apply Int.eq_zero_of_abs_lt_dvd h3
    rw [abs_lt]; constructor <;> omega
  exact hij (by omega)

lemma nnnorm_sum_eq_sup {n : ℕ} (hVG : VG p n) {π : Ω}
    (hπ : ‖π‖ = (p : ℝ) ^ (-(1 : ℝ) / (e p (n + 1) : ℝ)))
    (c : ℕ → Ω) (hc : ∀ i < d p n, c i ∈ L n) :
    ‖∑ i ∈ Finset.range (d p n), c i * π ^ i‖₊ =
      (Finset.range (d p n)).sup fun i => ‖c i‖₊ * ‖π‖₊ ^ i := by
  classical
  set s := (Finset.range (d p n)).filter (fun i => c i ≠ 0) with hs
  have hsum : ∑ i ∈ Finset.range (d p n), c i * π ^ i = ∑ i ∈ s, c i * π ^ i := by
    rw [hs, Finset.sum_filter_of_ne]
    intro i _ hne hci
    exact hne (by rw [hci, zero_mul])
  have hpair : (s : Set ℕ).Pairwise fun i j => ‖c i * π ^ i‖₊ ≠ ‖c j * π ^ j‖₊ := by
    intro i hi j hj hij
    rw [Finset.mem_coe, hs, Finset.mem_filter, Finset.mem_range] at hi hj
    obtain ⟨k, hk⟩ := norm_term p hVG hπ (hc i hi.1) hi.2 i
    obtain ⟨k', hk'⟩ := norm_term p hVG hπ (hc j hj.1) hj.2 j
    intro heq
    have heq' : ‖c i * π ^ i‖ = ‖c j * π ^ j‖ := by
      have h := congrArg ((↑) : NNReal → ℝ) heq
      simpa only [coe_nnnorm] using h
    rw [hk, hk'] at heq'
    exact exponent_ne p hi.1 hj.1 hij k k' (rpow_p_injective p heq')
  rw [hsum, IsUltrametricDist.nnnorm_sum_eq_sup_of_pairwise_ne hpair]
  simp only [nnnorm_mul, nnnorm_pow]
  apply le_antisymm
  · exact Finset.sup_mono (Finset.filter_subset _ _)
  · apply Finset.sup_le
    intro i hi
    by_cases hci : c i = 0
    · rw [hci, nnnorm_zero, zero_mul]; exact bot_le
    · exact Finset.le_sup (f := fun i => ‖c i‖₊ * ‖π‖₊ ^ i) (Finset.mem_filter.mpr ⟨hi, hci⟩)

def combo (n : ℕ) (π : Ω) : (Fin (d p n) → L n) →ₗ[ℚ_[p]] Ω where
  toFun v := ∑ i : Fin (d p n), ((v i : L n) : Ω) * π ^ (i : ℕ)
  map_add' v w := by
    simp only [Pi.add_apply, IntermediateField.coe_add, add_mul, Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, IntermediateField.coe_smul, RingHom.id_apply, Finset.smul_sum,
      smul_mul_assoc]

lemma combo_apply (n : ℕ) (π : Ω) (v : Fin (d p n) → L n) :
    combo p n π v = ∑ i ∈ Finset.range (d p n),
      (fun i => if h : i < d p n then ((v ⟨i, h⟩ : L n) : Ω) else 0) i * π ^ i := by
  simp only [combo, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [i.2]

lemma exists_coeff {n n' : ℕ} (hn' : n' = n + 1) (hVG : VG p n) {π : Ω} (hπmem : π ∈ L n')
    (hπ : ‖π‖ = (p : ℝ) ^ (-(1 : ℝ) / (e p n' : ℝ))) (y : Ω) (hy : y ∈ L n') :
    ∃ c : ℕ → Ω, (∀ i, c i ∈ L n) ∧ y = ∑ i ∈ Finset.range (d p n), c i * π ^ i := by
  classical
  subst hn'
  have hπ0 : π ≠ 0 := by
    intro h; rw [h, norm_zero] at hπ
    exact (Real.rpow_pos_of_pos (p_pos p) _).ne hπ
  set Φ := combo p n π with hΦ

  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    set c : ℕ → Ω := fun i => if h : i < d p n then ((v ⟨i, h⟩ : L n) : Ω) else 0 with hcdef
    have hcmem : ∀ i < d p n, c i ∈ L n := by
      intro i hi; simp only [hcdef, dif_pos hi]; exact (v ⟨i, hi⟩).2
    have hsum : ∑ i ∈ Finset.range (d p n), c i * π ^ i = 0 := by
      rw [← hv, hΦ, combo_apply]
    have horth := nnnorm_sum_eq_sup p hVG hπ c hcmem
    rw [hsum, nnnorm_zero] at horth
    funext i
    have hle : ‖c i‖₊ * ‖π‖₊ ^ (i : ℕ) ≤ 0 := by
      rw [horth]
      exact Finset.le_sup (f := fun i => ‖c i‖₊ * ‖π‖₊ ^ i) (Finset.mem_range.mpr i.2)
    have hci : c i = 0 := by
      have h1 : ‖c i‖₊ * ‖π‖₊ ^ (i : ℕ) = 0 := le_antisymm hle bot_le
      rw [mul_eq_zero] at h1
      rcases h1 with h1 | h1
      · exact nnnorm_eq_zero.mp h1
      · exact absurd (eq_zero_of_pow_eq_zero h1) (nnnorm_ne_zero_iff.mpr hπ0)
    simp only [hcdef, dif_pos i.2] at hci
    exact Subtype.ext hci

  set R₂ : Submodule ℚ_[p] Ω := LinearMap.range ((L (n + 1)).val.toLinearMap) with hR₂
  have hval_inj : Function.Injective ((L (n + 1)).val.toLinearMap) := fun a b h => Subtype.ext h
  have hle : LinearMap.range Φ ≤ R₂ := by
    rintro _ ⟨v, rfl⟩
    have hmem : Φ v ∈ L (n + 1) := by
      rw [hΦ]
      simp only [combo, LinearMap.coe_mk, AddHom.coe_mk]
      refine sum_mem fun i _ => mul_mem ?_ (pow_mem hπmem _)
      exact PadicAlgCl.cyclotomicTower_mono p (Nat.le_succ n) (v i).2
    exact ⟨⟨Φ v, hmem⟩, rfl⟩
  have hfin : Module.finrank ℚ_[p] (LinearMap.range Φ) = Module.finrank ℚ_[p] R₂ := by
    rw [LinearMap.finrank_range_of_inj hinj, hR₂, LinearMap.finrank_range_of_inj hval_inj,
      Module.finrank_pi_fintype, finrank_eq_e, finrank_eq_e, e_succ]
    simp
  have hEq : LinearMap.range Φ = R₂ := Submodule.eq_of_le_of_finrank_eq hle hfin
  have hyR : y ∈ R₂ := ⟨⟨y, hy⟩, rfl⟩
  rw [← hEq] at hyR
  obtain ⟨v, hv⟩ := hyR
  refine ⟨fun i => if h : i < d p n then ((v ⟨i, h⟩ : L n) : Ω) else 0, fun i => ?_, ?_⟩
  · by_cases h : i < d p n
    · simp only [dif_pos h]; exact (v ⟨i, h⟩).2
    · simp only [dif_neg h]; exact zero_mem _
  · rw [← hv, hΦ, combo_apply]

lemma VG_succ {n n' : ℕ} (hn' : n' = n + 1) (hVG : VG p n) : VG p n' := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot p n'
  have hn'pos : 0 < n' := by omega
  set π : Ω := ζ - 1 with hπdef
  have hπ : ‖π‖ = (p : ℝ) ^ (-(1 : ℝ) / (e p n' : ℝ)) := norm_sub_one_of_isPrimitiveRoot p hn'pos hζ
  have hπmem : π ∈ L n' := sub_mem (mem_of_isPrimitiveRoot p n' hζ) (one_mem _)
  intro y hy hy0
  obtain ⟨c, hcmem, hyc⟩ := exists_coeff p hn' hVG hπmem hπ y hy
  subst hn'
  have horth := nnnorm_sum_eq_sup p hVG hπ c (fun i _ => hcmem i)
  rw [← hyc] at horth
  obtain ⟨i₀, hi₀, hsup⟩ := Finset.exists_mem_eq_sup (Finset.range (d p n))
    (Finset.nonempty_range_iff.mpr (d_pos p n).ne') (fun i => ‖c i‖₊ * ‖π‖₊ ^ i)
  rw [hsup] at horth
  have hci₀ : c i₀ ≠ 0 := by
    intro h
    rw [h, nnnorm_zero, zero_mul, nnnorm_eq_zero] at horth
    exact hy0 horth
  obtain ⟨k, hk⟩ := norm_term p hVG hπ (hcmem i₀) hci₀ i₀
  refine ⟨k * (d p n : ℤ) - (i₀ : ℤ), ?_⟩
  rw [← hk, norm_mul, norm_pow]
  have h := congrArg ((↑) : NNReal → ℝ) horth
  simpa only [coe_nnnorm, NNReal.coe_mul, NNReal.coe_pow] using h

theorem VG_all : ∀ n, VG p n := by
  intro n
  induction n with
  | zero => exact VG_zero p
  | succ n ih => exact VG_succ p rfl ih

def T (σ : Γ) (y : Ω) : Ω := ∑ j ∈ Finset.range p, (σ ^ j) y

lemma T_add (σ : Γ) (y y' : Ω) : T p σ (y + y') = T p σ y + T p σ y' := by
  simp only [T, map_add, Finset.sum_add_distrib]

lemma T_sum (σ : Γ) {ι : Type*} (s : Finset ι) (f : ι → Ω) :
    T p σ (∑ i ∈ s, f i) = ∑ i ∈ s, T p σ (f i) := by
  simp only [T, map_sum]
  rw [Finset.sum_comm]

lemma pow_apply_of_apply_eq (σ : Γ) {a : Ω} (ha : σ a = a) (j : ℕ) : (σ ^ j) a = a := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, ha, ih]

lemma T_mul_of_fixed (σ : Γ) (a y : Ω) (ha : σ a = a) : T p σ (a * y) = a * T p σ y := by
  simp only [T, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_apply_of_apply_eq p σ ha j]

lemma T_mul_intCast (σ : Γ) (y : Ω) (z : ℤ) : T p σ (y * z) = T p σ y * z := by
  simp only [T, map_mul, map_intCast, Finset.sum_mul]

omit [Fact p.Prime] in

lemma pow_a_eq (k u a : ℕ) (ha : a = 1 + p ^ (k + 1) * u) (j : ℕ) :
    ∃ r : ℕ, a ^ j = 1 + p ^ (k + 1) * (j * u) + p ^ (k + 2) * r := by
  induction j with
  | zero => exact ⟨0, by simp⟩
  | succ j ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨p ^ k * j * u ^ 2 + r + p ^ (k + 1) * r * u, ?_⟩
      rw [pow_succ, hr, ha]
      ring

lemma T_zeta_pow {k : ℕ} {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ (k + 2))) (σ : Γ) {a u : ℕ}
    (ha : a = 1 + p ^ (k + 1) * u) (hσ : σ ζ = ζ ^ a) (m : ℕ) :
    T p σ (ζ ^ m) = ζ ^ m * ∑ j ∈ Finset.range p, ((ζ ^ p ^ (k + 1)) ^ (m * u)) ^ j := by
  simp only [T, map_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_apply_eq_pow_pow p σ hσ j, ← pow_mul]
  obtain ⟨r, hr⟩ := pow_a_eq p k u a ha j
  rw [hr]
  have h1 : ζ ^ (p ^ (k + 2)) = 1 := hζ.pow_eq_one
  calc ζ ^ ((1 + p ^ (k + 1) * (j * u) + p ^ (k + 2) * r) * m)
      = ζ ^ m * (ζ ^ p ^ (k + 1)) ^ (m * u * j) * (ζ ^ p ^ (k + 2)) ^ (r * m) := by
        rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]; congr 1; ring
    _ = ζ ^ m * ((ζ ^ p ^ (k + 1)) ^ (m * u)) ^ j := by
        rw [h1, one_pow, mul_one, ← pow_mul (ζ ^ p ^ (k + 1)) (m * u) j]

lemma T_zeta_pow_eq_zero {k : ℕ} {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ (k + 2))) (σ : Γ) {a u : ℕ}
    (ha : a = 1 + p ^ (k + 1) * u) (hσ : σ ζ = ζ ^ a) {m : ℕ} (hm : ¬ p ∣ m * u) :
    T p σ (ζ ^ m) = 0 := by
  have hp : p.Prime := Fact.out
  rw [T_zeta_pow p hζ σ ha hσ m]
  have hξ : IsPrimitiveRoot (ζ ^ p ^ (k + 1)) p :=
    hζ.pow (pow_pos hp.pos _) (by rw [pow_succ])
  have hξ' : IsPrimitiveRoot ((ζ ^ p ^ (k + 1)) ^ (m * u)) p :=
    hξ.pow_of_coprime _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm |>.symm)
  rw [hξ'.geom_sum_eq_zero hp.one_lt, mul_zero]

lemma T_one (σ : Γ) : T p σ 1 = p := by
  simp [T]

theorem T_pi_pow {k : ℕ} {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ (k + 2))) (σ : Γ) {a u : ℕ}
    (ha : a = 1 + p ^ (k + 1) * u) (hu : ¬ p ∣ u) (hσ : σ ζ = ζ ^ a) {i : ℕ} (hi : i < p) :
    T p σ ((ζ - 1) ^ i) = (-1) ^ i * p := by
  have hp : p.Prime := Fact.out
  have hexp : (ζ - 1) ^ i = ∑ m ∈ Finset.range (i + 1), ζ ^ m * ((-1) ^ (i - m) * (i.choose m : ℤ)
    : ℤ) := by
    rw [sub_eq_add_neg, add_pow]
    refine Finset.sum_congr rfl fun m _ => ?_
    push_cast; ring
  rw [hexp, T_sum]
  rw [Finset.sum_range_succ']
  have hzero : ∀ m ∈ Finset.range i,
      T p σ (ζ ^ (m + 1) * ((-1) ^ (i - (m + 1)) * (i.choose (m + 1) : ℤ) : ℤ)) = 0 := by
    intro m hm
    rw [Finset.mem_range] at hm
    rw [T_mul_intCast, T_zeta_pow_eq_zero p hζ σ ha hσ, zero_mul]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · exact absurd (Nat.le_of_dvd (Nat.succ_pos m) h) (by omega)
    · exact hu h
  rw [Finset.sum_eq_zero hzero, zero_add, T_mul_intCast, pow_zero, T_one]
  push_cast
  simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
  ring

theorem main (m : ℕ) (σ : Γ)
    (hσ : σ ∈ (L (m + 2)).fixingSubgroup) (hσ' : σ ∉ (L (m + 3)).fixingSubgroup)
    (y : Ω) (hy : y ∈ L (m + 3)) :
    ‖∑ i ∈ Finset.range p, (σ ^ i) y‖ ≤
      ‖(p : ℚ_[p])‖ * (p : ℝ) ^ (1 / (((p : ℝ) - 1) * (p : ℝ) ^ (m + 1))) * ‖y‖ := by
  classical
  have hp : p.Prime := Fact.out

  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot p (m + 3)
  haveI : NeZero (p ^ (m + 3)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one (ξ := σ ζ)
    (by rw [← map_pow, hζ.pow_eq_one, map_one])
  have ha' : σ ζ = ζ ^ a := ha.symm
  have ha1 : 1 ≤ a := by
    by_contra h0
    have : a = 0 := by omega
    subst this
    rw [pow_zero] at ha'
    have h1 : ζ = 1 := by
      have := congrArg σ.symm ha'
      simpa using this
    have hone : (p ^ (m + 3) : ℕ) = 1 := by
      have := hζ.eq_orderOf
      rw [h1, orderOf_one] at this
      exact this
    have : 1 < p ^ (m + 3) := Nat.one_lt_pow (by omega) hp.one_lt
    omega
  have hdvd : p ^ (m + 2) ∣ a - 1 :=
    (mem_fixingSubgroup_iff_dvd p (by omega) hζ σ ha1 ha').mp hσ
  have hndvd : ¬ p ^ (m + 3) ∣ a - 1 := fun h =>
    hσ' ((mem_fixingSubgroup_iff_dvd p (le_refl _) hζ σ ha1 ha').mpr h)
  obtain ⟨u, hu⟩ := hdvd
  have hpu : ¬ p ∣ u := by
    rintro ⟨v, rfl⟩
    apply hndvd
    exact ⟨v, by rw [hu]; ring⟩
  have haeq : a = 1 + p ^ (m + 2) * u := by omega

  set π : Ω := ζ - 1 with hπdef
  have hπ : ‖π‖ = (p : ℝ) ^ (-(1 : ℝ) / (e p (m + 3) : ℝ)) :=
    norm_sub_one_of_isPrimitiveRoot p (by omega) hζ
  have hπmem : π ∈ L (m + 3) := sub_mem (mem_of_isPrimitiveRoot p (m + 3) hζ) (one_mem _)
  have hπpos : 0 < ‖π‖ := by rw [hπ]; exact Real.rpow_pos_of_pos (p_pos p) _
  have hπle : ‖π‖ ≤ 1 := by
    rw [hπ]
    apply Real.rpow_le_one_of_one_le_of_nonpos (one_lt_p p).le
    have : (0 : ℝ) < (e p (m + 3) : ℝ) := by exact_mod_cast e_pos p (m + 3)
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) this.le

  have hVG := VG_all p (m + 2)
  obtain ⟨c, hcmem, hyc⟩ := exists_coeff p rfl hVG hπmem hπ y hy
  have hd : d p (m + 2) = p := by simp [d]
  rw [hd] at hyc
  have horth := nnnorm_sum_eq_sup p hVG hπ c (fun i _ => hcmem i)
  rw [hd, ← hyc] at horth

  have hci : ∀ i < p, ‖c i‖ * ‖π‖ ^ i ≤ ‖y‖ := by
    intro i hi
    have h1 : ‖c i‖₊ * ‖π‖₊ ^ i ≤ ‖y‖₊ := by
      rw [horth]
      exact Finset.le_sup (f := fun i => ‖c i‖₊ * ‖π‖₊ ^ i) (Finset.mem_range.mpr hi)
    exact_mod_cast h1

  have hT : ∑ i ∈ Finset.range p, (σ ^ i) y = (p : Ω) * ∑ i ∈ Finset.range p, (-1) ^ i * c i := by
    show T p σ y = _
    rw [hyc, T_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    have hfix : σ (c i) = c i :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ _ (hcmem i)
    rw [T_mul_of_fixed p σ (c i) _ hfix, T_pi_pow p hζ σ haeq hpu ha' hi]
    ring
  rw [hT, norm_mul, norm_natCast_p, ← Padic.norm_p]

  have hB : ‖∑ i ∈ Finset.range p, (-1) ^ i * c i‖ ≤ ‖y‖ / ‖π‖ ^ (p - 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rw [le_div_iff₀ (pow_pos hπpos _)]
    calc ‖c i‖ * ‖π‖ ^ (p - 1) ≤ ‖c i‖ * ‖π‖ ^ i :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hπpos.le hπle (by omega)) (norm_nonneg _)
      _ ≤ ‖y‖ := hci i hi

  have hpow : ‖y‖ / ‖π‖ ^ (p - 1) ≤ (p : ℝ) ^ (1 / (((p : ℝ) - 1) * (p : ℝ) ^ (m + 1))) * ‖y‖ := by
    rw [div_eq_mul_inv, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [hπ, ← Real.rpow_natCast, ← Real.rpow_mul (p_pos p).le, ← Real.rpow_neg (p_pos p).le]
    apply Real.rpow_le_rpow_of_exponent_le (one_lt_p p).le

    have he : (e p (m + 3) : ℝ) = ((p : ℝ) - 1) * (p : ℝ) ^ (m + 2) := by
      unfold e
      rw [Nat.totient_prime_pow_succ hp]
      have h1 : 1 ≤ p := hp.one_lt.le
      push_cast [Nat.cast_sub h1]
      ring
    rw [he]
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by have := one_lt_p p; linarith
    have hpp : (0 : ℝ) < (p : ℝ) ^ (m + 1) := pow_pos (p_pos p) _
    have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hp.one_lt.le]; simp
    rw [hcast]
    have hsimp : -(-1 / (((p : ℝ) - 1) * (p : ℝ) ^ (m + 2)) * ((p : ℝ) - 1)) = 1 / (p : ℝ) ^ (m +
      2) := by
      field_simp
    rw [hsimp]
    apply one_div_le_one_div_of_le (by positivity)
    have : (p : ℝ) ^ (m + 2) = (p : ℝ) ^ (m + 1) * p := by ring
    rw [this]
    nlinarith [one_lt_p p]
  calc ‖(p : ℚ_[p])‖ * ‖∑ i ∈ Finset.range p, (-1) ^ i * c i‖
      ≤ ‖(p : ℚ_[p])‖ * (‖y‖ / ‖π‖ ^ (p - 1)) := mul_le_mul_of_nonneg_left hB (norm_nonneg _)
    _ ≤ ‖(p : ℚ_[p])‖ * ((p : ℝ) ^ (1 / (((p : ℝ) - 1) * (p : ℝ) ^ (m + 1))) * ‖y‖) :=
        mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
    _ = ‖(p : ℚ_[p])‖ * (p : ℝ) ^ (1 / (((p : ℝ) - 1) * (p : ℝ) ^ (m + 1))) * ‖y‖ := by ring


end CycTowerTraceBound

namespace PadicAlgCl

/-- Tate's trace bound: for `σ` fixing the tower level `m + 2` but not
`m + 3`, the norm of the trace sum `∑ i < p, (σ ^ i) y` over an element
of the next level is bounded by `‖p‖` times a root-of-unity factor. -/
public theorem norm_sum_pow_apply_le_of_mem_cyclotomicTower (p : ℕ) [Fact p.Prime]
    (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hσ : σ ∈ (PadicAlgCl.cyclotomicTower p (m + 2)).fixingSubgroup)
    (hσ' : σ ∉ (PadicAlgCl.cyclotomicTower p (m + 3)).fixingSubgroup)
    (y : PadicAlgCl p) (hy : y ∈ PadicAlgCl.cyclotomicTower p (m + 3)) :
    ‖∑ i ∈ Finset.range p, (σ ^ i) y‖ ≤
      ‖(p : ℚ_[p])‖ * (p : ℝ) ^ (1 / (((p : ℝ) - 1) * (p : ℝ) ^ (m + 1))) * ‖y‖ :=
  CycTowerTraceBound.main p m σ hσ hσ' y hy

end PadicAlgCl

namespace PadicComplex

end PadicComplex

namespace ApproxBySubfield

open Polynomial


variable (p : ℕ) [hp : Fact p.Prime]

local notation "Ω" => PadicAlgCl p
local notation "Γ" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)

lemma norm_algEquiv (σ : Γ) (x : Ω) : ‖σ x‖ = ‖x‖ :=
  (spectralNorm_eq_of_equiv σ x).symm

lemma norm_natCast (N : ℕ) : ‖(N : Ω)‖ = ‖(N : ℚ_[p])‖ := by
  rw [← map_natCast (algebraMap ℚ_[p] Ω), PadicAlgCl.norm_extends]

lemma norm_natCast_eq_one {N : ℕ} (h : ¬ p ∣ N) : ‖(N : Ω)‖ = 1 := by
  rw [norm_natCast, Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd hp.out).mpr h

lemma inv_p_le_norm_natCast {N : ℕ} (hN : N ≠ 0) (h : ¬ p ^ 2 ∣ N) : (p : ℝ)⁻¹ ≤ ‖(N : Ω)‖ := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  by_cases hd : p ∣ N
  · obtain ⟨u, rfl⟩ := hd
    have hu : ¬ p ∣ u := by
      rintro ⟨v, rfl⟩
      exact h ⟨v, by ring⟩
    rw [Nat.cast_mul, norm_mul, norm_natCast_eq_one p hu, mul_one, norm_natCast, Padic.norm_p]
  · rw [norm_natCast_eq_one p hd]
    exact inv_le_one_of_one_le₀ hp1

lemma norm_natCast_pos {N : ℕ} (hN : N ≠ 0) : 0 < ‖(N : Ω)‖ := by
  rw [norm_pos_iff]
  exact_mod_cast hN

lemma norm_multiset_sum_le (t : Multiset Ω) (B : ℝ) (hB : 0 ≤ B) (h : ∀ x ∈ t, ‖x‖ ≤ B) :
    ‖t.sum‖ ≤ B := by
  induction t using Multiset.induction with
  | empty => simpa using hB
  | cons a t ih =>
    rw [Multiset.sum_cons]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · exact h a (Multiset.mem_cons_self a t)
    · exact ih fun x hx => h x (Multiset.mem_cons_of_mem hx)

lemma norm_multiset_prod_le (t : Multiset Ω) (δ : ℝ) (hδ : 0 ≤ δ) (h : ∀ x ∈ t, ‖x‖ ≤ δ) :
    ‖t.prod‖ ≤ δ ^ t.card := by
  induction t using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.prod_cons, Multiset.card_cons, norm_mul, pow_succ, mul_comm (δ ^ _)]
    refine mul_le_mul (h a (Multiset.mem_cons_self a t)) (ih fun x hx => h x
      (Multiset.mem_cons_of_mem hx))
      (norm_nonneg _) hδ

lemma norm_multiset_prod_eq (t : Multiset Ω) : ‖t.prod‖ = (t.map fun x => ‖x‖).prod := by
  induction t using Multiset.induction with
  | empty => simp
  | cons a t ih => rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, norm_mul, ih]

lemma norm_esymm_le (s : Multiset Ω) (δ : ℝ) (hδ : 0 ≤ δ) (h : ∀ x ∈ s, ‖x‖ ≤ δ) (m : ℕ) :
    ‖((s.powersetCard m).map Multiset.prod).sum‖ ≤ δ ^ m := by
  refine norm_multiset_sum_le p _ _ (pow_nonneg hδ m) ?_
  intro x hx
  rw [Multiset.mem_map] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  rw [Multiset.mem_powersetCard] at hu
  rw [← hu.2]
  exact norm_multiset_prod_le p u δ hδ fun y hy => h y (Multiset.mem_of_le hu.1 hy)

lemma pow_card_le_prod_of_le (t : Multiset ℝ) (a : ℝ) (ha : 0 ≤ a) (h : ∀ x ∈ t, a ≤ x) :
    a ^ t.card ≤ t.prod := by
  induction t using Multiset.induction with
  | empty => simp
  | cons b t ih =>
    rw [Multiset.prod_cons, Multiset.card_cons, pow_succ, mul_comm]
    have hb := h b (Multiset.mem_cons_self b t)
    refine mul_le_mul hb (ih fun x hx => h x (Multiset.mem_cons_of_mem hx)) (pow_nonneg ha _)
      (ha.trans hb)

lemma taylor_multiset_prod (r : Ω) (t : Multiset (Polynomial (PadicAlgCl p))) :
    taylor r t.prod = (t.map fun q => taylor r q).prod := by
  induction t using Multiset.induction with
  | empty => simp [taylor_one]
  | cons a t ih => rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, taylor_mul, ih]

lemma taylor_prod_X_sub_C (r : Ω) (s : Multiset Ω) :
    taylor r ((s.map fun a => X - C a).prod) = ((s.map fun a => a - r).map fun a => X - C a).prod
      := by
  rw [taylor_multiset_prod, Multiset.map_map, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun a _ => ?_
  simp only [Function.comp_apply, map_sub, taylor_X, taylor_C, C_sub]
  ring

lemma hasseDeriv_map {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S) (k : ℕ)
    (f : R[X]) : hasseDeriv k (f.map φ) = (hasseDeriv k f).map φ := by
  ext n
  simp [hasseDeriv_coeff, coeff_map]

theorem key (f : (Polynomial (PadicAlgCl p))) (hf : f.Monic) (α : Ω) (δ : ℝ) (hδ : 0 ≤ δ)
    (hroots : ∀ β ∈ f.roots, ‖β - α‖ ≤ δ) (j : ℕ) (hj : j < f.natDegree)
    (hN : (f.natDegree.choose j : Ω) ≠ 0) :
    ∃ β ∈ (hasseDeriv j f).roots,
      ‖β - α‖ ^ (f.natDegree - j) ≤ δ ^ (f.natDegree - j) / ‖(f.natDegree.choose j : Ω)‖ := by
  classical
  set n := f.natDegree with hn
  set m := n - j with hm
  have hm0 : m ≠ 0 := by omega
  have hmj : m + j = n := by omega

  have hsplit : f = (f.roots.map fun a => X - C a).prod :=
    (IsAlgClosed.splits f).eq_prod_roots_of_monic hf
  have hcard : f.roots.card = n := ((IsAlgClosed.splits f).natDegree_eq_card_roots).symm
  set s : Multiset (PadicAlgCl p) := f.roots.map fun a => a - α with hs
  have hscard : s.card = n := by rw [hs, Multiset.card_map, hcard]
  have hsδ : ∀ x ∈ s, ‖x‖ ≤ δ := by
    intro x hx
    rw [hs, Multiset.mem_map] at hx
    obtain ⟨β, hβ, rfl⟩ := hx
    exact hroots β hβ

  have htaylor : taylor α f = (s.map fun a => X - C a).prod := by
    conv_lhs => rw [hsplit]
    rw [taylor_prod_X_sub_C]
  have hcoeff : (taylor α f).coeff j = (-1) ^ (n - j) * ((s.powersetCard (n - j)).map
    Multiset.prod).sum := by
    rw [htaylor, Multiset.prod_X_sub_C_coeff s (by rw [hscard]; omega), hscard]
    rfl
  set g := hasseDeriv j f with hg
  have heval_le : ‖g.eval α‖ ≤ δ ^ m := by
    rw [hg, ← taylor_coeff, hcoeff, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, ← hm]
    exact norm_esymm_le p s δ hδ hsδ m

  have hgcoeff : g.coeff m = (n.choose j : Ω) := by
    rw [hg, hasseDeriv_coeff, hmj]
    have : f.coeff n = 1 := hf.coeff_natDegree
    rw [this, mul_one]
  have hgdeg : g.natDegree = m := by
    refine le_antisymm ?_ (le_natDegree_of_ne_zero (by rw [hgcoeff]; exact hN))
    rw [hg, hm, hn]
    exact natDegree_hasseDeriv_le f j
  have hglead : g.leadingCoeff = (n.choose j : Ω) := by
    rw [leadingCoeff, hgdeg, hgcoeff]
  have hg0 : g ≠ 0 := by
    intro h0
    rw [h0, leadingCoeff_zero] at hglead
    exact hN hglead.symm
  have hgsplit : g = C (n.choose j : Ω) * (g.roots.map fun a => X - C a).prod := by
    rw [← hglead]
    exact (IsAlgClosed.splits g).eq_prod_roots
  have hgcard : g.roots.card = m := by
    rw [← hgdeg]; exact ((IsAlgClosed.splits g).natDegree_eq_card_roots).symm

  have hevalprod : g.eval α = (n.choose j : Ω) * (g.roots.map fun β => α - β).prod := by
    conv_lhs => rw [hgsplit]
    rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    congr 1
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun β _ => ?_)
    simp
  have hnormprod : ‖(n.choose j : Ω)‖ * (g.roots.map fun β => ‖α - β‖).prod ≤ δ ^ m := by
    have := heval_le
    rw [hevalprod, norm_mul, norm_multiset_prod_eq, Multiset.map_map] at this
    exact this

  have hne : g.roots.toFinset.Nonempty := by
    rw [Multiset.toFinset_nonempty, ← Multiset.card_pos, hgcard]
    exact Nat.pos_of_ne_zero hm0
  obtain ⟨β₀, hβ₀, hmin⟩ := Finset.exists_min_image g.roots.toFinset (fun β => ‖α - β‖) hne
  rw [Multiset.mem_toFinset] at hβ₀
  refine ⟨β₀, hβ₀, ?_⟩
  have hNpos : 0 < ‖(n.choose j : Ω)‖ := norm_pos_iff.mpr hN
  have hpow : ‖α - β₀‖ ^ m ≤ (g.roots.map fun β => ‖α - β‖).prod := by
    have := pow_card_le_prod_of_le (g.roots.map fun β => ‖α - β‖) ‖α - β₀‖ (norm_nonneg _)
      (by
        intro x hx
        rw [Multiset.mem_map] at hx
        obtain ⟨β, hβ, rfl⟩ := hx
        exact hmin β (Multiset.mem_toFinset.mpr hβ))
    rwa [Multiset.card_map, hgcard] at this
  rw [norm_sub_rev, le_div_iff₀ hNpos, mul_comm]
  exact (mul_le_mul_of_nonneg_left hpow hNpos.le).trans hnormprod

section Galois

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

scoped instance isAlgClosureK : IsAlgClosure K Ω :=
  ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ_[p]) K⟩

scoped instance normalK : Normal K Ω := IsAlgClosure.normal K Ω

lemma isIntegralK (α : Ω) : IsIntegral K α :=
  (Algebra.IsAlgebraic.isAlgebraic (R := K) α).isIntegral

lemma roots_minpoly_norm_sub_le (α : Ω) (δ : ℝ)
    (h : ∀ σ : Γ, σ ∈ K.fixingSubgroup → ‖σ α - α‖ ≤ δ) :
    ∀ β ∈ ((minpoly K α).map (algebraMap K Ω)).roots, ‖β - α‖ ≤ δ := by
  intro β hβ
  have hint := isIntegralK p K α
  have hmon : ((minpoly K α).map (algebraMap K Ω)).Monic := (minpoly.monic hint).map _
  rw [mem_roots hmon.ne_zero, IsRoot.def, eval_map, ← aeval_def] at hβ
  have hmin : minpoly K α = minpoly K β :=
    minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hβ (minpoly.monic hint)
  have horb : β ∈ MulAction.orbit (Ω ≃ₐ[K] Ω) α :=
    (Normal.minpoly_eq_iff_mem_orbit Ω).mp hmin.symm
  obtain ⟨τ, hτ⟩ := horb
  set σ : Γ := τ.restrictScalars ℚ_[p] with hσ
  have hσK : σ ∈ K.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    change τ x = x
    exact τ.commutes ⟨x, hx⟩
  have hσα : σ α = β := hτ
  rw [← hσα]
  exact h σ hσK

lemma natDegree_minpoly_le_of_mem_roots_hasseDeriv (α : Ω) (j : ℕ)
    (hj : j < (minpoly K α).natDegree)
    (β : Ω) (hβ : β ∈ (hasseDeriv j ((minpoly K α).map (algebraMap K Ω))).roots) :
    (minpoly K β).natDegree ≤ (minpoly K α).natDegree - j := by
  set gK := hasseDeriv j (minpoly K α) with hgK
  have hmap : hasseDeriv j ((minpoly K α).map (algebraMap K Ω)) = gK.map (algebraMap K Ω) :=
    hasseDeriv_map _ _ _
  have hint := isIntegralK p K α

  have hcoeff : gK.coeff ((minpoly K α).natDegree - j) = ((minpoly K α).natDegree.choose j : K) :=
    by
    rw [hgK, hasseDeriv_coeff, Nat.sub_add_cancel hj.le, (minpoly.monic hint).coeff_natDegree,
      mul_one]
  have hgK0 : gK ≠ 0 := by
    intro h0
    have := hcoeff
    rw [h0, coeff_zero] at this
    have hc : ((minpoly K α).natDegree.choose j : K) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hj.le).ne'
    exact hc this.symm
  have hmap0 : gK.map (algebraMap K Ω) ≠ 0 := by
    rwa [Ne, Polynomial.map_eq_zero]
  rw [hmap, mem_roots hmap0, IsRoot.def, eval_map, ← aeval_def] at hβ
  have hdeg := minpoly.degree_le_of_ne_zero K β hgK0 hβ
  refine (natDegree_le_natDegree hdeg).trans ?_
  rw [hgK]
  exact natDegree_hasseDeriv_le _ _

lemma norm_conj_sub_le (α β : Ω) (δ ε : ℝ)
    (h : ∀ σ : Γ, σ ∈ K.fixingSubgroup → ‖σ α - α‖ ≤ δ) (hβ : ‖β - α‖ ≤ ε) (hδε : δ ≤ ε) :
    ∀ σ : Γ, σ ∈ K.fixingSubgroup → ‖σ β - β‖ ≤ ε := by
  intro σ hσ
  have hsplit : σ β - β = σ (β - α) + ((σ α - α) + (α - β)) := by
    rw [map_sub]; abel
  rw [hsplit]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_algEquiv]; exact hβ
  · refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((h σ hσ).trans hδε) ?_)
    rw [norm_sub_rev]; exact hβ

end Galois

lemma choose_prime_pow_modEq (L : ℕ) : ∀ n : ℕ, n.choose (p ^ L) ≡ n / p ^ L [MOD p] := by
  induction L with
  | zero => intro n; rw [pow_zero, Nat.choose_one_right, Nat.div_one]
  | succ L ih =>
    intro n
    have h1 := @Choose.choose_modEq_choose_mod_mul_choose_div_nat n (p ^ (L + 1)) p hp
    have hk : p ^ (L + 1) % p = 0 := by
      rw [pow_succ]; exact Nat.mul_mod_left _ _
    have hk' : p ^ (L + 1) / p = p ^ L := by
      rw [pow_succ, Nat.mul_div_cancel _ hp.out.pos]
    rw [hk, hk', Nat.choose_zero_right, one_mul] at h1
    refine h1.trans ?_
    have := ih (n / p)
    rwa [Nat.div_div_eq_div_mul, mul_comm, ← pow_succ] at this

lemma not_dvd_choose_prime_pow {n L : ℕ} (h1 : p ^ L ≤ n) (h2 : n < p ^ (L + 1)) :
    ¬ p ∣ n.choose (p ^ L) := by
  intro hd
  have hmod := choose_prime_pow_modEq p L n
  have hq1 : 1 ≤ n / p ^ L := (Nat.le_div_iff_mul_le (pow_pos hp.out.pos L)).mpr (by simpa using h1)
  have hq2 : n / p ^ L < p := by
    rw [Nat.div_lt_iff_lt_mul (pow_pos hp.out.pos L)]
    calc n < p ^ (L + 1) := h2
      _ = p * p ^ L := by rw [pow_succ, mul_comm]
  have h0 : n.choose (p ^ L) % p = 0 := Nat.eq_zero_of_dvd_of_lt hd |> fun _ =>
    Nat.mod_eq_zero_of_dvd hd
  have : (n / p ^ L) % p = 0 := by
    have := hmod
    rw [Nat.ModEq, h0] at this
    exact this.symm
  rw [Nat.mod_eq_of_lt hq2] at this
  omega

lemma not_sq_dvd_choose_prime_pow_pred {L : ℕ} (hL : 1 ≤ L) :
    ¬ p ^ 2 ∣ (p ^ L).choose (p ^ (L - 1)) := by
  have hprime : Prime p := Nat.prime_iff.mp hp.out
  have hk : p ^ (L - 1) ≤ p ^ L := Nat.pow_le_pow_right hp.out.pos (Nat.sub_le L 1)
  have hk0 : p ^ (L - 1) ≠ 0 := (pow_pos hp.out.pos _).ne'
  have hem := Nat.Prime.emultiplicity_choose_prime_pow hp.out hk hk0
  rw [multiplicity_pow_self_of_prime hprime] at hem
  have hL1 : L - (L - 1) = 1 := by omega
  rw [hL1] at hem
  have := (emultiplicity_eq_coe.mp hem).2
  simpa using this

noncomputable def E (n : ℕ) : ℝ := ∑ i ∈ Finset.range (Nat.log p n), ((p : ℝ)⁻¹) ^ i

noncomputable def B (n : ℕ) : ℝ := (p : ℝ) ^ (E p n)

lemma one_le_p : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le

lemma p_pos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos

lemma E_nonneg (n : ℕ) : 0 ≤ E p n :=
  Finset.sum_nonneg fun i _ => pow_nonneg (inv_nonneg.mpr (p_pos p).le) i

lemma E_mono {m n : ℕ} (h : m ≤ n) : E p m ≤ E p n := by
  unfold E
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.log_mono_right h)) ?_
  intro i _ _
  exact pow_nonneg (inv_nonneg.mpr (p_pos p).le) i

lemma E_le_two (n : ℕ) : E p n ≤ 2 := by
  unfold E
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (sum_geometric_two_le (Nat.log p n))
  rw [one_div]
  refine pow_le_pow_left₀ (inv_nonneg.mpr (p_pos p).le) ?_ i
  refine inv_anti₀ (by norm_num) ?_
  exact_mod_cast hp.out.two_le

lemma E_pow_succ (L : ℕ) : E p (p ^ (L + 1)) = E p (p ^ L) + ((p : ℝ)⁻¹) ^ L := by
  unfold E
  rw [Nat.log_pow hp.out.one_lt, Nat.log_pow hp.out.one_lt, Finset.sum_range_succ]

lemma one_le_B (n : ℕ) : 1 ≤ B p n := Real.one_le_rpow (one_le_p p) (E_nonneg p n)

lemma B_pos (n : ℕ) : 0 < B p n := lt_of_lt_of_le one_pos (one_le_B p n)

lemma B_mono {m n : ℕ} (h : m ≤ n) : B p m ≤ B p n :=
  Real.rpow_le_rpow_of_exponent_le (one_le_p p) (E_mono p h)

lemma B_le_sq (n : ℕ) : B p n ≤ (p : ℝ) ^ 2 := by
  have := Real.rpow_le_rpow_of_exponent_le (one_le_p p) (E_le_two p n)
  rw [B]
  refine this.trans_eq ?_
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

lemma B_pow_succ (L : ℕ) : B p (p ^ (L + 1)) = B p (p ^ L) * (p : ℝ) ^ (((p : ℝ)⁻¹) ^ L) := by
  rw [B, E_pow_succ, Real.rpow_add (p_pos p), B]

theorem main (n : ℕ) : ∀ (K : IntermediateField ℚ_[p] Ω) (α : Ω) (δ : ℝ),
    (minpoly K α).natDegree ≤ n →
    (∀ σ : Γ, σ ∈ K.fixingSubgroup → ‖σ α - α‖ ≤ δ) →
      ∃ a ∈ K, ‖α - a‖ ≤ B p n * δ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K α δ hdeg hconj
    have hδ : 0 ≤ δ := by
      have := hconj 1 (Subgroup.one_mem _)
      simpa using this
    have hint := isIntegralK p K α
    set n₀ := (minpoly K α).natDegree with hn₀
    have hn₀pos : 0 < n₀ := minpoly.natDegree_pos hint

    by_cases h1 : n₀ = 1
    · have hα : α ∈ (algebraMap K Ω).range := minpoly.natDegree_eq_one_iff.mp h1
      obtain ⟨a, ha⟩ := hα
      refine ⟨(a : Ω), a.2, ?_⟩
      have : (a : Ω) = α := ha
      rw [this, sub_self, norm_zero]
      exact mul_nonneg (B_pos p n).le hδ
    have hn₀2 : 2 ≤ n₀ := by omega

    set L := Nat.log p n₀ with hL
    have hpL : p ^ L ≤ n₀ := Nat.pow_log_le_self p (by omega)
    have hn₀lt : n₀ < p ^ (L + 1) := Nat.lt_pow_succ_log_self hp.out.one_lt n₀

    set f : (Polynomial (PadicAlgCl p)) := (minpoly K α).map (algebraMap K Ω) with hf
    have hfmon : f.Monic := (minpoly.monic hint).map _
    have hfdeg : f.natDegree = n₀ := (minpoly.monic hint).natDegree_map _
    have hroots : ∀ β ∈ f.roots, ‖β - α‖ ≤ δ := roots_minpoly_norm_sub_le p K α δ hconj

    have cont : ∀ (m : ℕ) (Λ : ℝ), 0 < m → m < n₀ → 1 ≤ Λ →
        (n₀.choose (n₀ - m) : Ω) ≠ 0 →
        (‖(n₀.choose (n₀ - m) : Ω)‖)⁻¹ ≤ Λ ^ m →
        B p m * Λ ≤ B p n₀ →
        ∃ a ∈ K, ‖α - a‖ ≤ B p n * δ := by
      intro m Λ hm0 hmn hΛ1 hN hNΛ hBΛ
      set j := n₀ - m with hj
      have hjlt : j < f.natDegree := by rw [hfdeg]; omega
      have hmj : f.natDegree - j = m := by rw [hfdeg]; omega
      have hNf : (f.natDegree.choose j : Ω) ≠ 0 := by rw [hfdeg]; exact hN
      obtain ⟨β, hβ, hβle⟩ := key p f hfmon α δ hδ hroots j hjlt hNf
      rw [hmj, hfdeg] at hβle

      have hβΛ : ‖β - α‖ ≤ Λ * δ := by
        have hΛδ : 0 ≤ Λ * δ := mul_nonneg (zero_le_one.trans hΛ1) hδ
        refine le_of_pow_le_pow_left₀ hm0.ne' hΛδ ?_
        refine hβle.trans ?_
        rw [div_eq_mul_inv, mul_pow, mul_comm]
        exact mul_le_mul_of_nonneg_right hNΛ (pow_nonneg hδ m)

      have hβdeg : (minpoly K β).natDegree ≤ m := by
        have := natDegree_minpoly_le_of_mem_roots_hasseDeriv p K α j (by omega) β
          (by rw [← hf]; exact hβ)
        omega

      have hβconj := norm_conj_sub_le p K α β δ (Λ * δ) hconj hβΛ
        (by nlinarith [hδ, hΛ1])

      have hmn' : m < n := lt_of_lt_of_le hmn hdeg
      obtain ⟨a, haK, ha⟩ := ih m hmn' K β (Λ * δ) hβdeg hβconj
      refine ⟨a, haK, ?_⟩
      have hsplit : α - a = (α - β) + (β - a) := by abel
      rw [hsplit]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_sub_rev]
        refine hβΛ.trans ?_
        have : Λ ≤ B p n := by
          have h1 : Λ ≤ B p m * Λ := le_mul_of_one_le_left (zero_le_one.trans hΛ1) (one_le_B p m)
          exact h1.trans (hBΛ.trans (B_mono p hdeg))
        exact mul_le_mul_of_nonneg_right this hδ
      · refine ha.trans ?_
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hBΛ.trans (B_mono p hdeg)) hδ
    by_cases hcase : p ^ L < n₀
    ·
      refine cont (p ^ L) 1 (pow_pos hp.out.pos L) hcase le_rfl ?_ ?_ ?_
      · rw [Nat.choose_symm hpL]
        have h := not_dvd_choose_prime_pow p hpL hn₀lt
        intro h0
        have h1 : ‖((n₀.choose (p ^ L) : ℕ) : Ω)‖ = 1 := norm_natCast_eq_one p h
        rw [h0, norm_zero] at h1
        exact zero_ne_one h1
      · rw [Nat.choose_symm hpL, norm_natCast_eq_one p (not_dvd_choose_prime_pow p hpL hn₀lt),
          inv_one, one_pow]
      · rw [mul_one]; exact B_mono p hpL
    ·
      have hn₀eq : n₀ = p ^ L := le_antisymm (not_lt.mp hcase) hpL
      have hL1 : 1 ≤ L := by
        by_contra hL0
        push Not at hL0
        have : L = 0 := by omega
        rw [this, pow_zero] at hn₀eq
        omega
      set m := p ^ (L - 1) with hm
      have hm0 : 0 < m := pow_pos hp.out.pos _
      have hmn : m < n₀ := by
        rw [hn₀eq, hm]
        exact Nat.pow_lt_pow_right hp.out.one_lt (by omega)
      have hmle : m ≤ n₀ := hmn.le
      have hNnat : ¬ p ^ 2 ∣ n₀.choose m := by
        rw [hn₀eq, hm]; exact not_sq_dvd_choose_prime_pow_pred p hL1
      have hNne : n₀.choose m ≠ 0 := (Nat.choose_pos hmle).ne'
      set Λ : ℝ := (p : ℝ) ^ ((m : ℝ)⁻¹) with hΛ
      have hΛ1 : 1 ≤ Λ := Real.one_le_rpow (one_le_p p) (by positivity)
      refine cont m Λ hm0 hmn hΛ1 ?_ ?_ ?_
      · rw [Nat.choose_symm hmle]
        exact_mod_cast hNne
      · rw [Nat.choose_symm hmle]
        have hle := inv_p_le_norm_natCast p hNne hNnat
        have hΛm : Λ ^ m = p := by
          rw [hΛ]; exact Real.rpow_inv_natCast_pow (p_pos p).le hm0.ne'
        rw [hΛm]
        rw [inv_le_comm₀ (norm_natCast_pos p hNne) (p_pos p)]
        exact hle
      ·
        have hL' : L = (L - 1) + 1 := by omega
        have hΛ' : Λ = (p : ℝ) ^ (((p : ℝ)⁻¹) ^ (L - 1)) := by
          rw [hΛ, hm]
          congr 1
          rw [Nat.cast_pow, ← inv_pow]
        rw [hn₀eq, hL', B_pow_succ, hΛ']

end ApproxBySubfield

namespace PadicAlgCl

/-- Approximation in a fixed subfield: an element of the algebraic
closure moved only slightly by every automorphism fixing `K` is
approximated, up to a constant independent of the element, by an
element of `K`. -/
public theorem exists_mem_intermediateField_norm_sub_le_mul_of_forall_norm_algEquiv_sub_le
    (p : ℕ) [Fact p.Prime] :
    ∃ c : ℝ, 0 < c ∧
      ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (α : PadicAlgCl p) (δ : ℝ),
        (∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ K.fixingSubgroup → ‖σ α - α‖ ≤ δ) →
          ∃ a ∈ K, ‖α - a‖ ≤ c * δ := by
  refine ⟨(p : ℝ) ^ 2, pow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) 2, ?_⟩
  intro K α δ h
  have hδ : 0 ≤ δ := by
    have := h 1 (Subgroup.one_mem _)
    simpa using this
  obtain ⟨a, haK, ha⟩ := ApproxBySubfield.main p ((minpoly K α).natDegree) K α δ le_rfl h
  exact ⟨a, haK, ha.trans (mul_le_mul_of_nonneg_right (ApproxBySubfield.B_le_sq p _) hδ)⟩

end PadicAlgCl

namespace FixedClosure


open UniformSpace

variable (p : ℕ) [Fact p.Prime]

local notation "Γ" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)

theorem smul_eq_self_of_mem_closure (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (x : ℂ_[p])
    (hx : x ∈ closure (Set.range fun k : K => ((k : PadicAlgCl p) : ℂ_[p])))
    (σ : Γ) (hσ : σ ∈ K.fixingSubgroup) : σ • x = x := by
  have hclosed : IsClosed {y : ℂ_[p] | σ • y = y} :=
    isClosed_eq (PadicComplex.continuous_smul_left p σ) continuous_id
  have hsub : (Set.range fun k : K => ((k : PadicAlgCl p) : ℂ_[p])) ⊆ {y : ℂ_[p] | σ • y = y} := by
    rintro _ ⟨k, rfl⟩
    show σ • ((k : PadicAlgCl p) : ℂ_[p]) = ((k : PadicAlgCl p) : ℂ_[p])
    rw [PadicComplex.smul_coe]
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
    rw [hσ _ k.2]
  exact closure_minimal hsub hclosed hx

theorem norm_algEquiv_sub_le (x : ℂ_[p]) (σ : Γ) (hσx : σ • x = x) (α : PadicAlgCl p) :
    ‖σ α - α‖ ≤ ‖x - (α : ℂ_[p])‖ := by
  have h1 : ((σ α - α : PadicAlgCl p) : ℂ_[p]) =
      σ • ((α : ℂ_[p]) - x) + (x - (α : ℂ_[p])) := by
    rw [Completion.coe_sub, ← PadicComplex.smul_coe, smul_sub, hσx]
    abel
  rw [← PadicComplex.norm_extends p (σ α - α), h1]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
  rw [PadicComplex.norm_smul_eq, ← norm_neg ((α : ℂ_[p]) - x), neg_sub, max_self]

theorem mem_closure_of_forall_smul_eq_self (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (x : ℂ_[p]) (hx : ∀ σ : Γ, σ ∈ K.fixingSubgroup → σ • x = x) :
    x ∈ closure (Set.range fun k : K => ((k : PadicAlgCl p) : ℂ_[p])) := by
  obtain ⟨c, hc, hAx⟩ :=
    PadicAlgCl.exists_mem_intermediateField_norm_sub_le_mul_of_forall_norm_algEquiv_sub_le p
  rw [Metric.mem_closure_iff]
  intro ε hε

  set ε' : ℝ := ε / (2 * (1 + c)) with hε'
  have hε'pos : 0 < ε' := by
    rw [hε']; positivity
  have hdense := (Metric.denseRange_iff.mp (Completion.denseRange_coe (α := PadicAlgCl p))) x ε'
    hε'pos
  obtain ⟨α, hα⟩ := hdense
  have hα' : ‖x - (α : ℂ_[p])‖ < ε' := by rwa [← dist_eq_norm]

  have hconj : ∀ σ : Γ, σ ∈ K.fixingSubgroup → ‖σ α - α‖ ≤ ε' := fun σ hσ =>
    (norm_algEquiv_sub_le p x σ (hx σ hσ) α).trans hα'.le
  obtain ⟨a, haK, ha⟩ := hAx K α ε' hconj
  refine ⟨((a : PadicAlgCl p) : ℂ_[p]), ⟨⟨a, haK⟩, rfl⟩, ?_⟩

  have h2 : ‖(α : ℂ_[p]) - ((a : PadicAlgCl p) : ℂ_[p])‖ ≤ c * ε' := by
    rw [← Completion.coe_sub, PadicComplex.norm_extends]
    exact ha
  have hsplit : x - ((a : PadicAlgCl p) : ℂ_[p]) =
      (x - (α : ℂ_[p])) + ((α : ℂ_[p]) - ((a : PadicAlgCl p) : ℂ_[p])) := by abel
  rw [dist_eq_norm, hsplit]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) ?_
  refine max_lt (hα'.trans ?_) (h2.trans_lt ?_)
  · rw [hε', div_lt_iff₀ (by positivity)]
    nlinarith
  · rw [hε', mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith

end FixedClosure

namespace PadicComplex

/-- An element of `ℂ_[p]` is fixed by every automorphism fixing `K`
if and only if it lies in the closure of the image of `K`. -/
public theorem forall_smul_eq_self_iff_mem_closure
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (x : ℂ_[p]) :
    (∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ K.fixingSubgroup → σ • x = x) ↔
      x ∈ closure (Set.range fun k : K => ((k : PadicAlgCl p) : ℂ_[p])) :=
  ⟨FixedClosure.mem_closure_of_forall_smul_eq_self p K x,
    fun hx σ hσ => FixedClosure.smul_eq_self_of_mem_closure p K x hx σ hσ⟩

end PadicComplex

namespace TateTraceExist


open UniformSpace
open scoped Pointwise

variable {p : ℕ} [Fact p.Prime]

local notation "Ω" => PadicAlgCl p
local notation "Γ" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)

section A

variable (p)
variable (Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p))

def IsGen (n : ℕ) (σ : Γ) : Prop := σ ∈ (Km n).fixingSubgroup ∧ σ ∉ (Km (n + 1)).fixingSubgroup

variable {Km}

lemma apply_eq_of_mem_fixingSubgroup {n : ℕ} {σ : Γ} (hσ : σ ∈ (Km n).fixingSubgroup) {y : Ω}
    (hy : y ∈ Km n) : σ y = y :=
  (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ y hy

lemma pow_apply_eq_of_mem_fixingSubgroup {n : ℕ} {σ : Γ} (hσ : σ ∈ (Km n).fixingSubgroup)
    (i : ℕ) {y : Ω} (hy : y ∈ Km n) : (σ ^ i) y = y :=
  apply_eq_of_mem_fixingSubgroup p (Subgroup.pow_mem _ hσ i) hy

variable (hmono : Monotone Km)
  (hcyc : ∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), σ ∈ (Km m).fixingSubgroup →
    σ ∉ (Km (m + 1)).fixingSubgroup →
      σ ^ p ∈ (Km (m + 1)).fixingSubgroup ∧ σ ^ p ∉ (Km (m + 2)).fixingSubgroup)

include hcyc in
lemma isGen_pow (n : ℕ) (σ : Γ) (hσ : IsGen p Km n σ) (k : ℕ) :
    IsGen p Km (n + k) (σ ^ (p ^ k)) := by
  induction k with
  | zero => simpa using hσ
  | succ k ih =>
      have h := hcyc (n + k) _ ih.1 ih.2
      refine ⟨?_, ?_⟩
      · rw [pow_succ, pow_mul]; exact h.1
      · rw [pow_succ, pow_mul]
        have : n + (k + 1) + 1 = n + k + 2 := by ring
        rw [this]; exact h.2

include hcyc in

lemma pow_mem_fixingSubgroup_succ_iff (n : ℕ) (σ : Γ) (hσ : IsGen p Km n σ) (i : ℕ) :
    σ ^ i ∈ (Km (n + 1)).fixingSubgroup ↔ p ∣ i := by
  constructor
  · intro hi
    by_contra hpi
    have hcop : Nat.Coprime i p := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd
      Fact.out).mpr hpi))

    obtain ⟨a, ha⟩ : ∃ a : ℕ, i * a % p = 1 := by
      have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
      obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp1
      exact ⟨a, ha⟩
    have hdiv : a * i = p * (a * i / p) + 1 := by
      have := Nat.div_add_mod (a * i) p
      rw [mul_comm] at ha
      omega
    apply hσ.2
    have h1 : σ ^ (a * i) ∈ (Km (n + 1)).fixingSubgroup := by
      rw [mul_comm, pow_mul]; exact Subgroup.pow_mem _ hi a
    have h2 : σ ^ (p * (a * i / p)) ∈ (Km (n + 1)).fixingSubgroup := by
      rw [pow_mul]; exact Subgroup.pow_mem _ (hcyc n σ hσ.1 hσ.2).1 _
    rw [hdiv, pow_add, pow_one] at h1
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ h2) h1
    simpa using this
  · rintro ⟨k, rfl⟩
    rw [pow_mul]
    exact Subgroup.pow_mem _ (hcyc n σ hσ.1 hσ.2).1 k

lemma sum_range_add_of_periodic {M : Type*} [AddCommMonoid M] (f : ℕ → M) (P : ℕ)
    (hf : ∀ i, f (i + P) = f i) (j : ℕ) :
    ∑ i ∈ Finset.range P, f (i + j) = ∑ i ∈ Finset.range P, f i := by
  induction j with
  | zero => simp
  | succ j ih =>
      have h1 : ∑ i ∈ Finset.range P, f (i + (j + 1)) = ∑ i ∈ Finset.range P, f (i + 1 + j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1; ring
      rw [h1]

      set g : ℕ → M := fun i => f (i + j) with hg
      have hgp : ∀ i, g (i + P) = g i := fun i => by
        simp only [hg]
        rw [show i + P + j = i + j + P by ring, hf]
      have h2 : ∑ i ∈ Finset.range P, f (i + 1 + j) = ∑ i ∈ Finset.range P, g (i + 1) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hg]
      rw [h2, ← ih]
      show ∑ i ∈ Finset.range P, g (i + 1) = ∑ i ∈ Finset.range P, g i
      rcases Nat.eq_zero_or_pos P with hP | hP
      · subst hP; simp
      · obtain ⟨Q, rfl⟩ : ∃ Q, P = Q + 1 := ⟨P - 1, by omega⟩
        rw [Finset.sum_range_succ, Finset.sum_range_succ' g]
        have h0 := hgp 0
        rw [zero_add] at h0
        rw [h0]

lemma norm_algEquiv (σ : Γ) (z : Ω) : ‖σ z‖ = ‖z‖ :=
  (spectralNorm_eq_of_equiv σ z).symm

lemma norm_algEquiv_sub (σ : Γ) (z w : Ω) : ‖σ z - σ w‖ = ‖z - w‖ := by
  rw [← map_sub, norm_algEquiv]

lemma norm_pow_apply_sub_le (σ : Γ) (z : Ω) (N : ℕ) : ‖(σ ^ N) z - z‖ ≤ ‖σ z - z‖ := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hrw : (σ ^ (N + 1)) z - z = (σ ((σ ^ N) z) - σ z) + (σ z - z) := by
        rw [pow_succ', AlgEquiv.mul_apply]; abel
      rw [hrw]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
      rw [norm_algEquiv_sub]; exact ih

variable (hfin : ∀ m, FiniteDimensional ℚ_[p] (Km m))
  (hdeg : ∀ m n : ℕ, n = m + 1 → Module.finrank ℚ_[p] (Km n) = p * Module.finrank ℚ_[p] (Km m))
  (hstab : ∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), σ ∈ (Km 0).fixingSubgroup →
    ∀ y ∈ Km m, σ y ∈ Km m)

lemma index_eq (n : ℕ) : (Km n).fixingSubgroup.index = Module.finrank ℚ_[p] (Km n) :=
  (IntermediateField.finrank_eq_fixingSubgroup_index _ (Km n)).symm

include hfin in
lemma index_ne_zero (n : ℕ) : (Km n).fixingSubgroup.index ≠ 0 := by
  haveI := hfin n
  rw [index_eq p]
  exact Module.finrank_pos.ne'

include hfin hdeg hmono in
lemma relIndex_eq (n : ℕ) :
    (Km (n + 1)).fixingSubgroup.relIndex (Km n).fixingSubgroup = p := by
  have hle : (Km (n + 1)).fixingSubgroup ≤ (Km n).fixingSubgroup :=
    IntermediateField.fixingSubgroup_le (hmono (Nat.le_succ n))
  have h := Subgroup.relIndex_mul_index hle
  rw [index_eq p, index_eq p, hdeg n (n + 1) rfl] at h
  have hpos : Module.finrank ℚ_[p] (Km n) ≠ 0 := by
    haveI := hfin n
    exact Module.finrank_pos.ne'
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hpos) h

include hfin hdeg hmono in

lemma exists_isGen (n : ℕ) : ∃ σ : Γ, IsGen p Km n σ := by
  have h := relIndex_eq p hmono hfin hdeg n
  have hne : ¬ (Km n).fixingSubgroup ≤ (Km (n + 1)).fixingSubgroup := by
    intro hle
    rw [← Subgroup.relIndex_eq_one] at hle
    rw [hle] at h
    exact (Fact.out : p.Prime).one_lt.ne h
  obtain ⟨σ, hσ, hσ'⟩ := SetLike.not_le_iff_exists.mp hne
  exact ⟨σ, hσ, hσ'⟩

include hcyc in
lemma zpow_mem_fixingSubgroup_succ_iff (n : ℕ) (σ : Γ) (hσ : IsGen p Km n σ) (z : ℤ) :
    σ ^ z ∈ (Km (n + 1)).fixingSubgroup ↔ (p : ℤ) ∣ z := by
  rcases Int.eq_nat_or_neg z with ⟨k, rfl | rfl⟩
  · rw [zpow_natCast, pow_mem_fixingSubgroup_succ_iff p hcyc n σ hσ, Int.natCast_dvd_natCast]
  · rw [zpow_neg, zpow_natCast, inv_mem_iff, pow_mem_fixingSubgroup_succ_iff p hcyc n σ hσ,
      Int.dvd_neg, Int.natCast_dvd_natCast]

include hfin hdeg hmono hcyc in

lemma exists_pow_inv_mul_mem (n : ℕ) (σ : Γ) (hσ : IsGen p Km n σ) (τ : Γ)
    (hτ : τ ∈ (Km n).fixingSubgroup) :
    ∃ i : ℕ, i < p ∧ (σ ^ i)⁻¹ * τ ∈ (Km (n + 1)).fixingSubgroup := by
  classical
  set H : Subgroup Γ := (Km n).fixingSubgroup with hH
  set H' : Subgroup Γ := (Km (n + 1)).fixingSubgroup with hH'
  set Q := H ⧸ H'.subgroupOf H with hQ
  have hcard : Nat.card Q = p := by
    have := relIndex_eq p hmono hfin hdeg n
    exact this
  haveI : Finite Q := Nat.finite_of_card_ne_zero (by rw [hcard]; exact (Fact.out : p.Prime).ne_zero)
  let s : H := ⟨σ, hσ.1⟩
  let f : Fin p → Q := fun i => QuotientGroup.mk (s ^ (i : ℕ))
  have hf : Function.Injective f := by
    intro i j hij
    have h1 : (s ^ (i : ℕ))⁻¹ * s ^ (j : ℕ) ∈ H'.subgroupOf H := QuotientGroup.eq.mp hij
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : ((s ^ (i : ℕ))⁻¹ * s ^ (j : ℕ) : H) = (s ^ ((j : ℤ) - (i : ℤ)) : H) := by
      rw [zpow_sub, zpow_natCast, zpow_natCast]
      exact (Commute.pow_pow_self s i j).inv_left.eq.trans (by group)
    rw [h2] at h1
    have h3 : (((s ^ ((j : ℤ) - (i : ℤ)) : H) : Γ)) = σ ^ ((j : ℤ) - (i : ℤ)) := by
      simp [s]
    rw [h3, zpow_mem_fixingSubgroup_succ_iff p hcyc n σ hσ] at h1
    have h4 : ((j : ℤ) - (i : ℤ)) = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd h1
      have hi := i.2; have hj := j.2
      rw [abs_lt]; constructor <;> omega
    exact Fin.ext (by omega)
  have hbij := hf.bijective_of_nat_card_le (by simp [hcard])
  obtain ⟨i, hi⟩ := hbij.2 (QuotientGroup.mk ⟨τ, hτ⟩)
  refine ⟨i, i.2, ?_⟩
  have h1 : (s ^ (i : ℕ))⁻¹ * ⟨τ, hτ⟩ ∈ H'.subgroupOf H := QuotientGroup.eq.mp hi
  rw [Subgroup.mem_subgroupOf] at h1
  simpa [s] using h1

include hfin hdeg hmono hcyc in

lemma exists_forall_apply_eq_pow_apply (m : ℕ) (σ : Γ) (hσ : IsGen p Km m σ) (k : ℕ) (τ : Γ)
    (hτ : τ ∈ (Km m).fixingSubgroup) :
    ∃ j : ℕ, ∀ y ∈ Km (m + k), τ y = (σ ^ j) y := by
  induction k with
  | zero =>
      refine ⟨0, fun y hy => ?_⟩
      rw [pow_zero, AlgEquiv.one_apply]
      exact apply_eq_of_mem_fixingSubgroup p (by simpa using hτ) hy
  | succ k ih =>
      obtain ⟨j, hj⟩ := ih
      set ρ : Γ := (σ ^ j)⁻¹ * τ with hρ
      have hρm : ρ ∈ (Km (m + k)).fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro y hy
        rw [hρ, AlgEquiv.mul_apply, hj y hy, ← AlgEquiv.mul_apply, inv_mul_cancel,
          AlgEquiv.one_apply]
      have hgen := isGen_pow p hcyc m σ hσ k
      obtain ⟨i, -, hi⟩ := exists_pow_inv_mul_mem p hmono hcyc hfin hdeg (m + k) _ hgen ρ hρm
      refine ⟨j + p ^ k * i, fun y hy => ?_⟩
      set ρ' : Γ := ((σ ^ p ^ k) ^ i)⁻¹ * ρ with hρ'
      have hτeq : τ = σ ^ j * ((σ ^ p ^ k) ^ i * ρ') := by
        rw [hρ', mul_inv_cancel_left, hρ, mul_inv_cancel_left]
      have hy' : ρ' y = y := apply_eq_of_mem_fixingSubgroup p hi (by
        have : m + (k + 1) = m + k + 1 := by ring
        rwa [this] at hy)
      rw [hτeq, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hy', ← pow_mul, ← AlgEquiv.mul_apply,
        ← pow_add]

include hfin hdeg hmono hcyc hstab in

lemma apply_comm (m n : ℕ) (hmn : m ≤ n) (τ τ' : Γ) (hτ : τ ∈ (Km m).fixingSubgroup)
    (hτ' : τ' ∈ (Km m).fixingSubgroup) (y : Ω) (hy : y ∈ Km n) : τ (τ' y) = τ' (τ y) := by
  obtain ⟨σ, hσ⟩ := exists_isGen p hmono hfin hdeg m
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  obtain ⟨j, hj⟩ := exists_forall_apply_eq_pow_apply p hmono hcyc hfin hdeg m σ hσ k τ hτ
  obtain ⟨j', hj'⟩ := exists_forall_apply_eq_pow_apply p hmono hcyc hfin hdeg m σ hσ k τ' hτ'
  have h0 : (Km m).fixingSubgroup ≤ (Km 0).fixingSubgroup :=
    IntermediateField.fixingSubgroup_le (hmono (Nat.zero_le m))
  have hσ0 : σ ∈ (Km 0).fixingSubgroup := h0 hσ.1
  have hy1 : (σ ^ j') y ∈ Km (m + k) := hstab _ _ (Subgroup.pow_mem _ hσ0 _) y hy
  have hy2 : (σ ^ j) y ∈ Km (m + k) := hstab _ _ (Subgroup.pow_mem _ hσ0 _) y hy
  rw [hj' y hy, hj _ hy1, hj y hy, hj' _ hy2, ← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply,
    ← pow_add, ← pow_add, add_comm]

include hfin hdeg hmono hcyc in

lemma norm_apply_sub_le_of_isGen (m n : ℕ) (hmn : m ≤ n) (σ : Γ) (hσ : IsGen p Km m σ) (τ : Γ)
    (hτ : τ ∈ (Km m).fixingSubgroup) (z : Ω) (hz : z ∈ Km n) : ‖τ z - z‖ ≤ ‖σ z - z‖ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  obtain ⟨j, hj⟩ := exists_forall_apply_eq_pow_apply p hmono hcyc hfin hdeg m σ hσ k τ hτ
  rw [hj z hz]
  exact norm_pow_apply_sub_le p σ z j

include hfin hdeg hmono hcyc hstab in

lemma sum_pow_apply_mem (n : ℕ) (σ : Γ) (hσ : IsGen p Km n σ) (y : Ω) (hy : y ∈ Km (n + 1)) :
    ∑ i ∈ Finset.range p, (σ ^ i) y ∈ Km n := by
  have hfix : ∀ ρ ∈ (Km n).fixingSubgroup, ρ (∑ i ∈ Finset.range p, (σ ^ i) y) =
      ∑ i ∈ Finset.range p, (σ ^ i) y := by
    intro ρ hρ
    obtain ⟨j, hj⟩ := exists_forall_apply_eq_pow_apply p hmono hcyc hfin hdeg n σ hσ 1 ρ hρ
    have h0 : (Km n).fixingSubgroup ≤ (Km 0).fixingSubgroup :=
      IntermediateField.fixingSubgroup_le (hmono (Nat.zero_le n))
    have hσ0 : σ ∈ (Km 0).fixingSubgroup := h0 hσ.1
    rw [map_sum]
    have h1 : ∀ i ∈ Finset.range p, ρ ((σ ^ i) y) = (σ ^ (i + j)) y := by
      intro i _
      rw [hj _ (hstab _ _ (Subgroup.pow_mem _ hσ0 _) y hy), ← AlgEquiv.mul_apply, ← pow_add,
        add_comm]
    rw [Finset.sum_congr rfl h1]
    apply sum_range_add_of_periodic (fun i => (σ ^ i) y) p
    intro i
    show (σ ^ (i + p)) y = (σ ^ i) y
    rw [pow_add, AlgEquiv.mul_apply, apply_eq_of_mem_fixingSubgroup p (hcyc n σ hσ.1 hσ.2).1 hy]
  have hmem : (∑ i ∈ Finset.range p, (σ ^ i) y) ∈
      IntermediateField.fixedField (Km n).fixingSubgroup := by
    rw [IntermediateField.mem_fixedField_iff]
    exact hfix
  rwa [InfiniteGalois.fixedField_fixingSubgroup] at hmem

end A

section B

variable (p)
variable {Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)}

def Ssum (σ : Γ) (k : ℕ) (y : Ω) : Ω := ∑ j ∈ Finset.range (p ^ k), (σ ^ j) y

def Nop (σ : Γ) (k : ℕ) (y : Ω) : Ω := ∑ a ∈ Finset.range p, ((σ ^ p ^ k) ^ a) y

def Top (σ : Γ) (k : ℕ) (y : Ω) : Ω := ((p : Ω) ^ k)⁻¹ * Ssum p σ k y

lemma natCast_p_ne_zero : (p : Ω) ≠ 0 := by
  exact_mod_cast (Fact.out : p.Prime).ne_zero

lemma norm_natCast_p : ‖(p : Ω)‖ = ‖(p : ℚ_[p])‖ := by
  rw [← map_natCast (algebraMap ℚ_[p] Ω) p, norm_algebraMap']

lemma norm_p_pos : 0 < ‖(p : ℚ_[p])‖ := by
  rw [Padic.norm_p]; have := (Fact.out : p.Prime).pos; positivity

@[scoped simp] lemma Ssum_add (σ : Γ) (k : ℕ) (y y' : Ω) :
    Ssum p σ k (y + y') = Ssum p σ k y + Ssum p σ k y' := by
  simp [Ssum, Finset.sum_add_distrib]

@[scoped simp] lemma Ssum_sub (σ : Γ) (k : ℕ) (y y' : Ω) :
    Ssum p σ k (y - y') = Ssum p σ k y - Ssum p σ k y' := by
  simp [Ssum, Finset.sum_sub_distrib]

@[scoped simp] lemma Nop_add (σ : Γ) (k : ℕ) (y y' : Ω) :
    Nop p σ k (y + y') = Nop p σ k y + Nop p σ k y' := by
  simp only [Nop, map_add, Finset.sum_add_distrib]

@[scoped simp] lemma Nop_sub (σ : Γ) (k : ℕ) (y y' : Ω) :
    Nop p σ k (y - y') = Nop p σ k y - Nop p σ k y' := by
  simp only [Nop, map_sub, Finset.sum_sub_distrib]

lemma pow_apply_of_apply_eq (σ : Γ) {a : Ω} (ha : σ a = a) (j : ℕ) : (σ ^ j) a = a := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, ha, ih]

lemma Ssum_mul_of_fixed (σ : Γ) (k : ℕ) (a y : Ω) (ha : σ a = a) :
    Ssum p σ k (a * y) = a * Ssum p σ k y := by
  simp only [Ssum, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_apply_of_apply_eq p σ ha j]

lemma Top_add (σ : Γ) (k : ℕ) (y y' : Ω) : Top p σ k (y + y') = Top p σ k y + Top p σ k y' := by
  simp [Top, mul_add]

lemma Top_mul_of_fixed (σ : Γ) (k : ℕ) (a y : Ω) (ha : σ a = a) :
    Top p σ k (a * y) = a * Top p σ k y := by
  simp only [Top, Ssum_mul_of_fixed p σ k a y ha]; ring

lemma sum_range_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n c : ℕ) :
    ∑ j ∈ Finset.range (n * c), f j = ∑ a ∈ Finset.range c, ∑ b ∈ Finset.range n, f (n * a + b) :=
      by
  induction c with
  | zero => simp
  | succ c ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

lemma Ssum_succ (σ : Γ) (k : ℕ) (y : Ω) : Ssum p σ (k + 1) y = Ssum p σ k (Nop p σ k y) := by
  simp only [Ssum, Nop]
  rw [pow_succ, sum_range_mul, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← AlgEquiv.mul_apply, ← pow_mul, ← pow_add, add_comm]

lemma Top_succ (σ : Γ) (k : ℕ) (y : Ω) :
    Top p σ (k + 1) y = Top p σ k ((p : Ω)⁻¹ * Nop p σ k y) := by
  have hp : σ ((p : Ω)⁻¹) = (p : Ω)⁻¹ := by rw [map_inv₀, map_natCast]
  rw [Top_mul_of_fixed p σ k _ _ hp]
  simp only [Top, Ssum_succ]
  rw [pow_succ]
  field_simp

variable (hcyc : ∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), σ ∈ (Km m).fixingSubgroup →
    σ ∉ (Km (m + 1)).fixingSubgroup →
      σ ^ p ∈ (Km (m + 1)).fixingSubgroup ∧ σ ^ p ∉ (Km (m + 2)).fixingSubgroup)
  (hmono : Monotone Km)
  (hfin : ∀ m, FiniteDimensional ℚ_[p] (Km m))
  (hdeg : ∀ m n : ℕ, n = m + 1 → Module.finrank ℚ_[p] (Km n) = p * Module.finrank ℚ_[p] (Km m))
  (hstab : ∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), σ ∈ (Km 0).fixingSubgroup →
    ∀ y ∈ Km m, σ y ∈ Km m)

include hcyc in

lemma Nop_eq_of_mem (m : ℕ) (σ : Γ) (hσ : IsGen p Km m σ) (k : ℕ) (y : Ω) (hy : y ∈ Km (m + k)) :
    Nop p σ k y = (p : Ω) * y := by
  have hgen := isGen_pow p hcyc m σ hσ k
  simp only [Nop]
  rw [Finset.sum_congr rfl fun a _ => pow_apply_eq_of_mem_fixingSubgroup p hgen.1 a hy]
  simp

include hcyc in

lemma Top_succ_of_mem (m : ℕ) (σ : Γ) (hσ : IsGen p Km m σ) (k : ℕ) (y : Ω)
    (hy : y ∈ Km (m + k)) : Top p σ (k + 1) y = Top p σ k y := by
  rw [Top_succ, Nop_eq_of_mem p hcyc m σ hσ k y hy, ← mul_assoc, inv_mul_cancel₀
    (natCast_p_ne_zero p),
    one_mul]

include hcyc hmono in
lemma Top_eq_of_le (m : ℕ) (σ : Γ) (hσ : IsGen p Km m σ) (k k' : ℕ) (hk : k ≤ k') (y : Ω)
    (hy : y ∈ Km (m + k)) : Top p σ k' y = Top p σ k y := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction l with
  | zero => rfl
  | succ l ih =>
      rw [← add_assoc, Top_succ_of_mem p hcyc m σ hσ (k + l) y (hmono (by omega) hy)]
      exact ih (by omega)

lemma Top_eq_self (m : ℕ) (σ : Γ) (hσ : IsGen p Km m σ) (k : ℕ) (y : Ω) (hy : y ∈ Km m) :
    Top p σ k y = y := by
  simp only [Top, Ssum]
  rw [Finset.sum_congr rfl fun j _ => pow_apply_eq_of_mem_fixingSubgroup p hσ.1 j hy]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (natCast_p_ne_zero p)), one_mul]

include hcyc hmono hfin hdeg hstab in

lemma Nop_mem (m : ℕ) (σ : Γ) (hσ : IsGen p Km m σ) (k : ℕ) (y : Ω) (hy : y ∈ Km (m + k + 1)) :
    Nop p σ k y ∈ Km (m + k) := by
  unfold Nop
  exact sum_pow_apply_mem p hmono hcyc hfin hdeg hstab (m + k) _ (isGen_pow p hcyc m σ hσ k) y hy

include hcyc hmono hfin hdeg hstab in

lemma Top_mem (m : ℕ) (σ : Γ) (hσ : IsGen p Km m σ) (k : ℕ) :
    ∀ y ∈ Km (m + k), Top p σ k y ∈ Km m := by
  induction k with
  | zero =>
      intro y hy
      rw [Nat.add_zero] at hy
      rw [Top_eq_self p m σ hσ 0 y hy]; exact hy
  | succ k ih =>
      intro y hy
      rw [Top_succ]
      apply ih
      refine mul_mem (inv_mem (natCast_mem _ p)) ?_
      have hy' : y ∈ Km (m + k + 1) := by
        have : m + (k + 1) = m + k + 1 := by ring
        rwa [this] at hy
      exact Nop_mem p hcyc hmono hfin hdeg hstab m σ hσ k y hy'

include hcyc hmono hfin hdeg in

lemma Ssum_apply_of_mem (m : ℕ) (σ : Γ) (hσ : IsGen p Km m σ) (k : ℕ) (τ : Γ)
    (hτ : τ ∈ (Km m).fixingSubgroup) (y : Ω) (hy : y ∈ Km (m + k)) :
    Ssum p σ k (τ y) = Ssum p σ k y := by
  obtain ⟨j₀, hj₀⟩ := exists_forall_apply_eq_pow_apply p hmono hcyc hfin hdeg m σ hσ k τ hτ
  simp only [Ssum]
  rw [hj₀ y hy]
  have h1 : ∀ j ∈ Finset.range (p ^ k), (σ ^ j) ((σ ^ j₀) y) = (σ ^ (j + j₀)) y := by
    intro j _; rw [← AlgEquiv.mul_apply, ← pow_add]
  rw [Finset.sum_congr rfl h1]
  apply sum_range_add_of_periodic (fun j => (σ ^ j) y) (p ^ k)
  intro j
  show (σ ^ (j + p ^ k)) y = (σ ^ j) y
  rw [pow_add, AlgEquiv.mul_apply,
    apply_eq_of_mem_fixingSubgroup p (isGen_pow p hcyc m σ hσ k).1 hy]

include hcyc hmono hfin hdeg in
lemma Top_apply_of_mem (m : ℕ) (σ : Γ) (hσ : IsGen p Km m σ) (k : ℕ) (τ : Γ)
    (hτ : τ ∈ (Km m).fixingSubgroup) (y : Ω) (hy : y ∈ Km (m + k)) :
    Top p σ k (τ y) = Top p σ k y := by
  simp only [Top, Ssum_apply_of_mem p hcyc hmono hfin hdeg m σ hσ k τ hτ y hy]

lemma norm_p_mul_sub_Nop_le (σ : Γ) (k : ℕ) (z : Ω) :
    ‖(p : Ω) * z - Nop p σ k z‖ ≤ ‖(σ ^ p ^ k) z - z‖ := by
  have hrw : (p : Ω) * z - Nop p σ k z = ∑ a ∈ Finset.range p, (z - ((σ ^ p ^ k) ^ a) z) := by
    simp only [Nop, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hrw]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun a _ => ?_
  rw [← norm_neg, neg_sub]
  exact norm_pow_apply_sub_le p _ z a

lemma norm_sub_inv_p_mul_Nop_le (σ : Γ) (k : ℕ) (z : Ω) :
    ‖z - (p : Ω)⁻¹ * Nop p σ k z‖ ≤ ‖(p : ℚ_[p])‖⁻¹ * ‖(σ ^ p ^ k) z - z‖ := by
  have hrw : z - (p : Ω)⁻¹ * Nop p σ k z = (p : Ω)⁻¹ * ((p : Ω) * z - Nop p σ k z) := by
    rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ (natCast_p_ne_zero p), one_mul]
  rw [hrw, norm_mul, norm_inv, norm_natCast_p]
  exact mul_le_mul_of_nonneg_left (norm_p_mul_sub_Nop_le p σ k z) (by positivity)

variable (c : ℕ → ℝ) (C : ℝ) (hc : ∀ m, 1 ≤ c m) (hC : ∀ n, ∏ m ∈ Finset.range n, c m ≤ C)
  (htr : ∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), σ ∈ (Km m).fixingSubgroup →
    σ ∉ (Km (m + 1)).fixingSubgroup → ∀ y ∈ Km (m + 1),
      ‖∑ i ∈ Finset.range p, (σ ^ i) y‖ ≤ ‖(p : ℚ_[p])‖ * c m * ‖y‖)

def D (m k : ℕ) : ℝ := ‖(p : ℚ_[p])‖⁻¹ * ∏ j ∈ Finset.range k, c (m + j)

include hc in
lemma one_le_prod_c (m k : ℕ) : 1 ≤ ∏ j ∈ Finset.range k, c (m + j) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.prod_range_succ]
      nlinarith [hc (m + k)]

include hc in
lemma D_nonneg (m k : ℕ) : 0 ≤ D p c m k := by
  unfold D
  have := one_le_prod_c c hc m k
  have := norm_p_pos (p := p)
  positivity

include hc in
lemma inv_norm_p_le_D (m k : ℕ) : ‖(p : ℚ_[p])‖⁻¹ ≤ D p c m k := by
  unfold D
  have h1 := one_le_prod_c c hc m k
  have h2 : 0 < ‖(p : ℚ_[p])‖⁻¹ := by have := norm_p_pos (p := p); positivity
  nlinarith

lemma D_succ (m k : ℕ) : D p c m (k + 1) = D p c m k * c (m + k) := by
  unfold D; rw [Finset.prod_range_succ]; ring

include hc hC in

lemma D_le (m k : ℕ) : D p c m k ≤ ‖(p : ℚ_[p])‖⁻¹ * C := by
  unfold D
  refine mul_le_mul_of_nonneg_left ?_ (by have := norm_p_pos (p := p); positivity)
  refine le_trans ?_ (hC (m + k))
  rw [Finset.prod_range_add]
  have h1 := one_le_prod_c c hc 0 m
  simp only [zero_add] at h1
  have h2 : 0 ≤ ∏ j ∈ Finset.range k, c (m + j) := zero_le_one.trans (one_le_prod_c c hc m k)
  nlinarith

include hcyc hmono hfin hdeg hstab hc htr in

lemma norm_sub_Top_le (m : ℕ) (σ : Γ) (hσ : IsGen p Km m σ) (σ' : Γ) (hσ' : IsGen p Km m σ')
    (k : ℕ) : ∀ y ∈ Km (m + k), ‖y - Top p σ k y‖ ≤ D p c m k * ‖σ' y - y‖ := by
  induction k with
  | zero =>
      intro y hy
      rw [Top_eq_self p m σ hσ 0 y (by simpa using hy), sub_self, norm_zero]
      exact mul_nonneg (D_nonneg p c hc m 0) (norm_nonneg _)
  | succ k ih =>
      intro y hy
      have hy' : y ∈ Km (m + k + 1) := by
        have : m + (k + 1) = m + k + 1 := by ring
        rwa [this] at hy
      have h0 : (Km m).fixingSubgroup ≤ (Km 0).fixingSubgroup :=
        IntermediateField.fixingSubgroup_le (hmono (Nat.zero_le m))
      have hgen := isGen_pow p hcyc m σ hσ k
      have hρm : σ ^ p ^ k ∈ (Km m).fixingSubgroup := Subgroup.pow_mem _ hσ.1 _

      have hNmem : Nop p σ k y ∈ Km (m + k) := Nop_mem p hcyc hmono hfin hdeg hstab m σ hσ k y hy'
      have hy₁mem : (p : Ω)⁻¹ * Nop p σ k y ∈ Km (m + k) :=
        mul_mem (inv_mem (natCast_mem _ p)) hNmem

      have hT : Top p σ (k + 1) y = Top p σ k ((p : Ω)⁻¹ * Nop p σ k y) := Top_succ p σ k y

      have h3 : ‖y - (p : Ω)⁻¹ * Nop p σ k y‖ ≤ ‖(p : ℚ_[p])‖⁻¹ * ‖σ' y - y‖ := by
        refine (norm_sub_inv_p_mul_Nop_le p σ k y).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (by have := norm_p_pos (p := p); positivity)
        exact norm_apply_sub_le_of_isGen p hmono hcyc hfin hdeg m (m + k + 1) (by omega) σ' hσ'
          (σ ^ p ^ k) hρm y hy'

      have h4 : ‖σ' ((p : Ω)⁻¹ * Nop p σ k y) - (p : Ω)⁻¹ * Nop p σ k y‖ ≤
          c (m + k) * ‖σ' y - y‖ := by
        have hcomm : σ' (Nop p σ k y) = Nop p σ k (σ' y) := by
          unfold Nop
          rw [map_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          exact apply_comm p hmono hcyc hfin hdeg hstab m (m + k + 1) (by omega) σ' ((σ ^ p ^ k) ^
            a)
            hσ'.1 (Subgroup.pow_mem _ hρm a) y hy'
        have hrw : σ' ((p : Ω)⁻¹ * Nop p σ k y) - (p : Ω)⁻¹ * Nop p σ k y =
            (p : Ω)⁻¹ * Nop p σ k (σ' y - y) := by
          rw [map_mul, map_inv₀, map_natCast, hcomm, Nop_sub, mul_sub]
        rw [hrw, norm_mul, norm_inv, norm_natCast_p]
        have hw : σ' y - y ∈ Km (m + k + 1) := sub_mem (hstab _ _ (h0 hσ'.1) y hy') hy'
        have h5 := htr (m + k) (σ ^ p ^ k) hgen.1 hgen.2 (σ' y - y) hw
        have h5' : ‖Nop p σ k (σ' y - y)‖ ≤ ‖(p : ℚ_[p])‖ * c (m + k) * ‖σ' y - y‖ := by
          unfold Nop; exact h5
        have hp := norm_p_pos (p := p)
        calc ‖(p : ℚ_[p])‖⁻¹ * ‖Nop p σ k (σ' y - y)‖
            ≤ ‖(p : ℚ_[p])‖⁻¹ * (‖(p : ℚ_[p])‖ * c (m + k) * ‖σ' y - y‖) :=
              mul_le_mul_of_nonneg_left h5' (by positivity)
          _ = c (m + k) * ‖σ' y - y‖ := by field_simp

      have hsplit : y - Top p σ (k + 1) y = (y - (p : Ω)⁻¹ * Nop p σ k y) +
          ((p : Ω)⁻¹ * Nop p σ k y - Top p σ k ((p : Ω)⁻¹ * Nop p σ k y)) := by
        rw [hT]; abel
      rw [hsplit]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · exact h3.trans (mul_le_mul_of_nonneg_right (inv_norm_p_le_D p c hc m (k + 1))
          (norm_nonneg _))
      · refine (ih _ hy₁mem).trans ?_
        rw [D_succ]
        have hD := D_nonneg p c hc m k
        calc D p c m k * ‖σ' ((p : Ω)⁻¹ * Nop p σ k y) - (p : Ω)⁻¹ * Nop p σ k y‖
              ≤ D p c m k * (c (m + k) * ‖σ' y - y‖) := mul_le_mul_of_nonneg_left h4 hD
          _ = D p c m k * c (m + k) * ‖σ' y - y‖ := by ring

end B

section C

variable (p)

structure Hyp (Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)) (c : ℕ → ℝ) (C : ℝ) : Prop where
  mono : Monotone Km
  fin : ∀ m, FiniteDimensional ℚ_[p] (Km m)
  stab : ∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), σ ∈ (Km 0).fixingSubgroup →
    ∀ y ∈ Km m, σ y ∈ Km m
  deg : ∀ m n : ℕ, n = m + 1 → Module.finrank ℚ_[p] (Km n) = p * Module.finrank ℚ_[p] (Km m)
  cyc : ∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), σ ∈ (Km m).fixingSubgroup →
    σ ∉ (Km (m + 1)).fixingSubgroup →
      σ ^ p ∈ (Km (m + 1)).fixingSubgroup ∧ σ ^ p ∉ (Km (m + 2)).fixingSubgroup
  one_le : ∀ m, 1 ≤ c m
  prod_le : ∀ n, ∏ m ∈ Finset.range n, c m ≤ C
  tr : ∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), σ ∈ (Km m).fixingSubgroup →
    σ ∉ (Km (m + 1)).fixingSubgroup → ∀ y ∈ Km (m + 1),
      ‖∑ i ∈ Finset.range p, (σ ^ i) y‖ ≤ ‖(p : ℚ_[p])‖ * c m * ‖y‖

variable {Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)} {c : ℕ → ℝ} {C : ℝ}
variable (H : Hyp p Km c C)

def dconst (C : ℝ) : ℝ := ‖(p : ℚ_[p])‖⁻¹ * C

include H in
lemma one_le_C : 1 ≤ C := by simpa using H.prod_le 0

include H in
lemma dconst_pos : 0 < dconst p C := by
  unfold dconst
  have := one_le_C p H
  have := norm_p_pos (p := p)
  positivity

def gen (m : ℕ) : Γ := Classical.choose (exists_isGen p H.mono H.fin H.deg m)

lemma gen_spec (m : ℕ) : IsGen p Km m (gen p H m) :=
  Classical.choose_spec (exists_isGen p H.mono H.fin H.deg m)

open Classical in

def tΩ (m : ℕ) (y : Ω) : Ω :=
  if h : ∃ k, y ∈ Km (m + k) then Top p (gen p H m) (Classical.choose h) y else 0

include H in
lemma mem_add_of_mem {n : ℕ} (m : ℕ) {y : Ω} (hy : y ∈ Km n) : y ∈ Km (m + n) :=
  H.mono (Nat.le_add_left n m) hy

lemma unorm_sub_le_max (x y : Ω) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max _ _

lemma tΩ_eq (m k : ℕ) (y : Ω) (hy : y ∈ Km (m + k)) : tΩ p H m y = Top p (gen p H m) k y := by
  have h : ∃ k, y ∈ Km (m + k) := ⟨k, hy⟩
  unfold tΩ
  rw [dif_pos h]
  have hk₀ := Classical.choose_spec h
  rw [← Top_eq_of_le p H.cyc H.mono m _ (gen_spec p H m) _ (max k (Classical.choose h))
      (le_max_right _ _) y hk₀,
    Top_eq_of_le p H.cyc H.mono m _ (gen_spec p H m) k (max k (Classical.choose h))
      (le_max_left _ _) y hy]

lemma tΩ_add (m : ℕ) {n n' : ℕ} (y y' : Ω) (hy : y ∈ Km n) (hy' : y' ∈ Km n') :
    tΩ p H m (y + y') = tΩ p H m y + tΩ p H m y' := by
  have h1 : y ∈ Km (m + (n + n')) := H.mono (by omega) hy
  have h2 : y' ∈ Km (m + (n + n')) := H.mono (by omega) hy'
  rw [tΩ_eq p H m (n + n') y h1, tΩ_eq p H m (n + n') y' h2,
    tΩ_eq p H m (n + n') (y + y') (add_mem h1 h2), Top_add]

lemma tΩ_mul (m : ℕ) {n : ℕ} (a y : Ω) (ha : a ∈ Km m) (hy : y ∈ Km n) :
    tΩ p H m (a * y) = a * tΩ p H m y := by
  have h1 : y ∈ Km (m + n) := mem_add_of_mem p H m hy
  have h2 : a * y ∈ Km (m + n) := mul_mem (H.mono (Nat.le_add_right m n) ha) h1
  rw [tΩ_eq p H m n _ h2, tΩ_eq p H m n y h1,
    Top_mul_of_fixed p _ n a y (apply_eq_of_mem_fixingSubgroup p (gen_spec p H m).1 ha)]

lemma tΩ_self (m : ℕ) (y : Ω) (hy : y ∈ Km m) : tΩ p H m y = y := by
  rw [tΩ_eq p H m 0 y (by simpa using hy), Top_eq_self p m _ (gen_spec p H m) 0 y hy]

lemma tΩ_mem (m : ℕ) {n : ℕ} (y : Ω) (hy : y ∈ Km n) : tΩ p H m y ∈ Km m := by
  rw [tΩ_eq p H m n y (mem_add_of_mem p H m hy)]
  exact Top_mem p H.cyc H.mono H.fin H.deg H.stab m _ (gen_spec p H m) n y (mem_add_of_mem p H m hy)

lemma tΩ_apply (m : ℕ) {n : ℕ} (τ : Γ) (hτ : τ ∈ (Km m).fixingSubgroup) (y : Ω) (hy : y ∈ Km n) :
    tΩ p H m (τ y) = tΩ p H m y := by
  have h0 : (Km m).fixingSubgroup ≤ (Km 0).fixingSubgroup :=
    IntermediateField.fixingSubgroup_le (H.mono (Nat.zero_le m))
  have h1 : y ∈ Km (m + n) := mem_add_of_mem p H m hy
  have h2 : τ y ∈ Km (m + n) := H.stab _ _ (h0 hτ) y h1
  rw [tΩ_eq p H m n _ h2, tΩ_eq p H m n y h1,
    Top_apply_of_mem p H.cyc H.mono H.fin H.deg m _ (gen_spec p H m) n τ hτ y h1]

lemma norm_sub_tΩ_le (m : ℕ) (σ' : Γ) (hσ' : IsGen p Km m σ') {n : ℕ} (y : Ω) (hy : y ∈ Km n) :
    ‖y - tΩ p H m y‖ ≤ dconst p C * ‖σ' y - y‖ := by
  have h1 : y ∈ Km (m + n) := mem_add_of_mem p H m hy
  rw [tΩ_eq p H m n y h1]
  refine (norm_sub_Top_le p H.cyc H.mono H.fin H.deg H.stab c H.one_le H.tr m _ (gen_spec p H m)
    σ' hσ' n y h1).trans ?_
  exact mul_le_mul_of_nonneg_right (D_le p c C H.one_le H.prod_le m n) (norm_nonneg _)

lemma norm_tΩ_le (m : ℕ) {n : ℕ} (y : Ω) (hy : y ∈ Km n) :
    ‖tΩ p H m y‖ ≤ max 1 (dconst p C) * ‖y‖ := by
  have h := norm_sub_tΩ_le p H m _ (gen_spec p H m) y hy
  have h1 : ‖gen p H m y - y‖ ≤ ‖y‖ := by
    refine (unorm_sub_le_max p _ _).trans ?_
    simp only [norm_algEquiv, max_self, le_refl]
  have hd := (dconst_pos p H).le
  have h2 : ‖y - tΩ p H m y‖ ≤ dconst p C * ‖y‖ := h.trans (mul_le_mul_of_nonneg_left h1 hd)
  have h3 : ‖tΩ p H m y‖ = ‖y - (y - tΩ p H m y)‖ := by congr 1; abel
  calc ‖tΩ p H m y‖ = ‖y - (y - tΩ p H m y)‖ := h3
    _ ≤ max ‖y‖ ‖y - tΩ p H m y‖ := unorm_sub_le_max p _ _
    _ ≤ max 1 (dconst p C) * ‖y‖ := by
        refine max_le ?_ ?_
        · calc ‖y‖ = 1 * ‖y‖ := (one_mul _).symm
            _ ≤ max 1 (dconst p C) * ‖y‖ :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        · exact h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

end C

section D

variable (p)
variable {Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)} {c : ℕ → ℝ} {C : ℝ}
variable (H : Hyp p Km c C)

def towerSubmodule : Submodule ℚ_[p] ℂ_[p] where
  carrier := ⋃ m : ℕ, Set.range fun k : Km m => ((k : Ω) : ℂ_[p])
  zero_mem' := Set.mem_iUnion.mpr ⟨0, ⟨0, by simp⟩⟩
  add_mem' := by
    intro u v hu hv
    obtain ⟨m, ⟨k, rfl⟩⟩ := Set.mem_iUnion.mp hu
    obtain ⟨n, ⟨l, rfl⟩⟩ := Set.mem_iUnion.mp hv
    refine Set.mem_iUnion.mpr ⟨max m n, ⟨⟨(k : Ω) + l, ?_⟩, ?_⟩⟩
    · exact add_mem (H.mono (le_max_left m n) k.2) (H.mono (le_max_right m n) l.2)
    · simp [Completion.coe_add]
  smul_mem' := by
    intro a u hu
    obtain ⟨m, ⟨k, rfl⟩⟩ := Set.mem_iUnion.mp hu
    refine Set.mem_iUnion.mpr ⟨m, ⟨⟨algebraMap ℚ_[p] Ω a * (k : Ω), ?_⟩, ?_⟩⟩
    · exact mul_mem (algebraMap_mem (Km m) a) k.2
    · simp only
      rw [Completion.coe_mul, Algebra.smul_def, IsScalarTower.algebraMap_apply ℚ_[p] Ω ℂ_[p]]
      rfl

lemma mem_towerSubmodule_iff (z : ℂ_[p]) :
    z ∈ towerSubmodule p H ↔ ∃ n : ℕ, ∃ y : Ω, y ∈ Km n ∧ z = ((y : Ω) : ℂ_[p]) := by
  constructor
  · intro hz
    obtain ⟨n, ⟨k, hk⟩⟩ := Set.mem_iUnion.mp hz
    exact ⟨n, k, k.2, hk.symm⟩
  · rintro ⟨n, y, hy, rfl⟩
    exact Set.mem_iUnion.mpr ⟨n, ⟨⟨y, hy⟩, rfl⟩⟩

lemma coe_mem_towerSubmodule {n : ℕ} {y : Ω} (hy : y ∈ Km n) :
    ((y : Ω) : ℂ_[p]) ∈ towerSubmodule p H :=
  (mem_towerSubmodule_iff p H _).mpr ⟨n, y, hy, rfl⟩

lemma coe_topologicalClosure_towerSubmodule :
    ((towerSubmodule p H).topologicalClosure : Set ℂ_[p]) = PadicComplex.towerClosure p Km := by
  rw [Submodule.topologicalClosure_coe]; rfl

lemma mem_towerClosure_iff (z : ℂ_[p]) :
    z ∈ PadicComplex.towerClosure p Km ↔ z ∈ (towerSubmodule p H).topologicalClosure := by
  rw [← SetLike.mem_coe, coe_topologicalClosure_towerSubmodule]

def preim (z : ℂ_[p]) : Ω := Function.invFun ((↑) : Ω → ℂ_[p]) z

lemma preim_coe (y : Ω) : preim p ((y : Ω) : ℂ_[p]) = y :=
  Function.leftInverse_invFun (Completion.coe_injective (PadicAlgCl p)) y

def fS (m : ℕ) : towerSubmodule p H →ₗ[ℚ_[p]] ℂ_[p] where
  toFun z := ((tΩ p H m (preim p z.1) : Ω) : ℂ_[p])
  map_add' := by
    intro z z'
    obtain ⟨n, y, hy, hz⟩ := (mem_towerSubmodule_iff p H _).mp z.2
    obtain ⟨n', y', hy', hz'⟩ := (mem_towerSubmodule_iff p H _).mp z'.2
    simp only [Submodule.coe_add, hz, hz']
    rw [← Completion.coe_add, preim_coe, preim_coe, preim_coe, tΩ_add p H m y y' hy hy',
      Completion.coe_add]
  map_smul' := by
    intro a z
    obtain ⟨n, y, hy, hz⟩ := (mem_towerSubmodule_iff p H _).mp z.2
    simp only [Submodule.coe_smul, hz, RingHom.id_apply]
    rw [← Completion.coe_smul, preim_coe, preim_coe, Algebra.smul_def,
      tΩ_mul p H m _ y (algebraMap_mem (Km m) a) hy, ← Algebra.smul_def, Completion.coe_smul]

lemma fS_apply_coe (m : ℕ) {n : ℕ} (y : Ω) (hy : y ∈ Km n) :
    fS p H m ⟨((y : Ω) : ℂ_[p]), coe_mem_towerSubmodule p H hy⟩ = ((tΩ p H m y : Ω) : ℂ_[p]) := by
  simp [fS, preim_coe]

lemma norm_fS_le (m : ℕ) (z : towerSubmodule p H) :
    ‖fS p H m z‖ ≤ max 1 (dconst p C) * ‖z‖ := by
  obtain ⟨n, y, hy, hz⟩ := (mem_towerSubmodule_iff p H _).mp z.2
  have h1 : fS p H m z = ((tΩ p H m y : Ω) : ℂ_[p]) := by
    have : z = ⟨((y : Ω) : ℂ_[p]), coe_mem_towerSubmodule p H hy⟩ := Subtype.ext hz
    rw [this, fS_apply_coe p H m y hy]
  rw [h1, PadicComplex.norm_extends]
  have h2 : ‖z‖ = ‖y‖ := by
    rw [← PadicComplex.norm_extends p y, ← hz]; rfl
  rw [h2]
  exact norm_tΩ_le p H m y hy

def fSc (m : ℕ) : towerSubmodule p H →L[ℚ_[p]] ℂ_[p] :=
  (fS p H m).mkContinuous (max 1 (dconst p C)) (norm_fS_le p H m)

def incl : towerSubmodule p H →L[ℚ_[p]] (towerSubmodule p H).topologicalClosure :=
  { Submodule.inclusion (Submodule.le_topologicalClosure _) with
    cont := continuous_inclusion (Submodule.le_topologicalClosure _) }

lemma incl_apply (z : towerSubmodule p H) : (incl p H z : ℂ_[p]) = z := rfl

lemma denseRange_incl : DenseRange (incl p H) := by
  have : DenseRange (Set.inclusion
      (Submodule.le_topologicalClosure (towerSubmodule p H) : ((towerSubmodule p H) : Set ℂ_[p]) ⊆
        (towerSubmodule p H).topologicalClosure)) := by
    exact (denseRange_inclusion_iff _).mpr (le_of_eq (Submodule.topologicalClosure_coe _))
  exact this

lemma isUniformInducing_incl : IsUniformInducing (incl p H) := by
  have hiso : Isometry (incl p H) := Isometry.of_dist_eq fun _ _ => rfl
  exact hiso.isUniformInducing

def Fext (m : ℕ) : (towerSubmodule p H).topologicalClosure →L[ℚ_[p]] ℂ_[p] :=
  (fSc p H m).extend (incl p H)

lemma Fext_coe (m : ℕ) {n : ℕ} (y : Ω) (hy : y ∈ Km n)
    (h : ((y : Ω) : ℂ_[p]) ∈ (towerSubmodule p H).topologicalClosure) :
    Fext p H m ⟨((y : Ω) : ℂ_[p]), h⟩ = ((tΩ p H m y : Ω) : ℂ_[p]) := by
  have h1 : (⟨((y : Ω) : ℂ_[p]), h⟩ : (towerSubmodule p H).topologicalClosure) =
      incl p H ⟨((y : Ω) : ℂ_[p]), coe_mem_towerSubmodule p H hy⟩ := rfl
  rw [Fext, h1, ContinuousLinearMap.extend_eq _ (denseRange_incl p H) (isUniformInducing_incl p H)]
  show fS p H m _ = _
  exact fS_apply_coe p H m y hy

open Classical in

def R (m : ℕ) (z : ℂ_[p]) : ℂ_[p] :=
  if h : z ∈ (towerSubmodule p H).topologicalClosure then Fext p H m ⟨z, h⟩ else 0

lemma R_coe (m : ℕ) (w : (towerSubmodule p H).topologicalClosure) : R p H m (w : ℂ_[p]) = Fext p H
  m w := by
  unfold R; rw [dif_pos w.2]

lemma R_apply_coe (m : ℕ) {n : ℕ} (y : Ω) (hy : y ∈ Km n) :
    R p H m ((y : Ω) : ℂ_[p]) = ((tΩ p H m y : Ω) : ℂ_[p]) := by
  have h : ((y : Ω) : ℂ_[p]) ∈ (towerSubmodule p H).topologicalClosure :=
    Submodule.le_topologicalClosure _ (coe_mem_towerSubmodule p H hy)
  unfold R; rw [dif_pos h, Fext_coe p H m y hy h]

lemma closure_induction {P : (towerSubmodule p H).topologicalClosure → Prop}
    (hP : IsClosed {w | P w})
    (hS : ∀ (n : ℕ) (y : Ω) (hy : y ∈ Km n),
      P ⟨((y : Ω) : ℂ_[p]), Submodule.le_topologicalClosure _ (coe_mem_towerSubmodule p H hy)⟩)
    (w : (towerSubmodule p H).topologicalClosure) : P w := by
  refine (denseRange_incl p H).induction_on w hP fun s => ?_
  obtain ⟨n, y, hy, hs⟩ := (mem_towerSubmodule_iff p H _).mp s.2
  have : incl p H s = ⟨((y : Ω) : ℂ_[p]),
      Submodule.le_topologicalClosure _ (coe_mem_towerSubmodule p H hy)⟩ := Subtype.ext hs
  rw [this]
  exact hS n y hy

lemma coe_mul_mem_closure {n : ℕ} (k : Ω) (hk : k ∈ Km n) {z : ℂ_[p]}
    (hz : z ∈ (towerSubmodule p H).topologicalClosure) :
    ((k : Ω) : ℂ_[p]) * z ∈ (towerSubmodule p H).topologicalClosure := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hz ⊢
  refine map_mem_closure (continuous_const_mul _) hz fun w hw => ?_
  obtain ⟨n', y, hy, rfl⟩ := (mem_towerSubmodule_iff p H _).mp hw
  rw [← Completion.coe_mul]
  exact coe_mem_towerSubmodule p H
    (mul_mem (H.mono (le_max_left n n') hk) (H.mono (le_max_right n n') hy))

lemma smul_mem_closure (τ : Γ) (hτ : τ ∈ (Km 0).fixingSubgroup) {z : ℂ_[p]}
    (hz : z ∈ (towerSubmodule p H).topologicalClosure) :
    τ • z ∈ (towerSubmodule p H).topologicalClosure := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hz ⊢
  refine map_mem_closure (PadicComplex.continuous_smul_left p τ) hz fun w hw => ?_
  obtain ⟨n, y, hy, rfl⟩ := (mem_towerSubmodule_iff p H _).mp hw
  rw [PadicComplex.smul_coe]
  exact coe_mem_towerSubmodule p H (H.stab n τ hτ y hy)

include H in

lemma isClosed_range_coe (m : ℕ) :
    IsClosed (Set.range fun k : Km m => ((k : Ω) : ℂ_[p])) := by
  haveI := H.fin m
  let L : Km m →ₗ[ℚ_[p]] ℂ_[p] :=
    ((Algebra.linearMap Ω ℂ_[p]).restrictScalars ℚ_[p]).comp (Km m).val.toLinearMap
  have hrange : (Set.range fun k : Km m => ((k : Ω) : ℂ_[p])) = (LinearMap.range L : Set ℂ_[p]) :=
    by
    ext z
    simp only [Set.mem_range, SetLike.mem_coe, LinearMap.mem_range]
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩; exact ⟨k, rfl⟩
  rw [hrange]
  exact (LinearMap.range L).closed_of_finiteDimensional

theorem isTateTrace (m : ℕ) : PadicComplex.IsTateTrace p Km m (dconst p C) (R p H m) := by
  have hX := mem_towerClosure_iff p H
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x hx y hy
    rw [hX] at hx hy
    have hxy : x + y ∈ (towerSubmodule p H).topologicalClosure := add_mem hx hy
    unfold R
    rw [dif_pos hx, dif_pos hy, dif_pos hxy, ← map_add]
    rfl
  ·
    intro k x hx
    rw [hX] at hx
    let g : (towerSubmodule p H).topologicalClosure → (towerSubmodule p H).topologicalClosure :=
      fun w => ⟨((k : Ω) : ℂ_[p]) * w, coe_mul_mem_closure p H (k : Ω) k.2 w.2⟩
    have hg : Continuous g := (continuous_const.mul continuous_subtype_val).subtype_mk _
    have key : ∀ w : (towerSubmodule p H).topologicalClosure,
        Fext p H m (g w) = ((k : Ω) : ℂ_[p]) * Fext p H m w := by
      intro w
      apply closure_induction p H (P := fun w => Fext p H m (g w) = ((k : Ω) : ℂ_[p]) * Fext p H m
        w)
      · exact isClosed_eq ((Fext p H m).continuous.comp hg) (continuous_const.mul (Fext p H
        m).continuous)
      · intro n y hy
        have hky : (k : Ω) * y ∈ Km (m + n) :=
          mul_mem (H.mono (Nat.le_add_right m n) k.2) (H.mono (Nat.le_add_left n m) hy)
        have hg1 : g ⟨((y : Ω) : ℂ_[p]), Submodule.le_topologicalClosure _ (coe_mem_towerSubmodule
          p H hy)⟩ =
            ⟨(((k : Ω) * y : Ω) : ℂ_[p]),
              Submodule.le_topologicalClosure _ (coe_mem_towerSubmodule p H hky)⟩ := by
          apply Subtype.ext
          show ((k : Ω) : ℂ_[p]) * ((y : Ω) : ℂ_[p]) = (((k : Ω) * y : Ω) : ℂ_[p])
          rw [Completion.coe_mul]
        rw [hg1, Fext_coe p H m _ hky, Fext_coe p H m y hy, tΩ_mul p H m (k : Ω) y k.2 hy,
          Completion.coe_mul]
    have h1 := key ⟨x, hx⟩
    rw [R_coe p H m ⟨x, hx⟩]
    have : ((k : Ω) : ℂ_[p]) * x = ((g ⟨x, hx⟩ : (towerSubmodule p H).topologicalClosure) : ℂ_[p])
      := rfl
    rw [this, R_coe, key]
  ·
    intro k
    rw [R_apply_coe p H m (k : Ω) k.2, tΩ_self p H m (k : Ω) k.2]
  ·
    intro x hx
    rw [hX] at hx
    have key : ∀ w : (towerSubmodule p H).topologicalClosure,
        Fext p H m w ∈ Set.range fun k : Km m => ((k : Ω) : ℂ_[p]) := by
      intro w
      apply closure_induction p H (P := fun w => Fext p H m w ∈ Set.range fun k : Km m => ((k : Ω)
        : ℂ_[p]))
      · exact (isClosed_range_coe p H m).preimage (Fext p H m).continuous
      · intro n y hy
        rw [Fext_coe p H m y hy]
        exact ⟨⟨tΩ p H m y, tΩ_mem p H m y hy⟩, rfl⟩
    obtain ⟨k, hk⟩ := key ⟨x, hx⟩
    refine ⟨k, ?_⟩
    rw [R_coe p H m ⟨x, hx⟩]
    exact hk.symm
  ·
    intro τ hτ x hx
    rw [hX] at hx
    have h0 : (Km m).fixingSubgroup ≤ (Km 0).fixingSubgroup :=
      IntermediateField.fixingSubgroup_le (H.mono (Nat.zero_le m))
    let g : (towerSubmodule p H).topologicalClosure → (towerSubmodule p H).topologicalClosure :=
      fun w => ⟨τ • (w : ℂ_[p]), smul_mem_closure p H τ (h0 hτ) w.2⟩
    have hg : Continuous g := ((PadicComplex.continuous_smul_left p τ).comp
      continuous_subtype_val).subtype_mk _
    have key : ∀ w : (towerSubmodule p H).topologicalClosure, Fext p H m (g w) = Fext p H m w := by
      intro w
      apply closure_induction p H (P := fun w => Fext p H m (g w) = Fext p H m w)
      · exact isClosed_eq ((Fext p H m).continuous.comp hg) (Fext p H m).continuous
      · intro n y hy
        have hτy : τ y ∈ Km n := H.stab n τ (h0 hτ) y hy
        have hg1 : g ⟨((y : Ω) : ℂ_[p]), Submodule.le_topologicalClosure _ (coe_mem_towerSubmodule
          p H hy)⟩ =
            ⟨((τ y : Ω) : ℂ_[p]),
              Submodule.le_topologicalClosure _ (coe_mem_towerSubmodule p H hτy)⟩ := by
          apply Subtype.ext
          show τ • ((y : Ω) : ℂ_[p]) = ((τ y : Ω) : ℂ_[p])
          rw [PadicComplex.smul_coe]
        rw [hg1, Fext_coe p H m _ hτy, Fext_coe p H m y hy, tΩ_apply p H m τ hτ y hy]
    have : τ • x = ((g ⟨x, hx⟩ : (towerSubmodule p H).topologicalClosure) : ℂ_[p]) := rfl
    rw [this, R_coe, key, ← R_coe p H m ⟨x, hx⟩]
  ·
    intro σ' hσ' hσ'' x hx
    rw [hX] at hx
    have hgen : IsGen p Km m σ' := ⟨hσ', hσ''⟩
    have key : ∀ w : (towerSubmodule p H).topologicalClosure,
        ‖(w : ℂ_[p]) - Fext p H m w‖ ≤ dconst p C * ‖σ' • (w : ℂ_[p]) - w‖ := by
      intro w
      apply closure_induction p H
        (P := fun w => ‖(w : ℂ_[p]) - Fext p H m w‖ ≤ dconst p C * ‖σ' • (w : ℂ_[p]) - w‖)
      · exact isClosed_le ((continuous_subtype_val.sub (Fext p H m).continuous).norm)
          (continuous_const.mul (((PadicComplex.continuous_smul_left p σ').comp
            continuous_subtype_val).sub continuous_subtype_val).norm)
      · intro n y hy
        show ‖((y : Ω) : ℂ_[p]) - Fext p H m _‖ ≤ dconst p C * ‖σ' • ((y : Ω) : ℂ_[p]) - (y :
          ℂ_[p])‖
        rw [Fext_coe p H m y hy, ← Completion.coe_sub, PadicComplex.norm_extends,
          PadicComplex.smul_coe, ← Completion.coe_sub, PadicComplex.norm_extends]
        exact norm_sub_tΩ_le p H m σ' hgen y hy
    have := key ⟨x, hx⟩
    rwa [← R_coe p H m ⟨x, hx⟩] at this

include H in

theorem main : ∃ d : ℝ, 0 < d ∧ ∀ m, ∃ R : ℂ_[p] → ℂ_[p], PadicComplex.IsTateTrace p Km m d R :=
  ⟨dconst p C, dconst_pos p H, fun m => ⟨R p H m, isTateTrace p H m⟩⟩

end D


end TateTraceExist

namespace PadicComplex

/-- Tate traces exist along any monotone tower of finite extensions
satisfying the degree and trace-bound hypotheses: there is a uniform
constant `d > 0` such that every level admits a Tate trace map. -/
public theorem exists_isTateTrace_of_norm_sum_pow_apply_le
    (p : ℕ) [Fact p.Prime] (Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)) (hmono : Monotone Km)
    (hfin : ∀ m, FiniteDimensional ℚ_[p] (Km m))
    (hstab : ∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), σ ∈ (Km 0).fixingSubgroup →
      ∀ y ∈ Km m, σ y ∈ Km m)
    (hdeg : ∀ m n : ℕ, n = m + 1 → Module.finrank ℚ_[p] (Km n) = p * Module.finrank ℚ_[p] (Km m))
    (hcyc : ∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), σ ∈ (Km m).fixingSubgroup →
      σ ∉ (Km (m + 1)).fixingSubgroup →
        σ ^ p ∈ (Km (m + 1)).fixingSubgroup ∧ σ ^ p ∉ (Km (m + 2)).fixingSubgroup)
    (c : ℕ → ℝ) (C : ℝ) (hc : ∀ m, 1 ≤ c m) (hC : ∀ n, ∏ m ∈ Finset.range n, c m ≤ C)
    (htr : ∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), σ ∈ (Km m).fixingSubgroup →
      σ ∉ (Km (m + 1)).fixingSubgroup → ∀ y ∈ Km (m + 1),
        ‖∑ i ∈ Finset.range p, (σ ^ i) y‖ ≤ ‖(p : ℚ_[p])‖ * c m * ‖y‖) :
    ∃ d : ℝ, 0 < d ∧ ∀ m, ∃ R : ℂ_[p] → ℂ_[p], PadicComplex.IsTateTrace p Km m d R :=
  TateTraceExist.main p ⟨hmono, hfin, hstab, hdeg, hcyc, hc, hC, htr⟩

end PadicComplex

namespace TraceVanishing


open scoped TensorProduct Matrix
open UniformSpace

variable {p : ℕ} [Fact p.Prime]

local notation "Ω" => PadicAlgCl p
local notation "Γ" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)

section coords

variable (p)
variable {L : Type*} [Field L] [Algebra ℚ_[p] L] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι ℚ_[p] L)

def coord (z : ℂ_[p] ⊗[ℚ_[p]] L) (i : ι) : ℂ_[p] :=
  (Algebra.TensorProduct.basis ℂ_[p] b).repr z i

omit [Fintype ι] [DecidableEq ι] in
@[scoped simp] lemma coord_zero (i : ι) : coord p b 0 i = 0 := by simp [coord]

omit [Fintype ι] [DecidableEq ι] in
@[scoped simp] lemma coord_add (z w : ℂ_[p] ⊗[ℚ_[p]] L) (i : ι) :
    coord p b (z + w) i = coord p b z i + coord p b w i := by
  simp [coord]

omit [Fintype ι] [DecidableEq ι] in
@[scoped simp] lemma coord_tmul (a : ℂ_[p]) (l : L) (i : ι) :
    coord p b (a ⊗ₜ[ℚ_[p]] l) i = a * algebraMap ℚ_[p] ℂ_[p] (b.repr l i) := by
  simp [coord, Algebra.TensorProduct.basis_repr_tmul, Finsupp.mapRange_apply]

omit [Fintype ι] [DecidableEq ι] in

lemma coord_map_gal (σ : Γ) (z : ℂ_[p] ⊗[ℚ_[p]] L) (i : ι) :
    coord p b (Algebra.TensorProduct.map (PadicComplex.galAlgHom p σ) (AlgHom.id ℚ_[p] L) z) i =
      σ • coord p b z i := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a l =>
      rw [Algebra.TensorProduct.map_tmul, coord_tmul, AlgHom.id_apply,
        PadicComplex.galAlgHom_apply, coord_tmul, smul_mul', PadicComplex.smul_algebraMap]
  | add z w hz hw =>
      rw [map_add, coord_add, coord_add, hz, hw, smul_add]

lemma coord_one_tmul_mul (ℓ : L) (z : ℂ_[p] ⊗[ℚ_[p]] L) (i : ι) :
    coord p b (((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] ℓ) * z) i =
      ∑ j, algebraMap ℚ_[p] ℂ_[p] (Algebra.leftMulMatrix b ℓ i j) * coord p b z j := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, coord_tmul]
      have h := congrFun (Algebra.leftMulMatrix_mulVec_repr b ℓ m) i
      simp only [Matrix.mulVec, dotProduct] at h
      rw [← h, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [coord_tmul, map_mul]
      ring
  | add z w hz hw =>
      rw [mul_add, coord_add, hz, hw, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [coord_add, mul_add]

omit [Fintype ι] [DecidableEq ι] in
lemma exists_coord_ne_zero {z : ℂ_[p] ⊗[ℚ_[p]] L} (hz : z ≠ 0) : ∃ i, coord p b z i ≠ 0 := by
  by_contra h
  push Not at h
  apply hz
  have : (Algebra.TensorProduct.basis ℂ_[p] b).repr z = 0 := by
    ext i
    exact h i
  simpa using this

end coords

lemma exists_pow_mem_fixingSubgroup (M : IntermediateField ℚ_[p] Ω) [FiniteDimensional ℚ_[p] M] :
    ∃ N : ℕ, 0 < N ∧ ∀ σ : Γ, σ ^ N ∈ M.fixingSubgroup := by
  classical
  set c := Fintype.card (M →ₐ[ℚ_[p]] Ω) with hc
  refine ⟨c.factorial, Nat.factorial_pos c, fun σ => ?_⟩
  let f : Fin (c + 1) → (M →ₐ[ℚ_[p]] Ω) := fun n =>
    ((σ ^ (n : ℕ) : Γ) : Ω →ₐ[ℚ_[p]] Ω).comp M.val
  obtain ⟨i, j, hij, hfij⟩ := Fintype.exists_ne_map_eq_of_card_lt f
    (by simp only [Fintype.card_fin]; omega)
  have key : ∀ i j : Fin (c + 1), i < j → f i = f j → σ ^ c.factorial ∈ M.fixingSubgroup := by
    intro i j hlt hf
    have hk : σ ^ ((j : ℕ) - i) ∈ M.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      have h1 := congrArg (fun g : M →ₐ[ℚ_[p]] Ω => g ⟨y, hy⟩) hf
      simp only [f, AlgHom.comp_apply, IntermediateField.val_mk, AlgEquiv.coe_algHom] at h1
      have hj : (j : ℕ) = (i : ℕ) + ((j : ℕ) - i) := by omega
      rw [hj, pow_add, AlgEquiv.mul_apply] at h1
      exact ((σ ^ (i : ℕ)).injective h1).symm
    have hdvd : ((j : ℕ) - i) ∣ c.factorial :=
      Nat.dvd_factorial (by omega) (by have := j.2; omega)
    obtain ⟨q, hq⟩ := hdvd
    rw [hq, pow_mul]
    exact Subgroup.pow_mem _ hk q
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h hfij
  · exact key j i h hfij.symm

section tower

variable (p)
variable (Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)) (hmono : Monotone Km)

include hmono

def towerSubmodule : Submodule ℚ_[p] ℂ_[p] where
  carrier := ⋃ m : ℕ, Set.range fun k : Km m => ((k : Ω) : ℂ_[p])
  zero_mem' := Set.mem_iUnion.mpr ⟨0, ⟨0, by simp⟩⟩
  add_mem' := by
    intro u v hu hv
    obtain ⟨m, ⟨k, rfl⟩⟩ := Set.mem_iUnion.mp hu
    obtain ⟨n, ⟨l, rfl⟩⟩ := Set.mem_iUnion.mp hv
    refine Set.mem_iUnion.mpr ⟨max m n, ⟨⟨(k : Ω) + l, ?_⟩, ?_⟩⟩
    · exact add_mem (hmono (le_max_left m n) k.2) (hmono (le_max_right m n) l.2)
    · simp [Completion.coe_add]
  smul_mem' := by
    intro a u hu
    obtain ⟨m, ⟨k, rfl⟩⟩ := Set.mem_iUnion.mp hu
    refine Set.mem_iUnion.mpr ⟨m, ⟨⟨algebraMap ℚ_[p] Ω a * (k : Ω), ?_⟩, ?_⟩⟩
    · exact mul_mem (algebraMap_mem (Km m) a) k.2
    · simp only
      rw [Completion.coe_mul, Algebra.smul_def, IsScalarTower.algebraMap_apply ℚ_[p] Ω ℂ_[p]]
      rfl

lemma coe_towerSubmodule_topologicalClosure :
    ((towerSubmodule p Km hmono).topologicalClosure : Set ℂ_[p]) =
      PadicComplex.towerClosure p Km := by
  rw [Submodule.topologicalClosure_coe]
  rfl

lemma mem_towerClosure_iff (z : ℂ_[p]) :
    z ∈ PadicComplex.towerClosure p Km ↔ z ∈ (towerSubmodule p Km hmono).topologicalClosure := by
  rw [← SetLike.mem_coe, coe_towerSubmodule_topologicalClosure]

lemma add_mem_towerClosure {z w : ℂ_[p]} (hz : z ∈ PadicComplex.towerClosure p Km)
    (hw : w ∈ PadicComplex.towerClosure p Km) : z + w ∈ PadicComplex.towerClosure p Km := by
  rw [mem_towerClosure_iff p Km hmono] at hz hw ⊢
  exact add_mem hz hw

lemma algebraMap_mul_mem_towerClosure (a : ℚ_[p]) {z : ℂ_[p]}
    (hz : z ∈ PadicComplex.towerClosure p Km) :
    algebraMap ℚ_[p] ℂ_[p] a * z ∈ PadicComplex.towerClosure p Km := by
  rw [mem_towerClosure_iff p Km hmono] at hz ⊢
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ a hz

lemma sum_mem_towerClosure {ι : Type*} (s : Finset ι) (g : ι → ℂ_[p])
    (hg : ∀ i ∈ s, g i ∈ PadicComplex.towerClosure p Km) :
    ∑ i ∈ s, g i ∈ PadicComplex.towerClosure p Km := by
  rw [mem_towerClosure_iff p Km hmono]
  exact Submodule.sum_mem _ fun i hi => (mem_towerClosure_iff p Km hmono _).mp (hg i hi)

end tower

private lemma _root_.PadicComplex.IsTateTrace.map_algebraMap_mul
    {Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)} {m : ℕ} {d : ℝ} {R : ℂ_[p] → ℂ_[p]}
    (hR : PadicComplex.IsTateTrace p Km m d R) (a : ℚ_[p]) {z : ℂ_[p]}
    (hz : z ∈ PadicComplex.towerClosure p Km) :
    R (algebraMap ℚ_[p] ℂ_[p] a * z) = algebraMap ℚ_[p] ℂ_[p] a * R z := by
  have h := hR.map_mul_left (algebraMap ℚ_[p] (Km m) a) z hz
  have hcoe : (((algebraMap ℚ_[p] (Km m) a : Km m) : Ω) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] a := by
    rw [IsScalarTower.algebraMap_apply ℚ_[p] Ω ℂ_[p]]
    rfl
  rwa [hcoe] at h


private lemma _root_.PadicComplex.IsTateTrace.map_sum_algebraMap_mul
    {Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)} (hmono : Monotone Km)
    {m : ℕ} {d : ℝ} {R : ℂ_[p] → ℂ_[p]}
    (hR : PadicComplex.IsTateTrace p Km m d R) {ι : Type*} (s : Finset ι) (a : ι → ℚ_[p])
    (g : ι → ℂ_[p]) (hg : ∀ i ∈ s, g i ∈ PadicComplex.towerClosure p Km) :
    R (∑ i ∈ s, algebraMap ℚ_[p] ℂ_[p] (a i) * g i) =
      ∑ i ∈ s, algebraMap ℚ_[p] ℂ_[p] (a i) * R (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      have h0 := hR.apply_coe 0
      simpa using h0
  | insert j s hj ih =>
      have hg' : ∀ i ∈ s, g i ∈ PadicComplex.towerClosure p Km :=
        fun i hi => hg i (Finset.mem_insert_of_mem hi)
      have hgj : g j ∈ PadicComplex.towerClosure p Km := hg j (Finset.mem_insert_self j s)
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        hR.map_add _ (algebraMap_mul_mem_towerClosure p Km hmono _ hgj)
          _ (sum_mem_towerClosure p Km hmono s _
              (fun i hi => algebraMap_mul_mem_towerClosure p Km hmono _ (hg' i hi))),
        ih hg', hR.map_algebraMap_mul (a j) hgj]


section main

variable (p)
variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))
  (Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)) (hmono : Monotone Km)
  (hK : ∀ m, K ≤ Km m)
  {L : Type*} [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
  (ψ : K.fixingSubgroup →* Lˣ)
  (hψ' : ∀ σ : K.fixingSubgroup,
    (∀ m, (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ∈ (Km m).fixingSubgroup) → ψ σ = 1)
  (x : ℂ_[p] ⊗[ℚ_[p]] L)
  (hψ : ∀ σ : K.fixingSubgroup,
    Algebra.TensorProduct.map
        (PadicComplex.galAlgHom p (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) (AlgHom.id ℚ_[p] L)
        x =
      ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] ((ψ σ : Lˣ) : L)) * x)

include hmono hK hψ' hψ

omit [FiniteDimensional ℚ_[p] L] in

lemma coord_mem_towerClosure {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ_[p] L)
    (i : ι) : coord p b x i ∈ PadicComplex.towerClosure p Km := by
  set Kinf : IntermediateField ℚ_[p] Ω := ⨆ m, Km m with hKinf
  have hfix : ∀ σ : Γ, σ ∈ Kinf.fixingSubgroup → σ • coord p b x i = coord p b x i := by
    intro σ hσ
    have hσK : σ ∈ K.fixingSubgroup :=
      IntermediateField.fixingSubgroup_le ((hK 0).trans (le_iSup Km 0)) hσ
    have hσm : ∀ m, σ ∈ (Km m).fixingSubgroup := fun m =>
      IntermediateField.fixingSubgroup_le (le_iSup Km m) hσ
    have h1 : ψ ⟨σ, hσK⟩ = 1 := hψ' ⟨σ, hσK⟩ hσm
    have h2 := hψ ⟨σ, hσK⟩
    rw [h1, Units.val_one, ← Algebra.TensorProduct.one_def, one_mul] at h2
    have h3 : coord p b (Algebra.TensorProduct.map (PadicComplex.galAlgHom p σ)
        (AlgHom.id ℚ_[p] L) x) i = coord p b x i := congrArg (coord p b · i) h2
    rwa [coord_map_gal] at h3
  have hmem :=
    (PadicComplex.forall_smul_eq_self_iff_mem_closure p Kinf (coord p b x i)).mp hfix
  have hset : (Set.range fun k : Kinf => ((k : Ω) : ℂ_[p])) =
      ⋃ m, Set.range fun k : Km m => ((k : Ω) : ℂ_[p]) := by
    ext z
    constructor
    · rintro ⟨k, rfl⟩
      have hk : (k : Ω) ∈ ((⨆ m, Km m : IntermediateField ℚ_[p] Ω) : Set Ω) := k.2
      rw [IntermediateField.coe_iSup_of_directed hmono.directed_le] at hk
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hk
      exact Set.mem_iUnion.mpr ⟨m, ⟨⟨(k : Ω), hm⟩, rfl⟩⟩
    · intro hz
      obtain ⟨m, ⟨k, rfl⟩⟩ := Set.mem_iUnion.mp hz
      exact ⟨⟨(k : Ω), (le_iSup Km m) k.2⟩, rfl⟩
  rw [hset] at hmem
  exact hmem

omit [FiniteDimensional ℚ_[p] L] in

lemma apply_eq_one_of_generator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℚ_[p] L) (i₁ : ι)
    {m₁ : ℕ} (k₁ : Km m₁) {ε : ℝ}
    (hk₁ : ‖coord p b x i₁ - ((k₁ : Ω) : ℂ_[p])‖ < ε)
    {d : ℝ} (hε : (|d| + 1) * ε ≤ ‖coord p b x i₁‖)
    {m : ℕ} (hm : m₁ ≤ m) {R : ℂ_[p] → ℂ_[p]} (hR : PadicComplex.IsTateTrace p Km m d R)
    (σ : Γ) (hσ : σ ∈ (Km m).fixingSubgroup) (hσ' : σ ∉ (Km (m + 1)).fixingSubgroup) :
    ψ ⟨σ, IntermediateField.fixingSubgroup_le (hK m) hσ⟩ = 1 := by
  have hσK : σ ∈ K.fixingSubgroup := IntermediateField.fixingSubgroup_le (hK m) hσ
  by_contra hne
  set ℓ : L := ((ψ ⟨σ, hσK⟩ : Lˣ) : L) with hℓ
  have hℓ1 : ℓ - 1 ≠ 0 := by
    intro h
    apply hne
    rw [sub_eq_zero] at h
    exact Units.ext h

  set c : ι → ℂ_[p] := fun i => coord p b x i with hc
  have hcX : ∀ i, c i ∈ PadicComplex.towerClosure p Km := fun i =>
    coord_mem_towerClosure p K Km hmono hK ψ hψ' x hψ b i
  set A : Matrix ι ι ℚ_[p] := Algebra.leftMulMatrix b ℓ with hA

  have hE1 : ∀ i, σ • c i = ∑ j, algebraMap ℚ_[p] ℂ_[p] (A i j) * c j := by
    intro i
    have h := congrArg (fun z => coord p b z i) (hψ ⟨σ, hσK⟩)
    simp only [coord_map_gal, coord_one_tmul_mul] at h
    exact h

  have hE2 : ∀ i, R (c i) = ∑ j, algebraMap ℚ_[p] ℂ_[p] (A i j) * R (c j) := by
    intro i
    have h1 : R (σ • c i) = R (c i) := hR.apply_smul σ hσ (c i) (hcX i)
    rw [← h1, hE1 i]
    exact hR.map_sum_algebraMap_mul hmono Finset.univ (fun j => A i j) c (fun j _ => hcX j)

  have hRc : ∀ j, R (c j) = 0 := by
    set A' : Matrix ι ι ℂ_[p] := (algebraMap ℚ_[p] ℂ_[p]).mapMatrix (A - 1) with hA'
    have hunit : IsUnit A' := by
      have h1 : IsUnit (ℓ - 1) := isUnit_iff_ne_zero.mpr hℓ1
      have h2 : IsUnit (A - 1) := by
        have : A - 1 = Algebra.leftMulMatrix b (ℓ - 1) := by
          rw [map_sub, map_one]
        rw [this]
        exact h1.map _
      exact h2.map _
    have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hunit
    set v : ι → ℂ_[p] := fun j => R (c j) with hv
    have hv0 : A' *ᵥ v = A' *ᵥ 0 := by
      rw [Matrix.mulVec_zero]
      ext i
      rw [hA', map_sub, map_one, Matrix.sub_mulVec, Pi.sub_apply, Matrix.one_mulVec,
        Pi.zero_apply, sub_eq_zero, RingHom.mapMatrix_apply, Matrix.mulVec, dotProduct]
      simp only [Matrix.map_apply]
      exact (hE2 i).symm
    have := hinj hv0
    intro j
    exact congrFun this j

  have hest := hR.norm_sub_apply_le σ hσ hσ' (c i₁) (hcX i₁)
  rw [hRc i₁, sub_zero] at hest

  have hk₁m : (k₁ : Ω) ∈ Km m := hmono hm k₁.2
  have hσk : σ • ((k₁ : Ω) : ℂ_[p]) = ((k₁ : Ω) : ℂ_[p]) := by
    rw [PadicComplex.smul_coe]
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
    rw [hσ _ hk₁m]
  have hmove : ‖σ • c i₁ - c i₁‖ ≤ ‖c i₁ - ((k₁ : Ω) : ℂ_[p])‖ := by
    have hrw : σ • c i₁ - c i₁ =
        σ • (c i₁ - ((k₁ : Ω) : ℂ_[p])) + (-(c i₁ - ((k₁ : Ω) : ℂ_[p]))) := by
      rw [smul_sub, hσk]
      abel
    rw [hrw]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    rw [PadicComplex.norm_smul_eq, norm_neg, max_self]

  have hpos : 0 < ‖c i₁‖ := by
    have h0 : (0 : ℝ) ≤ (|d| + 1) * ε := by
      have : 0 ≤ ‖coord p b x i₁ - ((k₁ : Ω) : ℂ_[p])‖ := norm_nonneg _
      nlinarith [abs_nonneg d]
    have h1 : 0 < ε := lt_of_le_of_lt (norm_nonneg _) hk₁
    rcases eq_or_lt_of_le (norm_nonneg (c i₁)) with h | h
    · exfalso
      have : (|d| + 1) * ε ≤ 0 := by rw [h]; exact hε
      nlinarith [abs_nonneg d]
    · exact h
  have hchain : ‖c i₁‖ < ‖c i₁‖ := by
    calc ‖c i₁‖ ≤ d * ‖σ • c i₁ - c i₁‖ := hest
      _ ≤ |d| * ‖σ • c i₁ - c i₁‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self d) (norm_nonneg _)
      _ ≤ |d| * ‖c i₁ - ((k₁ : Ω) : ℂ_[p])‖ :=
          mul_le_mul_of_nonneg_left hmove (abs_nonneg d)
      _ < (|d| + 1) * ε := by
          have h1 : |d| * ‖c i₁ - ((k₁ : Ω) : ℂ_[p])‖ ≤ |d| * ε :=
            mul_le_mul_of_nonneg_left hk₁.le (abs_nonneg d)
          have h2 : 0 < ε := lt_of_le_of_lt (norm_nonneg _) hk₁
          nlinarith
      _ ≤ ‖c i₁‖ := hε
  exact lt_irrefl _ hchain

lemma exists_level_trivial (hx : x ≠ 0)
    (d : ℝ) (m₀ : ℕ)
    (hR : ∀ m, m₀ ≤ m → ∃ R : ℂ_[p] → ℂ_[p], PadicComplex.IsTateTrace p Km m d R) :
    ∃ M : ℕ, ∀ σ : K.fixingSubgroup, (σ : Γ) ∈ (Km M).fixingSubgroup → ψ σ = 1 := by
  classical
  by_cases hstab : ∃ M, ∀ m, M ≤ m → (Km m).fixingSubgroup ≤ (Km (m + 1)).fixingSubgroup
  ·
    obtain ⟨M, hM⟩ := hstab
    refine ⟨M, fun σ hσ => hψ' σ (fun m => ?_)⟩
    rcases le_total m M with hm | hm
    · exact IntermediateField.fixingSubgroup_le (hmono hm) hσ
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
      clear hm
      induction k with
      | zero => rw [Nat.add_zero]; exact hσ
      | succ k ih =>
          have := hM (M + k) (Nat.le_add_right M k) ih
          rw [← Nat.add_assoc]
          exact this
  · push Not at hstab

    set b := Module.finBasis ℚ_[p] L with hb
    obtain ⟨i₁, hi₁⟩ := exists_coord_ne_zero p b hx
    have hpos : 0 < ‖coord p b x i₁‖ := norm_pos_iff.mpr hi₁
    set ε : ℝ := ‖coord p b x i₁‖ / (|d| + 1) with hεdef
    have hd1 : 0 < |d| + 1 := by positivity
    have hε : 0 < ε := div_pos hpos hd1
    have hεle : (|d| + 1) * ε ≤ ‖coord p b x i₁‖ := by
      rw [hεdef, mul_div_cancel₀ _ hd1.ne']
    have hcX : coord p b x i₁ ∈ PadicComplex.towerClosure p Km :=
      coord_mem_towerClosure p K Km hmono hK ψ hψ' x hψ b i₁
    obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp hcX ε hε
    obtain ⟨m₁, ⟨k₁, rfl⟩⟩ := Set.mem_iUnion.mp hy
    rw [dist_eq_norm] at hdist

    obtain ⟨m, hm, hgen⟩ := hstab (max m₀ m₁)
    obtain ⟨σ₀, hσ₀, hσ₀'⟩ := Set.not_subset.mp hgen
    obtain ⟨R, hR⟩ := hR m ((le_max_left m₀ m₁).trans hm)
    have hm₁ : m₁ ≤ m := (le_max_right m₀ m₁).trans hm

    have hkill : ∀ σ : Γ, ∀ hσ : σ ∈ (Km m).fixingSubgroup, σ ∉ (Km (m + 1)).fixingSubgroup →
        ψ ⟨σ, IntermediateField.fixingSubgroup_le (hK m) hσ⟩ = 1 :=
      fun σ hσ hσ' => apply_eq_one_of_generator p K Km hmono hK ψ hψ' x hψ b i₁ k₁ hdist hεle
        hm₁ hR σ hσ hσ'

    refine ⟨m, fun τ hτ => ?_⟩
    by_cases hτ' : (τ : Γ) ∈ (Km (m + 1)).fixingSubgroup
    · have hσ₀K : σ₀ ∈ K.fixingSubgroup := IntermediateField.fixingSubgroup_le (hK m) hσ₀
      set ρ : Γ := (τ : Γ) * σ₀⁻¹ with hρ
      have hρm : ρ ∈ (Km m).fixingSubgroup := mul_mem hτ (inv_mem hσ₀)
      have hρ' : ρ ∉ (Km (m + 1)).fixingSubgroup := by
        intro h
        apply hσ₀'
        have : σ₀ = ρ⁻¹ * (τ : Γ) := by rw [hρ]; group
        rw [this]
        exact mul_mem (inv_mem h) hτ'
      have h1 := hkill ρ hρm hρ'
      have h2 := hkill σ₀ hσ₀ hσ₀'
      have hτeq : τ = ⟨ρ, IntermediateField.fixingSubgroup_le (hK m) hρm⟩ *
          ⟨σ₀, IntermediateField.fixingSubgroup_le (hK m) hσ₀⟩ := by
        apply Subtype.ext
        show (τ : Γ) = ρ * σ₀
        rw [hρ]; group
      rw [hτeq, map_mul, h1, h2, one_mul]
    · have := hkill (τ : Γ) hτ hτ'
      simpa using this

theorem main (hfin : ∀ m, FiniteDimensional ℚ_[p] (Km m)) (hx : x ≠ 0)
    (d : ℝ) (m₀ : ℕ)
    (hR : ∀ m, m₀ ≤ m → ∃ R : ℂ_[p] → ℂ_[p], PadicComplex.IsTateTrace p Km m d R) :
    ∃ n : ℕ, 0 < n ∧ ∀ σ : K.fixingSubgroup, ψ σ ^ n = 1 := by
  obtain ⟨M, hM⟩ := exists_level_trivial p K Km hmono hK ψ hψ' x hψ hx d m₀ hR
  haveI := hfin M
  obtain ⟨N, hN, hpow⟩ := exists_pow_mem_fixingSubgroup (p := p) (Km M)
  refine ⟨N, hN, fun σ => ?_⟩
  rw [← map_pow]
  apply hM
  simpa using hpow σ

end main


end TraceVanishing

namespace TateTraceTower


open Polynomial

variable (p : ℕ) [Fact p.Prime]

local notation "Ω" => PadicAlgCl p
local notation "Γ" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)

def F (n : ℕ) : IntermediateField ℚ_[p] Ω := PadicAlgCl.cyclotomicTower p (n + 2)

lemma F_mono : Monotone (F p) := fun _ _ h =>
  PadicAlgCl.cyclotomicTower_mono p (Nat.add_le_add_right h 2)

lemma finrank_F (n : ℕ) : Module.finrank ℚ_[p] (F p n) = (p - 1) * p ^ (n + 1) := by
  have h := (PadicAlgCl.finrank_cyclotomicTower_and_pow_mem_fixingSubgroup p).1 (n + 2) (by omega)
  exact h

lemma finiteDimensional_F (n : ℕ) : FiniteDimensional ℚ_[p] (F p n) := by
  apply Module.finite_of_finrank_pos
  rw [finrank_F]
  have hp : p.Prime := Fact.out
  have : 0 < p - 1 := by have := hp.one_lt; omega
  exact Nat.mul_pos this (pow_pos hp.pos _)

lemma stable (n : ℕ) (σ : Γ) (y : Ω) (hy : y ∈ F p n) : σ y ∈ F p n := by
  unfold F PadicAlgCl.cyclotomicTower at hy ⊢
  set S : Set Ω := {ζ : Ω | ζ ^ p ^ (n + 2) = 1} with hS
  have hmap : (IntermediateField.adjoin ℚ_[p] S).map (σ : Ω →ₐ[ℚ_[p]] Ω) ≤
      IntermediateField.adjoin ℚ_[p] S := by
    rw [IntermediateField.adjoin_map]
    apply IntermediateField.adjoin.mono
    rintro _ ⟨ζ, hζ, rfl⟩
    show (σ : Ω →ₐ[ℚ_[p]] Ω) ζ ^ p ^ (n + 2) = 1
    rw [← map_pow, (hζ : ζ ^ p ^ (n + 2) = 1), map_one]
  exact hmap ⟨y, hy, rfl⟩

lemma hdeg (m n : ℕ) (h : n = m + 1) :
    Module.finrank ℚ_[p] (F p n) = p * Module.finrank ℚ_[p] (F p m) := by
  subst h
  rw [finrank_F, finrank_F]
  ring

lemma hcyc (m : ℕ) (σ : Γ) (hσ : σ ∈ (F p m).fixingSubgroup) (hσ' : σ ∉ (F p (m +
  1)).fixingSubgroup) :
    σ ^ p ∈ (F p (m + 1)).fixingSubgroup ∧ σ ^ p ∉ (F p (m + 2)).fixingSubgroup :=
  (PadicAlgCl.finrank_cyclotomicTower_and_pow_mem_fixingSubgroup p).2 m σ hσ hσ'

def c (m : ℕ) : ℝ := (p : ℝ) ^ (1 / (((p : ℝ) - 1) * (p : ℝ) ^ (m + 1)))

lemma p_pos : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
lemma one_lt_p : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt

lemma exponent_nonneg (m : ℕ) : (0 : ℝ) ≤ 1 / (((p : ℝ) - 1) * (p : ℝ) ^ (m + 1)) := by
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by have := one_lt_p p; linarith
  have h2 : (0 : ℝ) < (p : ℝ) ^ (m + 1) := pow_pos (p_pos p) _
  positivity

lemma one_le_c (m : ℕ) : 1 ≤ c p m := Real.one_le_rpow (one_lt_p p).le (exponent_nonneg p m)

lemma sum_exponent_le (n : ℕ) :
    ∑ m ∈ Finset.range n, 1 / (((p : ℝ) - 1) * (p : ℝ) ^ (m + 1)) ≤ 1 / ((p : ℝ) - 1) ^ 2 := by
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by have := one_lt_p p; linarith
  have hp0 : (0 : ℝ) < p := p_pos p
  set x : ℝ := (p : ℝ)⁻¹ with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hx1 : x < 1 := by rw [hx]; exact inv_lt_one_of_one_lt₀ (one_lt_p p)

  have hterm : ∀ m, 1 / (((p : ℝ) - 1) * (p : ℝ) ^ (m + 1)) = ((p : ℝ) - 1)⁻¹ * (x * x ^ m) := by
    intro m
    rw [hx, ← pow_succ', inv_pow]
    field_simp
  simp_rw [hterm]
  rw [← Finset.mul_sum, ← Finset.mul_sum]

  have hgeom : ∑ m ∈ Finset.range n, x ^ m ≤ (1 - x)⁻¹ := by
    have h := geom_sum_eq hx1.ne n
    rw [h]
    have h1 : 0 < 1 - x := by linarith
    have h2 : (x ^ n - 1) / (x - 1) = (1 - x ^ n) / (1 - x) := by
      have hx1' : x - 1 ≠ 0 := by linarith
      have h1' : 1 - x ≠ 0 := by linarith
      field_simp
      ring
    rw [h2, inv_eq_one_div, div_le_div_iff_of_pos_right h1]
    linarith [pow_nonneg hx0 n]
  have hkey : ((p : ℝ) - 1)⁻¹ * (x * ∑ m ∈ Finset.range n, x ^ m) ≤ ((p : ℝ) - 1)⁻¹ * (x * (1 -
    x)⁻¹) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgeom hx0) (by positivity)
  refine hkey.trans (le_of_eq ?_)
  rw [hx]
  have hp1' : (p : ℝ) - 1 ≠ 0 := hp1.ne'
  have hpx : (1 : ℝ) - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / p := by field_simp
  rw [hpx]
  field_simp

lemma prod_c_le (n : ℕ) : ∏ m ∈ Finset.range n, c p m ≤ (p : ℝ) ^ (1 / ((p : ℝ) - 1) ^ 2) := by
  unfold c
  rw [← Real.rpow_sum_of_pos (p_pos p)]
  exact Real.rpow_le_rpow_of_exponent_le (one_lt_p p).le (sum_exponent_le p n)

lemma htr (m : ℕ) (σ : Γ) (hσ : σ ∈ (F p m).fixingSubgroup) (hσ' : σ ∉ (F p (m + 1)).fixingSubgroup)
    (y : Ω) (hy : y ∈ F p (m + 1)) :
    ‖∑ i ∈ Finset.range p, (σ ^ i) y‖ ≤ ‖(p : ℚ_[p])‖ * c p m * ‖y‖ :=
  PadicAlgCl.norm_sum_pow_apply_le_of_mem_cyclotomicTower p m σ hσ hσ' y hy

theorem main : ∃ d : ℝ, 0 < d ∧ ∀ m : ℕ, ∃ R : ℂ_[p] → ℂ_[p],
    PadicComplex.IsTateTrace p (fun n => PadicAlgCl.cyclotomicTower p (n + 2)) m d R :=
  PadicComplex.exists_isTateTrace_of_norm_sum_pow_apply_le p (F p) (F_mono p)
    (finiteDimensional_F p) (fun m σ _ y hy => stable p m σ y hy) (hdeg p) (hcyc p)
    (c p) ((p : ℝ) ^ (1 / ((p : ℝ) - 1) ^ 2)) (one_le_c p) (prod_c_le p) (htr p)

end TateTraceTower

namespace PadicComplex

/-- Tate traces exist along the cyclotomic tower, with a uniform
constant independent of the level. -/
public theorem exists_isTateTrace_cyclotomicTower (p : ℕ) [Fact p.Prime] :
    ∃ d : ℝ, 0 < d ∧ ∀ m : ℕ, ∃ R : ℂ_[p] → ℂ_[p],
      PadicComplex.IsTateTrace p (fun n => PadicAlgCl.cyclotomicTower p (n + 2)) m d R :=
  TateTraceTower.main p

/-- If a tensor satisfies the eigenrelation for every automorphism
fixing `K`, and the Tate traces along a tower above `K` exist, then
some positive power of every eigenvalue `ψ σ` is trivial. -/
public theorem exists_forall_pow_eq_one_of_isTateTrace_of_tmul_eq_mul
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)) (hmono : Monotone Km)
    (hK : ∀ m, K ≤ Km m) (hfin : ∀ m, FiniteDimensional ℚ_[p] (Km m))
    (d : ℝ) (m₀ : ℕ)
    (hR : ∀ m, m₀ ≤ m → ∃ R : ℂ_[p] → ℂ_[p], PadicComplex.IsTateTrace p Km m d R)
    (L : Type*) [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    (ψ : K.fixingSubgroup →* Lˣ)
    (hψ' : ∀ σ : K.fixingSubgroup,
      (∀ m, (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ∈ (Km m).fixingSubgroup) → ψ σ = 1)
    (x : ℂ_[p] ⊗[ℚ_[p]] L) (hx : x ≠ 0)
    (hψ : ∀ σ : K.fixingSubgroup,
      Algebra.TensorProduct.map
          (PadicComplex.galAlgHom p (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) (AlgHom.id ℚ_[p] L)
          x =
        ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] ((ψ σ : Lˣ) : L)) * x) :
    ∃ n : ℕ, 0 < n ∧ ∀ σ : K.fixingSubgroup, ψ σ ^ n = 1 :=
  TraceVanishing.main p K Km hmono hK ψ hψ' x hψ hfin hx d m₀ hR

end PadicComplex

namespace FullVanishing


open scoped NNReal TensorProduct

variable {p : ℕ} [Fact p.Prime]

local notation "Ω" => PadicAlgCl p
local notation "Γ" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)

section tower

variable (p)

abbrev F (n : ℕ) : IntermediateField ℚ_[p] (PadicAlgCl p) := PadicAlgCl.cyclotomicTower p n

def rootSet (n : ℕ) : Set Ω := {ζ : Ω | ζ ^ (p ^ n) = 1}

lemma F_eq_adjoin (n : ℕ) : F p n = IntermediateField.adjoin ℚ_[p] (rootSet p n) := rfl

lemma rootSet_finite (n : ℕ) : (rootSet p n).Finite := by
  classical
  have hpn : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  refine (Polynomial.nthRoots (p ^ n) (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
  simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hpn]
  exact hζ

scoped instance F_finiteDimensional (n : ℕ) : FiniteDimensional ℚ_[p] (F p n) := by
  haveI : Finite (rootSet p n) := (rootSet_finite p n).to_subtype
  rw [F_eq_adjoin]
  exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

lemma F_mono : Monotone (F p) := PadicAlgCl.cyclotomicTower_mono p

lemma mem_fixingSubgroup_F_of_forall (g : Γ) (n : ℕ)
    (h : ∀ ζ : Ω, ζ ^ (p ^ n) = 1 → g ζ = ζ) : g ∈ (F p n).fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  rw [F_eq_adjoin] at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap x => exact g.commutes x
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | inv x _ hx => rw [map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

lemma apply_eq_of_mem_fixingSubgroup {E : IntermediateField ℚ_[p] Ω} {g : Γ}
    (hg : g ∈ E.fixingSubgroup) {y : Ω} (hy : y ∈ E) : g y = y :=
  (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg y hy

def χ (g : Γ) : ℤ_[p]ˣ := cyclotomicCharacter (PadicAlgCl p) p (g : Ω ≃ₐ[ℚ_[p]] Ω).toRingEquiv

lemma toRingEquiv_mul (g h : Γ) : (g * h).toRingEquiv = g.toRingEquiv * h.toRingEquiv := rfl

lemma χ_mul (g h : Γ) : χ p (g * h) = χ p g * χ p h := by
  unfold χ; rw [toRingEquiv_mul, map_mul]

lemma χ_one : χ p 1 = 1 := by unfold χ; exact map_one _

lemma χ_pow (g : Γ) (n : ℕ) : χ p (g ^ n) = χ p g ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, χ_one]
  | succ n ih => rw [pow_succ, pow_succ, χ_mul, ih]

lemma toZModPow_χ_eq_one {g : Γ} {n : ℕ} (hg : g ∈ (F p n).fixingSubgroup) :
    PadicInt.toZModPow n (χ p g : ℤ_[p]) = 1 := by
  unfold χ
  rw [cyclotomicCharacter.toZModPow]
  have hu := modularCyclotomicCharacter.unique (PadicAlgCl p)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω (p ^ n))
    (g : Ω ≃ₐ[ℚ_[p]] Ω).toRingEquiv (c := 1) ?_
  · rw [← hu]
  · intro t ht
    have ht' : ((t : Ωˣ) : Ω) ^ (p ^ n) = 1 := by
      have := (mem_rootsOfUnity _ t).1 ht
      rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
    have hfix : g ((t : Ωˣ) : Ω) = t :=
      apply_eq_of_mem_fixingSubgroup p hg (PadicAlgCl.mem_cyclotomicTower_of_pow_eq_one p ht')
    show g ((t : Ωˣ) : Ω) = _
    rw [hfix, ZMod.val_one_eq_one_mod]
    rcases Nat.lt_or_ge 1 (p ^ n) with h1 | h1
    · rw [Nat.mod_eq_of_lt h1, pow_one]
    · have hpn : p ^ n = 1 := le_antisymm h1 (pow_pos (Fact.out : p.Prime).pos n)
      rw [hpn, Nat.mod_self, pow_zero]
      rw [hpn, pow_one] at ht'
      exact ht'

lemma mem_fixingSubgroup_F_of_χ_eq_one {g : Γ} (hg : χ p g = 1) (n : ℕ) :
    g ∈ (F p n).fixingSubgroup := by
  refine mem_fixingSubgroup_F_of_forall p g n fun ζ hζ => ?_
  have h := cyclotomicCharacter.spec p (g : Ω ≃ₐ[ℚ_[p]] Ω).toRingEquiv ζ hζ
  change g ζ = ζ ^ ((PadicInt.toZModPow n) (χ p g : ℤ_[p])).val at h
  rw [hg, Units.val_one, map_one, ZMod.val_one_eq_one_mod] at h
  rw [h]
  rcases Nat.lt_or_ge 1 (p ^ n) with h1 | h1
  · rw [Nat.mod_eq_of_lt h1, pow_one]
  · have hpn : p ^ n = 1 := le_antisymm h1 (pow_pos (Fact.out : p.Prime).pos n)
    rw [hpn, Nat.mod_self, pow_zero]
    rw [hpn, pow_one] at hζ
    exact hζ.symm

lemma χ_eq_one_of_forall {g : Γ} (hg : ∀ n, g ∈ (F p n).fixingSubgroup) : χ p g = 1 := by
  apply Units.ext
  refine PadicInt.ext_of_toZModPow.1 fun n => ?_
  rw [toZModPow_χ_eq_one p (hg n), Units.val_one, map_one]

end tower

section gen

variable (p)

abbrev Fm (m : ℕ) : IntermediateField ℚ_[p] (PadicAlgCl p) := F p (m + 2)

lemma Fm_mono : Monotone (Fm p) := fun a b hab => F_mono p (by omega)

def IsGen (m : ℕ) (σ : Γ) : Prop :=
  σ ∈ (Fm p m).fixingSubgroup ∧ σ ∉ (Fm p (m + 1)).fixingSubgroup

lemma hcyc (m : ℕ) (σ : Γ) (h1 : σ ∈ (Fm p m).fixingSubgroup)
    (h2 : σ ∉ (Fm p (m + 1)).fixingSubgroup) :
    σ ^ p ∈ (Fm p (m + 1)).fixingSubgroup ∧ σ ^ p ∉ (Fm p (m + 2)).fixingSubgroup :=
  (PadicAlgCl.finrank_cyclotomicTower_and_pow_mem_fixingSubgroup p).2 m σ h1 h2

lemma finrank_Fm (m : ℕ) : Module.finrank ℚ_[p] (Fm p m) = (p - 1) * p ^ (m + 1) := by
  have h := (PadicAlgCl.finrank_cyclotomicTower_and_pow_mem_fixingSubgroup p).1 (m + 2) (by omega)
  rw [show m + 2 - 1 = m + 1 by omega] at h
  exact h

variable {p}

lemma isGen_pow {m : ℕ} {σ : Γ} (hσ : IsGen p m σ) (j : ℕ) : IsGen p (m + j) (σ ^ (p ^ j)) := by
  induction j with
  | zero => simpa using hσ
  | succ j ih =>
      have h := hcyc p (m + j) _ ih.1 ih.2
      refine ⟨?_, ?_⟩
      · rw [pow_succ, pow_mul]; exact h.1
      · rw [pow_succ, pow_mul]; exact h.2

lemma pow_mem_fixingSubgroup_succ_iff {m : ℕ} {σ : Γ} (hσ : IsGen p m σ) (i : ℕ) :
    σ ^ i ∈ (Fm p (m + 1)).fixingSubgroup ↔ p ∣ i := by
  constructor
  · intro hi
    by_contra hpi
    have hcop : Nat.Coprime i p :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpi)
    obtain ⟨a, ha⟩ : ∃ a : ℕ, i * a % p = 1 := by
      obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (Fact.out : p.Prime).one_lt
      exact ⟨a, ha⟩
    have hdiv : a * i = p * (a * i / p) + 1 := by
      have := Nat.div_add_mod (a * i) p
      rw [mul_comm] at ha
      omega
    apply hσ.2
    have h1 : σ ^ (a * i) ∈ (Fm p (m + 1)).fixingSubgroup := by
      rw [mul_comm, pow_mul]; exact Subgroup.pow_mem _ hi a
    have h2 : σ ^ (p * (a * i / p)) ∈ (Fm p (m + 1)).fixingSubgroup := by
      rw [pow_mul]; exact Subgroup.pow_mem _ (hcyc p m σ hσ.1 hσ.2).1 _
    rw [hdiv, pow_add, pow_one] at h1
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ h2) h1
    simpa using this
  · rintro ⟨k, rfl⟩
    rw [pow_mul]
    exact Subgroup.pow_mem _ (hcyc p m σ hσ.1 hσ.2).1 k

lemma exists_pow_not_mem {m : ℕ} {σ : Γ} (hσ : IsGen p m σ) {i : ℕ} (hi : 0 < i) :
    ∃ n, σ ^ i ∉ (Fm p n).fixingSubgroup := by
  induction i using Nat.strong_induction_on generalizing m σ with
  | _ i ih =>
    by_cases hpi : p ∣ i
    · obtain ⟨j, rfl⟩ := hpi
      have hj : 0 < j := Nat.pos_of_mul_pos_left hi
      have hlt : j < p * j := lt_mul_left hj (Fact.out : p.Prime).one_lt
      have hg : IsGen p (m + 1) (σ ^ p) := by simpa using isGen_pow hσ 1
      obtain ⟨n, hn⟩ := ih j hlt hg hj
      exact ⟨n, by rwa [pow_mul]⟩
    · exact ⟨m + 1, fun h => hpi ((pow_mem_fixingSubgroup_succ_iff hσ i).1 h)⟩

lemma χ_zpow_ne_one {m : ℕ} {σ : Γ} (hσ : IsGen p m σ) {z : ℤ} (hz : z ≠ 0) :
    (χ p σ) ^ z ≠ 1 := by
  have key : ∀ i : ℕ, 0 < i → χ p σ ^ i ≠ 1 := by
    intro i hi h
    obtain ⟨n, hn⟩ := exists_pow_not_mem hσ hi
    exact hn (mem_fixingSubgroup_F_of_χ_eq_one p (by rw [χ_pow, h]) (n + 2))
  rcases Int.eq_nat_or_neg z with ⟨i, rfl | rfl⟩
  · have hi : 0 < i := by omega
    rw [zpow_natCast]; exact key i hi
  · have hi : 0 < i := by omega
    rw [zpow_neg, zpow_natCast, Ne, inv_eq_one]; exact key i hi

variable (p)

lemma exists_isGen (m₀ : ℕ) : ∃ m, m₀ ≤ m ∧ ∃ σ : Γ, IsGen p m σ := by
  by_contra hcon
  push Not at hcon
  have hstep : ∀ j, (Fm p m₀).fixingSubgroup ≤ (Fm p (m₀ + j)).fixingSubgroup := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        intro τ hτ
        have h1 : τ ∈ (Fm p (m₀ + j)).fixingSubgroup := ih hτ
        by_contra h2
        exact hcon (m₀ + j) (by omega) τ ⟨h1, by rwa [show m₀ + (j + 1) = m₀ + j + 1 by ring] at h2⟩
  have hle : ∀ j, Fm p (m₀ + j) ≤ Fm p m₀ := by
    intro j
    have := (IntermediateField.le_iff_le _ _).2 (hstep j)
    rwa [InfiniteGalois.fixedField_fixingSubgroup] at this
  have hfin : ∀ j, Module.finrank ℚ_[p] (Fm p (m₀ + j)) ≤ Module.finrank ℚ_[p] (Fm p m₀) := fun j =>
    IntermediateField.finrank_le_of_le_right (hle j)
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  set A := Module.finrank ℚ_[p] (Fm p m₀) with hA
  have h := hfin A
  rw [finrank_Fm] at h
  have h1 : p ^ (m₀ + A + 1) ≤ A := by
    calc p ^ (m₀ + A + 1) ≤ (p - 1) * p ^ (m₀ + A + 1) := Nat.le_mul_of_pos_left _ (by omega)
      _ ≤ A := h
  have h2 : A < p ^ A := Nat.lt_pow_self hp1
  have h3 : p ^ A ≤ p ^ (m₀ + A + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

end gen

section lgc

variable (p)

scoped instance neZero_prime_rat : NeZero ((p : ℕ) : ℚ) :=
  ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩

theorem cyclotomicCharacter_localGaloisToGlobal (σ : Γ) :
    cyclotomicCharacter (AlgebraicClosure ℚ) p (localGaloisToGlobal p σ).toRingEquiv = χ p σ := by
  apply Units.ext
  refine PadicInt.ext_of_toZModPow.1 fun n => ?_
  set a := PadicInt.toZModPow n
    ((cyclotomicCharacter (AlgebraicClosure ℚ) p (localGaloisToGlobal p σ).toRingEquiv : ℤ_[p]ˣ) :
      ℤ_[p])
    with ha

  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) (p ^ n)
  have hζ : IsPrimitiveRoot (padicEmbedding p ζ₀) (p ^ n) :=
    hζ₀.map_of_injective (padicEmbedding p).toRingHom.injective
  have hσζ : σ (padicEmbedding p ζ₀) = (padicEmbedding p ζ₀) ^ a.val := by
    rw [← padicEmbedding_localGaloisToGlobal, ← map_pow]
    congr 1
    exact cyclotomicCharacter.spec p (localGaloisToGlobal p σ).toRingEquiv ζ₀ hζ₀.pow_eq_one
  unfold χ
  rw [cyclotomicCharacter.toZModPow]
  refine modularCyclotomicCharacter.unique (PadicAlgCl p)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω (p ^ n))
    (σ : Ω ≃ₐ[ℚ_[p]] Ω).toRingEquiv (c := a) fun t ht => ?_
  have ht' : ((t : Ωˣ) : Ω) ^ (p ^ n) = 1 := by
    have := (mem_rootsOfUnity _ t).1 ht
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one ht'
  show σ ((t : Ωˣ) : Ω) = _
  rw [← hi, map_pow, hσζ, ← pow_mul, mul_comm, pow_mul]

end lgc

end FullVanishing

/-- The cyclotomic character computed through the global Galois group
agrees with the one computed in the `p`-adic algebraic closure. -/
public theorem cyclotomicCharacter_localGaloisToGlobal (p : ℕ) [Fact p.Prime]
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    cyclotomicCharacter (AlgebraicClosure ℚ) p (localGaloisToGlobal p σ).toRingEquiv =
      cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv :=
  FullVanishing.cyclotomicCharacter_localGaloisToGlobal p σ

namespace PadicComplex

open FullVanishing in
/-- Tate vanishing for the full `p`-adic Galois group: a nonzero
cyclotomic eigenspace in `ℂ_[p]` does not exist. An element transforming
by `χ ^ k` with `k ≠ 0` under every automorphism must be zero. -/
public theorem eq_zero_of_forall_smul_eq_cyclotomicCharacter_zpow_mul
    (p : ℕ) [Fact p.Prime] (k : ℤ) (hk : k ≠ 0) (c : ℂ_[p])
    (hc : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      σ • c =
        (algebraMap ℚ_[p] ℂ_[p]
            (((cyclotomicCharacter (AlgebraicClosure ℚ) p (localGaloisToGlobal p σ).toRingEquiv :
                ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])) ^ k * c) :
    c = 0 := by
  by_contra hc0
  let Kb : IntermediateField ℚ_[p] (PadicAlgCl p) := ⊥
  let χQ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* ℚ_[p]ˣ :=
    (Units.map (PadicInt.Coe.ringHom (p := p) : ℤ_[p] →* ℚ_[p])).comp
      ((cyclotomicCharacter (PadicAlgCl p) p).comp
        (MonoidHom.mk' (fun σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p => σ.toRingEquiv)
          (fun _ _ => rfl)))
  have hχQ : ∀ σ, ((χQ σ : ℚ_[p]ˣ) : ℚ_[p]) = ((χ p σ : ℤ_[p]) : ℚ_[p]) := fun σ => rfl
  let ψ : Kb.fixingSubgroup →* ℚ_[p]ˣ := (zpowGroupHom k).comp (χQ.comp (Subgroup.subtype _))
  have hψ : ∀ σ : Kb.fixingSubgroup, ((ψ σ : ℚ_[p]ˣ) : ℚ_[p]) =
      ((χ p σ : ℤ_[p]) : ℚ_[p]) ^ k := by
    intro σ
    simp only [ψ, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      zpowGroupHom_apply, Units.val_zpow_eq_zpow_val, hχQ]
  let x : TensorProduct ℚ_[p] ℂ_[p] ℚ_[p] := c ⊗ₜ[ℚ_[p]] (1 : ℚ_[p])
  have hx : x ≠ 0 := by
    intro h
    apply hc0
    have h2 : (TensorProduct.rid ℚ_[p] ℂ_[p]) x = (TensorProduct.rid ℚ_[p] ℂ_[p]) 0 := by
      rw [h]
    rw [LinearEquiv.map_zero] at h2
    simpa [x] using h2
  have hxσ : ∀ σ : Kb.fixingSubgroup,
      Algebra.TensorProduct.map
          (PadicComplex.galAlgHom p (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))
          (AlgHom.id ℚ_[p] ℚ_[p]) x =
        ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] ((ψ σ : ℚ_[p]ˣ) : ℚ_[p])) * x := by
    intro σ
    simp only [x, Algebra.TensorProduct.map_tmul, PadicComplex.galAlgHom_apply, AlgHom.coe_id,
      id_eq, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [hc, FullVanishing.cyclotomicCharacter_localGaloisToGlobal, hψ, ← map_zpow₀,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, TensorProduct.smul_tmul]
    simp [χ]
  obtain ⟨d, -, hR⟩ := PadicComplex.exists_isTateTrace_cyclotomicTower p
  have hψ' : ∀ σ : Kb.fixingSubgroup,
      (∀ m, (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ∈ (Fm p m).fixingSubgroup) →
        ψ σ = 1 := by
    intro σ hσ
    have hall : ∀ n, (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ∈ (F p n).fixingSubgroup :=
      fun n => IntermediateField.fixingSubgroup_le (F_mono p (Nat.le_add_right n 2)) (hσ n)
    have h1 : χ p σ = 1 := χ_eq_one_of_forall p hall
    apply Units.ext
    rw [hψ, h1, Units.val_one, Units.val_one, PadicInt.coe_one, one_zpow]
  obtain ⟨n, hn, hfin⟩ :=
    PadicComplex.exists_forall_pow_eq_one_of_isTateTrace_of_tmul_eq_mul p Kb (Fm p) (Fm_mono p)
      (fun m => bot_le) (fun m => inferInstance) d 0 (fun m _ => hR m) ℚ_[p] ψ hψ' x hx hxσ
  obtain ⟨m, -, σ, hσ⟩ := exists_isGen p 0
  have hσb : σ ∈ Kb.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    obtain ⟨q, rfl⟩ := IntermediateField.mem_bot.mp hy
    exact σ.commutes q
  have h := congrArg (fun u : ℚ_[p]ˣ => (u : ℚ_[p])) (hfin ⟨σ, hσb⟩)
  simp only [Units.val_pow_eq_pow_val, hψ, Units.val_one] at h
  rw [← zpow_natCast, ← zpow_mul] at h
  have hkn : k * (n : ℤ) ≠ 0 := mul_ne_zero hk (by exact_mod_cast hn.ne')
  apply χ_zpow_ne_one hσ hkn
  have hinjU : Function.Injective
      (Units.map (PadicInt.Coe.ringHom (p := p) : ℤ_[p] →* ℚ_[p])) := by
    intro u v huv
    apply Units.ext
    have h' := congrArg (fun w : ℚ_[p]ˣ => (w : ℚ_[p])) huv
    simp only [Units.coe_map] at h'
    exact Subtype.val_injective h'
  apply hinjU
  rw [map_zpow, map_one]
  apply Units.ext
  rw [Units.val_zpow_eq_zpow_val, Units.val_one]
  exact h

end PadicComplex



set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

private theorem eq_zero_of_forall_mem_smul_eq_of_finiteIndex_aux
    {G : Type*} [Group G] {L : Type*} [Field L] [MulSemiringAction G L]
    (χ : G →* Lˣ) (hχ : ∀ (σ τ : G), σ • ((χ τ : Lˣ) : L) = ((χ τ : Lˣ) : L))
    (hvan : ∀ m : ℤ, m ≠ 0 → ∀ x : L, (∀ σ : G, σ • x = ((χ σ : Lˣ) : L) ^ m * x) → x = 0)
    (H : Subgroup G) [H.FiniteIndex] (k : ℤ) (hk : k ≠ 0) (c : L)
    (hc : ∀ h : G, h ∈ H → h • c = ((χ h : Lˣ) : L) ^ k * c) :
    c = 0 := by
  classical
  letI : Fintype (G ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex

  have hsm : ∀ (σ : G) (x : L), σ • x = MulSemiringAction.toRingHom G L σ x := fun σ x => rfl
  have hχz : ∀ (σ τ : G) (z : ℤ), σ • (((χ τ : Lˣ) : L) ^ z) = ((χ τ : Lˣ) : L) ^ z := by
    intro σ τ z
    rw [hsm, map_zpow₀, ← hsm, hχ]

  let τ : G ⧸ H → G := fun q => q.out
  have hτ : ∀ q : G ⧸ H, (τ q : G ⧸ H) = q := fun q => q.out_eq
  let d : G ⧸ H → L := fun q => ((χ (τ q) : Lˣ) : L) ^ (-k) * (τ q • c)
  have hd : ∀ (σ : G) (q : G ⧸ H), σ • d q = ((χ σ : Lˣ) : L) ^ k * d (σ • q) := by
    intro σ q

    have hmem : (τ (σ • q))⁻¹ * (σ * τ q) ∈ H := by
      rw [← QuotientGroup.eq, hτ, show ((σ * τ q : G) : G ⧸ H) = σ • ((τ q : G) : G ⧸ H) from rfl,
        hτ]
    have hsplit : σ * τ q = τ (σ • q) * ((τ (σ • q))⁻¹ * (σ * τ q)) := by rw [mul_inv_cancel_left]
    have h1 : σ • (τ q • c) = ((((χ (τ (σ • q)))⁻¹ * (χ σ * χ (τ q))) ^ k : Lˣ) : L) * (τ (σ • q)
      • c) := by
      rw [← mul_smul, hsplit, mul_smul, hc _ hmem, smul_mul', hχz, map_mul, map_mul, map_inv,
        Units.val_zpow_eq_zpow_val]

    have key : (χ (τ q)) ^ (-k) * ((χ (τ (σ • q)))⁻¹ * (χ σ * χ (τ q))) ^ k = (χ σ) ^ k * (χ (τ (σ
      • q))) ^ (-k) := by
      set a := χ (τ q)
      set b := χ (τ (σ • q))
      set s := χ σ
      rw [mul_zpow, mul_zpow, inv_zpow']

      rw [mul_comm (s ^ k) (a ^ k), ← mul_assoc, ← mul_assoc, mul_comm (a ^ (-k)) (b ^ (-k)),
        mul_assoc (b ^ (-k)),
        ← zpow_add, neg_add_cancel, zpow_zero, mul_one, mul_comm]
    have keyL : ((χ (τ q) : Lˣ) : L) ^ (-k) * ((((χ (τ (σ • q)))⁻¹ * (χ σ * χ (τ q))) ^ k : Lˣ) :
      L) =
        ((χ σ : Lˣ) : L) ^ k * ((χ (τ (σ • q)) : Lˣ) : L) ^ (-k) := by
      have := congrArg (fun u : Lˣ => (u : L)) key
      simpa only [Units.val_mul, Units.val_zpow_eq_zpow_val] using this
    show σ • (((χ (τ q) : Lˣ) : L) ^ (-k) * (τ q • c)) =
      ((χ σ : Lˣ) : L) ^ k * (((χ (τ (σ • q)) : Lˣ) : L) ^ (-k) * (τ (σ • q) • c))
    rw [smul_mul', hχz, h1, ← mul_assoc, keyL, mul_assoc]

  let P : L := ∏ q : G ⧸ H, d q
  have hP : ∀ σ : G, σ • P = ((χ σ : Lˣ) : L) ^ (k * (Fintype.card (G ⧸ H) : ℤ)) * P := by
    intro σ
    show σ • (∏ q : G ⧸ H, d q) = _ * ∏ q : G ⧸ H, d q
    rw [Finset.smul_prod']
    simp_rw [hd σ]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← zpow_natCast, ← zpow_mul]
    congr 1
    exact Equiv.prod_comp (MulAction.toPerm σ) d
  have hP0 : P = 0 := by
    refine hvan _ ?_ P hP
    exact mul_ne_zero hk (by exact_mod_cast Fintype.card_ne_zero)
  obtain ⟨q, -, hq⟩ := Finset.prod_eq_zero_iff.1 hP0
  have hq' : τ q • c = 0 := by
    rcases mul_eq_zero.1 hq with h | h
    · exact absurd h (zpow_ne_zero _ (χ (τ q)).ne_zero)
    · exact h
  have := congrArg ((τ q)⁻¹ • ·) hq'
  simpa only [inv_smul_smul, smul_zero] using this

namespace PadicComplex

/-- Vanishing of nontrivial cyclotomic eigenspaces in `ℂ_[p]` over a
finite extension of `ℚ_[p]`: if `σ • c = χ_p(σ) ^ k • c` for every `σ`
fixing `K` and `k ≠ 0`, then `c = 0`. -/
public theorem eq_zero_of_forall_mem_fixingSubgroup_smul_eq_cyclotomicCharacter_zpow_mul
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (k : ℤ) (hk : k ≠ 0) (c : ℂ_[p])
    (hc : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ K.fixingSubgroup →
      σ • c =
        (algebraMap ℚ_[p] ℂ_[p]
            (((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])) ^ k
              * c) :
    c = 0 := by
  classical

  let ρ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* (PadicAlgCl p ≃+* PadicAlgCl p) :=
    { toFun := fun σ => σ.toRingEquiv, map_one' := rfl, map_mul' := fun _ _ => rfl }
  let ι : ℤ_[p]ˣ →* ℂ_[p]ˣ := Units.map (((algebraMap ℚ_[p] ℂ_[p]).comp (PadicInt.Coe.ringHom (p
    := p))) : ℤ_[p] →* ℂ_[p])
  let χ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* ℂ_[p]ˣ := ι.comp ((cyclotomicCharacter
    (PadicAlgCl p) p).comp ρ)
  have hχval : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ((χ σ : ℂ_[p]ˣ) : ℂ_[p]) =
      algebraMap ℚ_[p] ℂ_[p] (((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv : ℤ_[p]ˣ) :
        ℤ_[p]) : ℚ_[p]) :=
    fun σ => rfl
  haveI : K.fixingSubgroup.FiniteIndex :=
    ⟨by rw [← IntermediateField.finrank_eq_fixingSubgroup_index]; exact Module.finrank_pos.ne'⟩
  refine eq_zero_of_forall_mem_smul_eq_of_finiteIndex_aux χ ?_ ?_ K.fixingSubgroup k hk c ?_
  · intro σ τ
    rw [hχval]
    exact PadicComplex.smul_algebraMap p σ _
  · intro m hm x hx
    refine PadicComplex.eq_zero_of_forall_smul_eq_cyclotomicCharacter_zpow_mul p m hm x fun σ => ?_
    rw [hx σ, hχval, cyclotomicCharacter_localGaloisToGlobal]
  · intro h hh
    rw [hχval]
    exact hc h hh

end PadicComplex

end
