/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from the following files
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
`Definitions/Def_CerednikDrinfeld_FormalUpperHalfPlanePoints.lean`,
the theorem files `Theorems/Thm_<Y>.lean` and solution files `P2M/Sol/S_<Y>.lean`
for `<Y>` in the list below, where `CF_` abbreviates `CerednikDrinfeld_FormalOmega_`:
`CF_DeligneDatum_exists_drinfeldDatum_isQuadrupleOf_of_inEdgeChart`
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.AlgebraicGeometry.FormalOmega.DrinfeldDatum
public import MathlibExt.AlgebraicGeometry.FormalOmega.LatticeStd
public import MathlibExt.AlgebraicGeometry.FormalOmega.InvertibleModule
public import MathlibExt.AlgebraicGeometry.FormalOmega.LatticeEdge
import MathlibExt.AlgebraicGeometry.FormalOmega.QuadrupleLocalAux

@[expose] public section

noncomputable section

open scoped TensorProduct MatrixGroups Matrix
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace CerednikDrinfeld.FormalOmega.QuadrupleLocal

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

section Local
variable [IsFractionRing 𝒪 K] {π : 𝒪}
variable {M' M : FullLattice 𝒪 K} (d : DeligneDatum (K := K) π B)

omit [IsFractionRing 𝒪 K] in
private theorem isOpen_setOf_mem_loc₀ (hle : M'.1 ≤ M.1) (v : Fin 2 → K) :
    IsOpen {x : PrimeSpectrum B | v ∈ (loc₀ d hle x).1.1} := by
  by_cases hv' : v ∈ M'.1
  · have : {x : PrimeSpectrum B | v ∈ (loc₀ d hle x).1.1} = Set.univ := by
      ext x; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      by_cases hx : x ∈ S0 d (M := M) hle
      · rw [loc₀_fst_of_mem d hle hx]; exact hv'
      · rw [loc₀_fst_of_not_mem d hle hx]; exact hle hv'
    rw [this]; exact isOpen_univ
  · by_cases hv : v ∈ M.1
    · have : {x : PrimeSpectrum B | v ∈ (loc₀ d hle x).1.1} = (S0 d (M := M) hle)ᶜ := by
        ext x; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
        by_cases hx : x ∈ S0 d (M := M) hle
        · rw [loc₀_fst_of_mem d hle hx]; exact ⟨fun h => absurd h hv', fun h => absurd hx h⟩
        · rw [loc₀_fst_of_not_mem d hle hx]; exact ⟨fun _ => hx, fun _ => hv⟩
      rw [this]; exact (isClosed_S0 d hle).isOpen_compl
    · have : {x : PrimeSpectrum B | v ∈ (loc₀ d hle x).1.1} = ∅ := by
        ext x; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        by_cases hx : x ∈ S0 d (M := M) hle
        · rw [loc₀_fst_of_mem d hle hx]; exact hv'
        · rw [loc₀_fst_of_not_mem d hle hx]; exact hv
      rw [this]; exact isOpen_empty

private theorem isOpen_setOf_mem_loc₁ (hπ : Irreducible π)
    (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (v : Fin 2 → K) : IsOpen {x : PrimeSpectrum B | v ∈ (loc₁ d hπ hπM x).1.1} := by
  by_cases hv : v ∈ M.1
  · have : {x : PrimeSpectrum B | v ∈ (loc₁ d hπ hπM x).1.1} = Set.univ := by
      ext x; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      by_cases hx : x ∈ S1 d hπ hπM
      · rw [loc₁_fst_of_mem d hπ hπM hx]; exact hv
      · rw [loc₁_fst_of_not_mem d hπ hπM hx]; exact le_Mpi hπ hπM hv
    rw [this]; exact isOpen_univ
  · by_cases hv' : v ∈ (Mpi (K := K) hπ M').1
    · have : {x : PrimeSpectrum B | v ∈ (loc₁ d hπ hπM x).1.1} = (S1 d hπ hπM)ᶜ := by
        ext x; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
        by_cases hx : x ∈ S1 d hπ hπM
        · rw [loc₁_fst_of_mem d hπ hπM hx]; exact ⟨fun h => absurd h hv, fun h => absurd hx h⟩
        · rw [loc₁_fst_of_not_mem d hπ hπM hx]; exact ⟨fun _ => hx, fun _ => hv'⟩
      rw [this]; exact (isClosed_S1 d hπ hπM).isOpen_compl
    · have : {x : PrimeSpectrum B | v ∈ (loc₁ d hπ hπM x).1.1} = ∅ := by
        ext x; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        by_cases hx : x ∈ S1 d hπ hπM
        · rw [loc₁_fst_of_mem d hπ hπM hx]; exact hv
        · rw [loc₁_fst_of_not_mem d hπ hπM hx]; exact hv'
      rw [this]; exact isOpen_empty

omit [IsFractionRing 𝒪 K] in
private theorem Pi0_mkQ_tmul (hle : M'.1 ≤ M.1) (b : B) (v : Fin 2 → K) (hv : v ∈ M'.1) :
    Pi0 d hle ((d.line M').mkQ (b ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥M'.1))) = (d.line M).mkQ
        (b ⊗ₜ[𝒪] (⟨v, hle hv⟩ : ↥M.1)) := by
  rw [Pi0, Submodule.mkQ_apply, Submodule.mapQ_apply, inclBaseChange, LinearMap.baseChange_tmul]
  rfl

private theorem Pi1_mkQ_tmul (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (b : B)
    (v : Fin 2 → K)
    (hv : v ∈ M.1) :
    Pi1 d hπ hπM ((d.line M).mkQ (b ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥M.1))) =
      (d.line M').mkQ (b ⊗ₜ[𝒪] (⟨algebraMap 𝒪 K π • v, hπM v hv⟩ : ↥M'.1)) := by
  rw [Pi1, Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.baseChange_tmul]
  rfl

omit [IsFractionRing 𝒪 K] in
private theorem val_loc₀_on (hle : M'.1 ≤ M.1) {y : PrimeSpectrum B} (hy : y ∈ S0 d (M := M) hle)
    (v : Fin 2 → K)
    (hv : v ∈ (loc₀ d hle y).1.1) (hv' : v ∈ M'.1) :
    (loc₀ d hle y).2 ((1 : locRing B y) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(loc₀ d hle y).1.1)) =
      LocalizedModule.mk ((d.line M').mkQ ((1 : B) ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥M'.1))) 1 := by
  have e0 := loc₀_eq_of_mem d hle hy
  revert hv
  generalize loc₀ d hle y = p₀ at e0 ⊢
  subst e0
  intro hv
  exact (stalkQuot_one_tmul y M' (d.line M') ⟨v, hv⟩).trans
      (LocalizedModule.mkLinearMap_apply _ _ _)

omit [IsFractionRing 𝒪 K] in
private theorem val_loc₀_off (hle : M'.1 ≤ M.1) {y : PrimeSpectrum B} (hy : y ∉ S0 d (M := M) hle)
    (v : Fin 2 → K)
    (hv : v ∈ (loc₀ d hle y).1.1) (hvM : v ∈ M.1) :
    (loc₀ d hle y).2 ((1 : locRing B y) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(loc₀ d hle y).1.1)) =
      Pi0inv d hle y hy (LocalizedModule.mk ((d.line M).mkQ ((1 : B) ⊗ₜ[𝒪] (⟨v, hvM⟩ : ↥M.1))) 1) :=
          by
  have e0 := loc₀_eq_of_not_mem d hle hy
  revert hv
  generalize loc₀ d hle y = p₀ at e0 ⊢
  subst e0
  intro hv
  change Pi0inv d hle y hy (stalkQuot y M (d.line M) ((1 : locRing B y) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥M.1))) = _
  rw [stalkQuot_one_tmul, LocalizedModule.mkLinearMap_apply]

private theorem val_loc₁_on (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    {y : PrimeSpectrum B}
    (hy : y ∈ S1 d hπ hπM) (v : Fin 2 → K) (hv : v ∈ (loc₁ d hπ hπM y).1.1) (hvM : v ∈ M.1) :
    (loc₁ d hπ hπM y).2 ((1 : locRing B y) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(loc₁ d hπ hπM y).1.1)) =
      LocalizedModule.mk ((d.line M).mkQ ((1 : B) ⊗ₜ[𝒪] (⟨v, hvM⟩ : ↥M.1))) 1 := by
  have e1 := loc₁_eq_of_mem d hπ hπM hy
  revert hv
  generalize loc₁ d hπ hπM y = p₁ at e1 ⊢
  subst e1
  intro hv
  exact (stalkQuot_one_tmul y M (d.line M) ⟨v, hv⟩).trans (LocalizedModule.mkLinearMap_apply _ _ _)

private theorem val_loc₁_off (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    {y : PrimeSpectrum B}
    (hy : y ∉ S1 d hπ hπM) (v : Fin 2 → K) (hv : v ∈ (loc₁ d hπ hπM y).1.1)
    (hvπ : algebraMap 𝒪 K π • v ∈ M'.1) :
    (loc₁ d hπ hπM y).2 ((1 : locRing B y) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(loc₁ d hπ hπM y).1.1)) =
      Pi1inv d hπ hπM y hy
        (LocalizedModule.mk ((d.line M').mkQ ((1 : B) ⊗ₜ[𝒪] (⟨algebraMap 𝒪 K π • v, hvπ⟩ : ↥M'.1)))
            1) := by
  have e1 := loc₁_eq_of_not_mem d hπ hπM hy
  revert hv
  generalize loc₁ d hπ hπM y = p₁ at e1 ⊢
  subst e1
  intro hv
  change Pi1inv d hπ hπM y hy (stalkQuot y M' (d.line M')
      (sPi hπ M' y ((1 : locRing B y) ⊗ₜ[𝒪] ⟨v, hv⟩))) = _
  rw [sPi, LinearMap.baseChange_tmul, stalkQuot_one_tmul, LocalizedModule.mkLinearMap_apply]
  rfl

omit [Algebra 𝒪 K] [IsFractionRing 𝒪 K] in
private theorem exists_basicOpen_subset_compl {S : Set (PrimeSpectrum B)} (hS : IsClosed S)
    {x : PrimeSpectrum B} (hx : x ∉ S) :
    ∃ g : B, g ∉ x.asIdeal ∧ ∀ y : PrimeSpectrum B, g ∉ y.asIdeal → y ∉ S := by
  obtain ⟨U, ⟨g, rfl⟩, hxg, hgS⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := x) (by exact hx)
        hS.isOpen_compl
  exact ⟨g, hxg, fun y hy => hgS hy⟩

omit [Algebra 𝒪 K] [IsFractionRing 𝒪 K] in
private theorem exists_section_of_bijective {P Q : Type} [AddCommGroup P] [Module B P]
    [AddCommGroup Q]
    [Module B Q]
    (F : P →ₗ[B] Q) (x : PrimeSpectrum B) (hF : Function.Bijective
        (LocalizedModule.map x.asIdeal.primeCompl F))
    (g : B) (hg : g ∉ x.asIdeal) (m : Q) :
    ∃ (f : B) (t : P), f ∉ x.asIdeal ∧ g ∣ f ∧ f • m = F t := by
  obtain ⟨τ, hτ⟩ := hF.2 (LocalizedModule.mk m 1)
  induction τ using LocalizedModule.induction_on with
  | h t s =>
    rw [LocalizedModule.map_mk, LocalizedModule.mk_eq] at hτ
    obtain ⟨u, hu⟩ := hτ
    simp only [Submonoid.smul_def, one_smul] at hu
    refine ⟨g * ((u : B) * (s : B)), g • (u : B) • t,
      fun h => (x.isPrime.mem_or_mem h).elim hg fun h' => (x.isPrime.mem_or_mem h').elim u.2 s.2,
          dvd_mul_right g _, ?_⟩
    rw [map_smul, map_smul, hu, mul_smul, mul_smul]

omit [Algebra 𝒪 K] [IsFractionRing 𝒪 K] in
private theorem one_notMem (x : PrimeSpectrum B) : (1 : B) ∉ x.asIdeal := fun h =>
  x.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)

omit [IsFractionRing 𝒪 K] in
private theorem u₀_continuous_loc (hle : M'.1 ≤ M.1) (x : PrimeSpectrum B) (v : Fin 2 → K)
    (hvx : v ∈ (loc₀ d hle x).1.1) :
    ∃ (f : B) (t : T0 d M'), f ∉ x.asIdeal ∧ ∀ (y : PrimeSpectrum B) (hy : f ∉ y.asIdeal),
      ∃ hv : v ∈ (loc₀ d hle y).1.1,
        (loc₀ d hle y).2 ((1 : locRing B y) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(loc₀ d hle y).1.1)) =
            LocalizedModule.mk t ⟨f, hy⟩ := by
  classical
  have hvM : v ∈ M.1 := by
    by_cases hx : x ∈ S0 d (M := M) hle
    · rw [loc₀_fst_of_mem d hle hx] at hvx; exact hle hvx
    · rw [loc₀_fst_of_not_mem d hle hx] at hvx; exact hvx
  by_cases hv' : v ∈ M'.1
  · refine ⟨1, (d.line M').mkQ ((1 : B) ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥M'.1)), one_notMem x, fun y hy => ?_⟩
    have hvy : v ∈ (loc₀ d hle y).1.1 := by
      by_cases hy0 : y ∈ S0 d (M := M) hle
      · rw [loc₀_fst_of_mem d hle hy0]; exact hv'
      · rw [loc₀_fst_of_not_mem d hle hy0]; exact hle hv'
    refine ⟨hvy, ?_⟩
    rw [show (⟨1, hy⟩ : y.asIdeal.primeCompl) = 1 from Subtype.ext rfl]
    by_cases hy0 : y ∈ S0 d (M := M) hle
    · exact val_loc₀_on d hle hy0 v hvy hv'
    · rw [val_loc₀_off d hle hy0 v hvy (hle hv'), ← Pi0_mkQ_tmul d hle 1 v hv',
        ← LocalizedModule.map_mk,
        Pi0inv_map_Pi0]
  · have hx0 : x ∉ S0 d (M := M) hle := fun hx => hv' (by rwa [loc₀_fst_of_mem d hle hx] at hvx)
    obtain ⟨g, hg, hgS⟩ := exists_basicOpen_subset_compl (isClosed_S0 d hle) hx0
    obtain ⟨f, t, hf, ⟨c, hc⟩, hft⟩ := exists_section_of_bijective (Pi0 d hle) x
      (Module.Invertible.bijective_localizedModule_map_of_not_range_le (Pi0 d hle) x hx0) g hg
      ((d.line M).mkQ ((1 : B) ⊗ₜ[𝒪] (⟨v, hvM⟩ : ↥M.1)))
    refine ⟨f, t, hf, fun y hy => ?_⟩
    have hgy : g ∉ y.asIdeal := fun h => hy (hc ▸ y.asIdeal.mul_mem_right c h)
    have hy0 : y ∉ S0 d (M := M) hle := hgS y hgy
    have hvy : v ∈ (loc₀ d hle y).1.1 := by rw [loc₀_fst_of_not_mem d hle hy0]; exact hvM
    refine ⟨hvy, ?_⟩
    rw [val_loc₀_off d hle hy0 v hvy hvM]
    have : (LocalizedModule.mk ((d.line M).mkQ ((1 : B) ⊗ₜ[𝒪] (⟨v, hvM⟩ : ↥M.1))) 1 : stalk B y
        (T1 d M)) =
        LocalizedModule.map y.asIdeal.primeCompl (Pi0 d hle) (LocalizedModule.mk t ⟨f, hy⟩) := by
      rw [LocalizedModule.map_mk, ← hft, LocalizedModule.mk_eq]
      exact ⟨1, by simp only [Submonoid.smul_def, one_smul]⟩
    rw [this, Pi0inv_map_Pi0]

private theorem u₁_continuous_loc (hπ : Irreducible π)
    (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (x : PrimeSpectrum B) (v : Fin 2 → K) (hvx : v ∈ (loc₁ d hπ hπM x).1.1) :
    ∃ (f : B) (t : T1 d M), f ∉ x.asIdeal ∧ ∀ (y : PrimeSpectrum B) (hy : f ∉ y.asIdeal),
      ∃ hv : v ∈ (loc₁ d hπ hπM y).1.1,
        (loc₁ d hπ hπM y).2 ((1 : locRing B y) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(loc₁ d hπ hπM y).1.1)) =
          LocalizedModule.mk t ⟨f, hy⟩ := by
  classical
  have hvP : v ∈ (Mpi (K := K) hπ M').1 := by
    by_cases hx : x ∈ S1 d hπ hπM
    · rw [loc₁_fst_of_mem d hπ hπM hx] at hvx; exact le_Mpi hπ hπM hvx
    · rw [loc₁_fst_of_not_mem d hπ hπM hx] at hvx; exact hvx
  have hvπ : algebraMap 𝒪 K π • v ∈ M'.1 := smul_mem_of_mem_Mpi hπ M' v hvP
  by_cases hvM : v ∈ M.1
  · refine ⟨1, (d.line M).mkQ ((1 : B) ⊗ₜ[𝒪] (⟨v, hvM⟩ : ↥M.1)), one_notMem x, fun y hy => ?_⟩
    have hvy : v ∈ (loc₁ d hπ hπM y).1.1 := by
      by_cases hy1 : y ∈ S1 d hπ hπM
      · rw [loc₁_fst_of_mem d hπ hπM hy1]; exact hvM
      · rw [loc₁_fst_of_not_mem d hπ hπM hy1]; exact le_Mpi hπ hπM hvM
    refine ⟨hvy, ?_⟩
    rw [show (⟨1, hy⟩ : y.asIdeal.primeCompl) = 1 from Subtype.ext rfl]
    by_cases hy1 : y ∈ S1 d hπ hπM
    · exact val_loc₁_on d hπ hπM hy1 v hvy hvM
    · rw [val_loc₁_off d hπ hπM hy1 v hvy hvπ,
        show (⟨algebraMap 𝒪 K π • v, hvπ⟩ : ↥M'.1) = ⟨algebraMap 𝒪 K π • v, hπM v hvM⟩ from rfl,
        ← Pi1_mkQ_tmul d hπ hπM 1 v hvM, ← LocalizedModule.map_mk, Pi1inv_map_Pi1]
  · have hx1 : x ∉ S1 d hπ hπM := fun hx => hvM (by rwa [loc₁_fst_of_mem d hπ hπM hx] at hvx)
    obtain ⟨g, hg, hgS⟩ := exists_basicOpen_subset_compl (isClosed_S1 d hπ hπM) hx1
    obtain ⟨f, t, hf, ⟨c, hc⟩, hft⟩ := exists_section_of_bijective (Pi1 d hπ hπM) x
      (Module.Invertible.bijective_localizedModule_map_of_not_range_le (Pi1 d hπ hπM) x hx1) g hg
      ((d.line M').mkQ ((1 : B) ⊗ₜ[𝒪] (⟨algebraMap 𝒪 K π • v, hvπ⟩ : ↥M'.1)))
    refine ⟨f, t, hf, fun y hy => ?_⟩
    have hgy : g ∉ y.asIdeal := fun h => hy (hc ▸ y.asIdeal.mul_mem_right c h)
    have hy1 : y ∉ S1 d hπ hπM := hgS y hgy
    have hvy : v ∈ (loc₁ d hπ hπM y).1.1 := by rw [loc₁_fst_of_not_mem d hπ hπM hy1]; exact hvP
    refine ⟨hvy, ?_⟩
    rw [val_loc₁_off d hπ hπM hy1 v hvy hvπ]
    have : (LocalizedModule.mk ((d.line M').mkQ ((1 : B) ⊗ₜ[𝒪]
        (⟨algebraMap 𝒪 K π • v, hvπ⟩ : ↥M'.1))) 1 :
        stalk B y (T0 d M')) =
        LocalizedModule.map y.asIdeal.primeCompl (Pi1 d hπ hπM) (LocalizedModule.mk t ⟨f, hy⟩) := by
      rw [LocalizedModule.map_mk, ← hft, LocalizedModule.mk_eq]
      exact ⟨1, by simp only [Submonoid.smul_def, one_smul]⟩
    rw [this, Pi1inv_map_Pi1]

omit [IsFractionRing 𝒪 K] in
private theorem locallyConstant_loc₀ (hle : M'.1 ≤ M.1) (x : PrimeSpectrum B)
    (hx : x ∈ S0 d (M := M) hle) :
    ∃ U : Set (PrimeSpectrum B), IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, y ∈ S0 d (M := M) hle → (loc₀ d hle y).1.1 = (loc₀ d hle x).1.1 :=
  ⟨Set.univ, isOpen_univ, Set.mem_univ x, fun y _ hy => by
    rw [loc₀_fst_of_mem d hle hy, loc₀_fst_of_mem d hle hx]⟩

private theorem locallyConstant_loc₁ (hπ : Irreducible π)
    (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (x : PrimeSpectrum B) (hx : x ∈ S1 d hπ hπM) :
    ∃ U : Set (PrimeSpectrum B), IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, y ∈ S1 d hπ hπM → (loc₁ d hπ hπM y).1.1 = (loc₁ d hπ hπM x).1.1 :=
  ⟨Set.univ, isOpen_univ, Set.mem_univ x, fun y _ hy => by
    rw [loc₁_fst_of_mem d hπ hπM hy, loc₁_fst_of_mem d hπ hπM hx]⟩

end Local

section DetAux
variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K]
    [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K]

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in
private theorem exists_det_eq_mul (g₁ g₂ : Matrix.GeneralLinearGroup (Fin 2) K)
    (h : latticeMap g₁ (stdLattice 𝒪 K) = latticeMap g₂ (stdLattice 𝒪 K)) :
    ∃ w : 𝒪ˣ, ((Matrix.GeneralLinearGroup.det g₂ : Kˣ) : K) =
        (Matrix.GeneralLinearGroup.det g₁ : Kˣ) * algebraMap 𝒪 K w := by
  have hfix : latticeMap (g₁⁻¹ * g₂) (stdLattice 𝒪 K) = stdLattice 𝒪 K := by
    rw [latticeMap_mul, ← h, latticeMap_inv_latticeMap]
  obtain ⟨N, hN⟩ := (latticeMap_stdLattice_eq_iff_mem_range _).mp hfix
  refine ⟨Matrix.GeneralLinearGroup.det N, ?_⟩
  have hdet : Matrix.GeneralLinearGroup.det g₂ = Matrix.GeneralLinearGroup.det g₁ *
      Matrix.GeneralLinearGroup.det (g₁⁻¹ * g₂) := by
    rw [← map_mul, mul_inv_cancel_left]
  have hdetk : ((Matrix.GeneralLinearGroup.det (g₁⁻¹ * g₂) : Kˣ) : K) = algebraMap 𝒪 K
      (Matrix.GeneralLinearGroup.det N : 𝒪ˣ) := by
    rw [← hN, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
    change ((N : Matrix (Fin 2) (Fin 2) 𝒪).map (algebraMap 𝒪 K)).det = _
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [hdet, Units.val_mul, hdetk]

end DetAux

section SmulTop
variable {B : Type} [CommRing B]

private theorem smul_top_ne_top {L : Type} [AddCommGroup L] [Module B L] [Module.Invertible B L]
    (x : PrimeSpectrum B) :
    (x.asIdeal • ⊤ : Submodule B L) ≠ ⊤ := by
  intro htop
  have hsub : Subsingleton (L ⧸ (x.asIdeal • ⊤ : Submodule B L)) :=
    Submodule.Quotient.subsingleton_iff.mpr htop
  have hsub' : Subsingleton ((B ⧸ x.asIdeal) ⊗[B] L) :=
    (TensorProduct.quotTensorEquivQuotSMul L x.asIdeal).toEquiv.subsingleton
  have : Nontrivial (B ⧸ x.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr x.isPrime.ne_top
  have h01 : (0 : B ⧸ x.asIdeal) = 1 :=
    (FaithfulSMul.eq_of_smul_eq_smul (M := B ⧸ x.asIdeal) (α := (B ⧸ x.asIdeal) ⊗[B] L)
      (fun m => hsub'.elim _ _))
  exact zero_ne_one h01

end SmulTop

section Det
variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
variable {B : Type} [CommRing B] [Algebra 𝒪 B]
variable [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] {π : 𝒪}
variable {M' M : FullLattice 𝒪 K} (d : DeligneDatum (K := K) π B)

omit [IsFractionRing 𝒪 K] in
omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in
private theorem hasDetIndex₀_loc (hle : M'.1 ≤ M.1)
    (h0 : HasDetIndex π M'.1 0) (x : PrimeSpectrum B)
    (hx : LinearMap.range (Pi0 d hle) ≤ x.asIdeal • (⊤ : Submodule B (T1 d M))) :
    HasDetIndex π (loc₀ d hle x).1.1 0 := by
  rw [loc₀_fst_of_mem d hle hx]
  exact h0

private theorem hasDetIndex₁_loc (hπ : Irreducible π) (hle : M'.1 ≤ M.1)
    (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (h0 : HasDetIndex π M'.1 0)
    (hMM : M'.1 ≠ M.1) (x : PrimeSpectrum B)
    (hx : LinearMap.range (Pi1 d hπ hπM) ≤ x.asIdeal • (⊤ : Submodule B (T0 d M'))) :
    HasDetIndex π (loc₁ d hπ hπM x).1.1 (-1) := by
  rw [loc₁_fst_of_mem d hπ hπM hx]
  have hπle : latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 ≤ M'.1 := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := mem_latticeMap_scalarGL.mp hv
    rw [unitOfNeZero_coe]; exact hπM w hw
  have hne : latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 ≠ M'.1 := by
    intro hEq
    have hs : Function.Surjective (smulInto π hπM) := by
      intro w
      have hw : (w : Fin 2 → K) ∈ latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 :=
          hEq.symm ▸ w.2
      obtain ⟨v, hv, hvw⟩ := mem_latticeMap_scalarGL.mp hw
      refine ⟨⟨v, hv⟩, Subtype.ext ?_⟩
      rw [coe_smulInto_apply, ← hvw, unitOfNeZero_coe]
    have hs' : Function.Surjective ((smulInto π hπM).baseChange B) := by
      rw [LinearMap.baseChange_eq_lTensor]; exact LinearMap.lTensor_surjective B hs
    have hsurj : Function.Surjective (Pi1 d hπ hπM) := by
      intro t
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ t
      obtain ⟨y, rfl⟩ := hs' z
      exact ⟨Submodule.Quotient.mk y, rfl⟩
    have htop : (x.asIdeal • ⊤ : Submodule B (T0 d M')) = ⊤ :=
      eq_top_iff.mpr (le_trans (LinearMap.range_eq_top.mpr hsurj).ge hx)
    exact smul_top_ne_top x htop
  have h1lt : latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 < M'.1 := lt_of_le_of_ne
      hπle hne
  have h2lt : M'.1 < M.1 := lt_of_le_of_ne hle hMM
  obtain ⟨h, hM, hM'⟩ :=
      CerednikDrinfeld.FormalOmega.exists_act_stdFullLattice_eq_and_act_act_eq_of_lt_of_lt π hπ
    (diagFstGL (unitOfNeZero (K := K) hπ.ne_zero)) (by rw [diagFstGL_coe, unitOfNeZero_coe]) M' M
        h1lt h2lt
  have hMv : latticeMap h (stdLattice 𝒪 K) = M.1 := congrArg Subtype.val hM
  have hM'v : latticeMap (h * diagFstGL (unitOfNeZero (K := K) hπ.ne_zero)) (stdLattice 𝒪 K) = M'.1
      := by
    rw [latticeMap_mul]; exact congrArg Subtype.val hM'
  obtain ⟨g₀, hg₀, u₀, hu₀⟩ := h0
  obtain ⟨w, hw⟩ := exists_det_eq_mul g₀ (h * diagFstGL (unitOfNeZero (K := K) hπ.ne_zero))
      (hg₀.trans hM'v.symm)
  have hdg : ((Matrix.GeneralLinearGroup.det (diagFstGL (unitOfNeZero (K := K) hπ.ne_zero)) : Kˣ) :
      K) =
      algebraMap 𝒪 K π := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, diagFstGL_coe, Matrix.det_diagonal,
        unitOfNeZero_coe]
    simp [Fin.prod_univ_two]
  have hπK : algebraMap 𝒪 K π ≠ 0 := fun h0' => hπ.ne_zero
      (IsFractionRing.injective 𝒪 K (by rw [h0', map_zero]))
  refine ⟨h, hMv, u₀ * w, ?_⟩
  rw [map_mul, Units.val_mul, hdg, hu₀, zpow_zero, mul_one] at hw
  rw [zpow_neg_one, Units.val_mul, map_mul, eq_mul_inv_iff_mul_eq₀ hπK, hw]

end Det

section Local2
variable [IsFractionRing 𝒪 K] {π : 𝒪}
variable {M' M : FullLattice 𝒪 K} (d : DeligneDatum (K := K) π B)

private theorem not_mem_smul_top_of_bijective {P Q : Type} [AddCommGroup P] [Module B P]
    [AddCommGroup Q]
    [Module B Q]
    [Module.Invertible B P] [Module.Invertible B Q] (f : P →ₗ[B] Q) (x : PrimeSpectrum B)
    (hf : Function.Bijective (LocalizedModule.map x.asIdeal.primeCompl f)) (t : P)
    (ht : t ∉ x.asIdeal • (⊤ : Submodule B P)) : f t ∉ x.asIdeal • (⊤ : Submodule B Q) := by
  intro hft
  apply ht
  apply mem_smul_top_of_forall_form
  intro φ
  let e := LinearEquiv.ofBijective (LocalizedModule.map x.asIdeal.primeCompl f) hf
  have h1 : (LocalizedModule.mk (f t) 1 : LocalizedModule x.asIdeal.primeCompl Q) ∈
      x.asIdeal • (⊤ : Submodule B (LocalizedModule x.asIdeal.primeCompl Q)) := by
    have := Submodule.mem_map_of_mem (f := LocalizedModule.mkLinearMap x.asIdeal.primeCompl Q) hft
    rw [Submodule.map_smul'', Submodule.map_top, LocalizedModule.mkLinearMap_apply] at this
    exact Submodule.smul_mono le_rfl le_top this
  have h2 : (LocalizedModule.mk t 1 : LocalizedModule x.asIdeal.primeCompl P) ∈
      x.asIdeal • (⊤ : Submodule B (LocalizedModule x.asIdeal.primeCompl P)) := by
    have he : e.symm (LocalizedModule.mk (f t) 1) = LocalizedModule.mk t 1 := by
      rw [LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply, LocalizedModule.map_mk]
    have := Submodule.mem_map_of_mem (f := (e.symm.toLinearMap.restrictScalars B)) h1
    rw [Submodule.map_smul'', Submodule.map_top] at this
    have := Submodule.smul_mono (le_refl x.asIdeal) (le_top (a := LinearMap.range _)) this
    rwa [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, he] at this
  have h3 : (LocalizedModule.mk (φ t) 1 : LocalizedModule x.asIdeal.primeCompl B) ∈
      x.asIdeal • (⊤ : Submodule B (LocalizedModule x.asIdeal.primeCompl B)) := by
    have := Submodule.mem_map_of_mem (f := (LocalizedModule.map x.asIdeal.primeCompl
        φ).restrictScalars B) h2
    rw [Submodule.map_smul'', Submodule.map_top] at this
    have := Submodule.smul_mono (le_refl x.asIdeal) (le_top (a := LinearMap.range _)) this
    rwa [LinearMap.restrictScalars_apply, LocalizedModule.map_mk] at this
  exact mem_of_mk_mem_smul_top x (φ t) h3

omit [IsFractionRing 𝒪 K] in
private theorem not_mem_sup_iff_mkQ_not_mem (x : PrimeSpectrum B) (L : FullLattice 𝒪 K)
    (N : Submodule B (latticeBaseChange 𝒪 K B L))
    (y : latticeBaseChange 𝒪 K B L) :
    y ∉ N ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L)) ↔
      N.mkQ y ∉ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L ⧸ N)) := by
  rw [not_iff_not]
  constructor
  · intro hy
    have : N.mkQ y ∈ ((x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L)) ⊔ N).map N.mkQ :=
      Submodule.mem_map_of_mem (by rwa [sup_comm] at hy)
    rwa [Submodule.map_sup, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ,
        Submodule.mkQ_map_self,
      sup_bot_eq] at this
  · intro hy
    have hmap : (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L ⧸ N)) =
        (x.asIdeal • (⊤ : Submodule B (latticeBaseChange 𝒪 K B L))).map N.mkQ := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
    have : y ∈ ((x.asIdeal • (⊤ : Submodule B (latticeBaseChange 𝒪 K B L))).map N.mkQ).comap N.mkQ
        := by
      rw [← hmap]; exact hy
    rwa [Submodule.comap_map_mkQ] at this

omit [IsFractionRing 𝒪 K] in
private theorem not_mem_sup_incl_of_not_mem_S0 (hle : M'.1 ≤ M.1) (x : PrimeSpectrum B)
    (hx : x ∉ S0 d (M := M) hle)
    (y : latticeBaseChange 𝒪 K B M')
    (hy : y ∉ d.line M' ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M'))) :
    inclBaseChange B hle y ∉ d.line M ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)) :=
        by
  rw [not_mem_sup_iff_mkQ_not_mem x] at hy ⊢
  have h := not_mem_smul_top_of_bijective (Pi0 d hle) x
    (Module.Invertible.bijective_localizedModule_map_of_not_range_le (Pi0 d hle) x hx) _ hy
  rwa [Pi0, Submodule.mkQ_apply, Submodule.mapQ_apply] at h

private theorem not_mem_sup_smul_of_not_mem_S1 (hπ : Irreducible π)
    (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (x : PrimeSpectrum B) (hx : x ∉ S1 d hπ hπM) (y : latticeBaseChange 𝒪 K B M)
    (hy : y ∉ d.line M ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))) :
    (smulInto π hπM).baseChange B y ∉ d.line M' ⊔ (x.asIdeal • ⊤ : Submodule B
        (latticeBaseChange 𝒪 K B M')) := by
  rw [not_mem_sup_iff_mkQ_not_mem x] at hy ⊢
  have h := not_mem_smul_top_of_bijective (Pi1 d hπ hπM) x
    (Module.Invertible.bijective_localizedModule_map_of_not_range_le (Pi1 d hπ hπM) x hx) _ hy
  rwa [Pi1, Submodule.mkQ_apply, Submodule.mapQ_apply] at h

private theorem not_exists_eq_smul_of_not_mem (hπ : Irreducible π) {L : Submodule 𝒪 (Fin 2 → K)}
    {v : Fin 2 → K}
    (hv : v ∉ L) : ¬ ∃ w : ↥L, algebraMap 𝒪 K π • v = algebraMap 𝒪 K π • (w : Fin 2 → K) := by
  rintro ⟨w, h⟩
  apply hv
  rw [smul_right_injective (Fin 2 → K) (hπK_of_irreducible (K := K) hπ) h]
  exact w.2

private theorem exists_eq_smul_Mpi (hπ : Irreducible π) (M' : FullLattice 𝒪 K) (v' : ↥M'.1) :
    ∃ w : ↥(Mpi (K := K) hπ M').1, (v' : Fin 2 → K) = algebraMap 𝒪 K π • (w : Fin 2 → K) := by
  refine ⟨⟨((piUnit (K := K) hπ)⁻¹ : Kˣ) • (v' : Fin 2 → K), ?_⟩, ?_⟩
  · exact mem_latticeMap_scalarGL.mpr ⟨v', v'.2, rfl⟩
  · change (v' : Fin 2 → K) = algebraMap 𝒪 K π • ((((piUnit (K := K) hπ)⁻¹ : Kˣ) : K) •
      (v' : Fin 2 → K))
    rw [smul_smul, Units.val_inv_eq_inv_val, show algebraMap 𝒪 K π = ((piUnit (K := K) hπ : Kˣ) : K)
        from rfl,
      mul_inv_cancel₀ (piUnit (K := K) hπ).ne_zero, one_smul]

private theorem smulEquiv_baseChange_coe (hπ : Irreducible π) (M' : FullLattice 𝒪 K) :
    (((smulEquiv (K := K) hπ M').baseChange 𝒪 B _ _ :
      latticeBaseChange 𝒪 K B (Mpi (K := K) hπ M') ≃ₗ[B] latticeBaseChange 𝒪 K B M') :
      latticeBaseChange 𝒪 K B (Mpi (K := K) hπ M') →ₗ[B] latticeBaseChange 𝒪 K B M') =
      (smulInto π (smul_mem_of_mem_Mpi (K := K) hπ M')).baseChange B := by
  refine TensorProduct.AlgebraTensorModule.ext fun b v => ?_
  rw [LinearEquiv.coe_coe, LinearEquiv.baseChange_tmul, LinearMap.baseChange_tmul]
  rfl

private theorem one_tmul_mem_sup_Mpi_iff (hπ : Irreducible π) (M' : FullLattice 𝒪 K) (I : Ideal B)
    (v : ↥(Mpi (K := K) hπ M').1) :
    (1 : B) ⊗ₜ[𝒪] v ∈ d.line (Mpi (K := K) hπ M') ⊔ (I • ⊤ : Submodule B
        (latticeBaseChange 𝒪 K B (Mpi (K := K) hπ M'))) ↔
      (1 : B) ⊗ₜ[𝒪] (smulInto π (smul_mem_of_mem_Mpi (K := K) hπ M') v) ∈
        d.line M' ⊔ (I • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M')) := by
  set e : latticeBaseChange 𝒪 K B (Mpi (K := K) hπ M') ≃ₗ[B] latticeBaseChange 𝒪 K B M' :=
    (smulEquiv (K := K) hπ M').baseChange 𝒪 B _ _ with he_def
  have he : (e : latticeBaseChange 𝒪 K B (Mpi (K := K) hπ M') →ₗ[B] latticeBaseChange 𝒪 K B M') =
      (smulInto π (smul_mem_of_mem_Mpi (K := K) hπ M')).baseChange B := by
    rw [he_def]; exact smulEquiv_baseChange_coe hπ M'
  have hmap : (d.line (Mpi (K := K) hπ M') ⊔ (I • ⊤ : Submodule B
      (latticeBaseChange 𝒪 K B (Mpi (K := K) hπ M')))).map
      (e : latticeBaseChange 𝒪 K B (Mpi (K := K) hπ M') →ₗ[B] latticeBaseChange 𝒪 K B M') =
      d.line M' ⊔ (I • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M')) := by
    rw [Submodule.map_sup, Submodule.map_smul'', Submodule.map_top, LinearEquiv.range, he,
      map_smulInto_line_Mpi d hπ M']
  have hev : e ((1 : B) ⊗ₜ[𝒪] v) = (1 : B) ⊗ₜ[𝒪] (smulInto π (smul_mem_of_mem_Mpi (K := K) hπ M') v)
      := by
    rw [← LinearEquiv.coe_coe, he, LinearMap.baseChange_tmul]
  rw [← hmap, ← hev, Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

private theorem not_mem_sup_Mpi_of (hπ : Irreducible π) (M' : FullLattice 𝒪 K) (I : Ideal B)
    (v : ↥(Mpi (K := K) hπ M').1)
    (h : (1 : B) ⊗ₜ[𝒪] (smulInto π (smul_mem_of_mem_Mpi (K := K) hπ M') v) ∉
      d.line M' ⊔ (I • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M'))) :
    (1 : B) ⊗ₜ[𝒪] v ∉
      d.line (Mpi (K := K) hπ M') ⊔ (I • ⊤ : Submodule B
          (latticeBaseChange 𝒪 K B (Mpi (K := K) hπ M'))) :=
  fun hv => h ((one_tmul_mem_sup_Mpi_iff d hπ M' I v).mp hv)

private theorem inEdgeChart_Mpi_of_inEdgeChart_self (hπ : Irreducible π) (M' : FullLattice 𝒪 K)
    (hπM : ∀ v ∈ M'.1, algebraMap 𝒪 K π • v ∈ M'.1) (hd : d.InEdgeChart π M' M') :
    d.InEdgeChart π M' (Mpi (K := K) hπ M') := by
  intro 𝔭 h𝔭
  have hdx := hd 𝔭 h𝔭
  refine ⟨le_Mpi hπ hπM, fun v => smul_mem_of_mem_Mpi (K := K) hπ M' v v.2, ?_, ?_⟩
  · intro v hv
    refine not_mem_sup_Mpi_of d hπ M' 𝔭 v (hdx.2.2.2 _ ?_)
    rw [coe_smulInto_apply]
    exact not_exists_eq_smul_of_not_mem hπ hv
  · intro v' hv'
    exact (hv' (exists_eq_smul_Mpi hπ M' v')).elim

private theorem fst_ne_Mpi_fst (hπ : Irreducible π) (M' : FullLattice 𝒪 K)
    (h0 : HasDetIndex π M'.1 0) :
    M'.1 ≠ (Mpi (K := K) hπ M').1 := by
  intro heq
  obtain ⟨g₀, hg₀, u, hu⟩ := h0
  have h' : latticeMap g₀ (stdLattice 𝒪 K) = latticeMap (scalarGL (piUnit (K := K) hπ)⁻¹ * g₀)
      (stdLattice 𝒪 K) := by
    rw [latticeMap_mul, hg₀]; exact heq
  obtain ⟨w, hw⟩ := exists_det_eq_mul g₀ _ h'
  have hdet : ((Matrix.GeneralLinearGroup.det (scalarGL (piUnit (K := K) hπ)⁻¹) : Kˣ) : K) =
      (((piUnit (K := K) hπ)⁻¹ : Kˣ) : K) ^ 2 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, scalarGL_coe, Matrix.det_smul, Matrix.det_one,
        mul_one,
      Fintype.card_fin]
  rw [map_mul, Units.val_mul, hdet, mul_comm] at hw
  have h1 : (((piUnit (K := K) hπ)⁻¹ : Kˣ) : K) ^ 2 = algebraMap 𝒪 K w :=
    mul_left_cancel₀ (Matrix.GeneralLinearGroup.det g₀).ne_zero hw
  refine hπ.not_isUnit (isUnit_of_algebraMap_mul_eq_one (K := K)
      (w := algebraMap 𝒪 K π * algebraMap 𝒪 K w)
    ⟨π * w, by rw [map_mul]⟩ ?_)
  rw [← h1, ← mul_assoc, ← pow_two, Units.val_inv_eq_inv_val, inv_pow,
    show algebraMap 𝒪 K π = ((piUnit (K := K) hπ : Kˣ) : K) from rfl,
    mul_inv_cancel₀ (pow_ne_zero 2 (piUnit (K := K) hπ).ne_zero)]

private theorem edgeNondegAt_loc (hπ : Irreducible π) (hle : M'.1 ≤ M.1)
    (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (hd : d.InEdgeChart π M' M) (x : PrimeSpectrum B) :
    d.EdgeNondegAt π x.asIdeal (loc₀ d hle x).1 (loc₁ d hπ hπM x).1 := by
  classical
  have hdx := hd x.asIdeal x.isPrime
  by_cases h0 : x ∈ S0 d (M := M) hle <;> by_cases h1 : x ∈ S1 d hπ hπM
  · rw [loc₀_eq_of_mem d hle h0, loc₁_eq_of_mem d hπ hπM h1]; exact hdx
  · rw [loc₀_eq_of_mem d hle h0, loc₁_eq_of_not_mem d hπ hπM h1]
    refine ⟨hle.trans (le_Mpi hπ hπM), fun v => smul_mem_of_mem_Mpi hπ M' v v.2, ?_, ?_⟩
    · intro v hv
      apply not_mem_sup_Mpi_of d hπ M' x.asIdeal v
      by_cases hvM : (v : Fin 2 → K) ∈ M.1
      · have h := not_mem_sup_smul_of_not_mem_S1 d hπ hπM x h1 _ (hdx.2.2.1 ⟨v, hvM⟩ hv)
        have hw : smulInto π hπM ⟨(v : Fin 2 → K), hvM⟩ = smulInto π
            (smul_mem_of_mem_Mpi (K := K) hπ M') v :=
          Subtype.ext rfl
        rwa [LinearMap.baseChange_tmul, hw] at h
      · exact hdx.2.2.2 _ (by rw [coe_smulInto_apply]; exact not_exists_eq_smul_of_not_mem hπ hvM)
    · intro v' hv'
      exfalso; apply hv'
      refine ⟨⟨((piUnit (K := K) hπ)⁻¹ : Kˣ) • (v' : Fin 2 → K), ?_⟩, ?_⟩
      · exact mem_latticeMap_scalarGL.mpr ⟨v', v'.2, rfl⟩
      · change (v' : Fin 2 → K) = algebraMap 𝒪 K π • ((((piUnit (K := K) hπ)⁻¹ : Kˣ) : K) •
          (v' : Fin 2 → K))
        rw [smul_smul, Units.val_inv_eq_inv_val, show algebraMap 𝒪 K π =
            ((piUnit (K := K) hπ : Kˣ) : K) from rfl,
          mul_inv_cancel₀ (piUnit (K := K) hπ).ne_zero, one_smul]
  · rw [loc₀_eq_of_not_mem d hle h0, loc₁_eq_of_mem d hπ hπM h1]
    refine ⟨le_rfl, fun v => hle (hπM v v.2), fun v hv => (hv v.2).elim, ?_⟩
    intro v' hv'
    by_cases hvM' : (v' : Fin 2 → K) ∈ M'.1
    · have h4 := hdx.2.2.2 ⟨v', hvM'⟩ hv'
      have h := not_mem_sup_incl_of_not_mem_S0 d hle x h0 _ h4
      rwa [inclBaseChange, LinearMap.baseChange_tmul] at h
    · exact hdx.2.2.1 v' hvM'
  · exact ((mem_S0_or_mem_S1 d hπ hle hπM hB x).elim h0 h1).elim

private theorem loc_smul_mem_smul_top {Q : Type} [AddCommGroup Q] [Module B Q] (x : PrimeSpectrum B)
    (r : locRing B x)
    (m : stalk B x Q) (hm : m ∈ x.asIdeal • (⊤ : Submodule B (stalk B x Q))) :
    r • m ∈ x.asIdeal • (⊤ : Submodule B (stalk B x Q)) := by
  refine Submodule.smul_induction_on hm ?_ ?_
  · intro p hp n _
    rw [← algebraMap_smul (locRing B x) p n, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]
    exact Submodule.smul_mem_smul hp Submodule.mem_top
  · intro a b ha hb
    rw [smul_add]
    exact Submodule.add_mem _ ha hb

private theorem range_map_le_smul_top {P Q : Type} [AddCommGroup P] [Module B P] [AddCommGroup Q]
    [Module B Q]
    (f : P →ₗ[B] Q) (x : PrimeSpectrum B) (hf : LinearMap.range f ≤ x.asIdeal • (⊤ : Submodule B Q))
        :
    (LinearMap.range (LocalizedModule.map x.asIdeal.primeCompl f)).restrictScalars B ≤
      x.asIdeal • (⊤ : Submodule B (stalk B x Q)) := by
  rintro m ⟨t, rfl⟩
  induction t using LocalizedModule.induction_on with
  | h p s =>
    rw [LocalizedModule.map_mk]
    have h1 : (LocalizedModule.mk (f p) 1 : stalk B x Q) ∈ x.asIdeal •
        (⊤ : Submodule B (stalk B x Q)) := by
      have := Submodule.mem_map_of_mem (f := LocalizedModule.mkLinearMap x.asIdeal.primeCompl Q)
          (hf ⟨p, rfl⟩)
      rw [Submodule.map_smul'', Submodule.map_top, LocalizedModule.mkLinearMap_apply] at this
      exact Submodule.smul_mono le_rfl le_top this
    have h2 : (LocalizedModule.mk (f p) s : stalk B x Q) =
        (Localization.mk 1 s : locRing B x) • (LocalizedModule.mk (f p) 1 : stalk B x Q) := by
      rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]
    rw [h2]
    exact loc_smul_mem_smul_top x _ _ h1

private theorem mem_smul_top_of_mk_mem {Q : Type} [AddCommGroup Q] [Module B Q]
    [Module.Invertible B Q]
    (x : PrimeSpectrum B)
    (q : Q) (hq : (LocalizedModule.mk q 1 : stalk B x Q) ∈ x.asIdeal •
        (⊤ : Submodule B (stalk B x Q))) :
    q ∈ x.asIdeal • (⊤ : Submodule B Q) := by
  apply mem_smul_top_of_forall_form
  intro φ
  have := Submodule.mem_map_of_mem (f := (LocalizedModule.map x.asIdeal.primeCompl
      φ).restrictScalars B) hq
  rw [Submodule.map_smul'', Submodule.map_top] at this
  have := Submodule.smul_mono (le_refl x.asIdeal) (le_top (a := LinearMap.range _)) this
  rw [LinearMap.restrictScalars_apply, LocalizedModule.map_mk] at this
  exact mem_of_mk_mem_smul_top x (φ q) this

omit [IsFractionRing 𝒪 K] in
private theorem one_tmul_mem_sup_of_stalkQuot_mem (x : PrimeSpectrum B) (L : FullLattice 𝒪 K)
    (v : ↥L.1)
    (h : stalkQuot x L (d.line L) ((1 : locRing B x) ⊗ₜ[𝒪] v) ∈ x.asIdeal •
        (⊤ : Submodule B (stalk B x (T0 d L)))) :
    (1 : B) ⊗ₜ[𝒪] v ∈ d.line L ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L)) := by
  by_contra hc
  rw [not_mem_sup_iff_mkQ_not_mem x] at hc
  apply hc
  rw [stalkQuot_one_tmul, LocalizedModule.mkLinearMap_apply] at h
  exact mem_smul_top_of_mk_mem x _ h

private theorem injective₀_loc (hπ : Irreducible π) (hle : M'.1 ≤ M.1)
    (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (hd : d.InEdgeChart π M' M) (x : PrimeSpectrum B)
    (v : ↥(loc₀ d hle x).1.1)
    (hv : (loc₀ d hle x).2 ((1 : locRing B x) ⊗ₜ[𝒪] v) ∈
      (LinearMap.range (LocalizedModule.map x.asIdeal.primeCompl (Pi1 d hπ hπM))).restrictScalars B
          ⊔
        x.asIdeal • (⊤ : Submodule B (stalk B x (T0 d M')))) :
    ∃ w ∈ (loc₁ d hπ hπM x).1.1, (v : Fin 2 → K) = algebraMap 𝒪 K π • w := by
  classical
  have hdx := hd x.asIdeal x.isPrime
  by_cases h0 : x ∈ S0 d (M := M) hle <;> by_cases h1 : x ∈ S1 d hπ hπM
  · revert v hv
    rw [loc₀_eq_of_mem d hle h0, loc₁_eq_of_mem d hπ hπM h1]
    intro v hv
    have hv' := (sup_le (range_map_le_smul_top (Pi1 d hπ hπM) x h1) le_rfl) hv
    have hmem := one_tmul_mem_sup_of_stalkQuot_mem d x M' v hv'
    by_contra hne
    exact hdx.2.2.2 v (fun ⟨w, hw⟩ => hne ⟨w, w.2, hw⟩) hmem
  · revert v hv
    rw [loc₀_eq_of_mem d hle h0, loc₁_eq_of_not_mem d hπ hπM h1]
    intro v _
    refine ⟨(((piUnit (K := K) hπ)⁻¹ : Kˣ) : K) • (v : Fin 2 → K),
        mem_latticeMap_scalarGL.mpr ⟨v, v.2, rfl⟩, ?_⟩
    rw [smul_smul, Units.val_inv_eq_inv_val, show algebraMap 𝒪 K π = ((piUnit (K := K) hπ : Kˣ) : K)
        from rfl,
      mul_inv_cancel₀ (piUnit (K := K) hπ).ne_zero, one_smul]
  · revert v hv
    rw [loc₀_eq_of_not_mem d hle h0, loc₁_eq_of_mem d hπ hπM h1]
    intro v hv
    have hv' := (sup_le (range_map_le_smul_top (Pi1 d hπ hπM) x h1) le_rfl) hv
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hv'
    have hv'' : stalkQuot x M (d.line M) ((1 : locRing B x) ⊗ₜ[𝒪] v) ∈
        x.asIdeal • (⊤ : Submodule B (stalk B x (T1 d M))) := by
      have := Submodule.mem_map_of_mem
        (f := (LocalizedModule.map x.asIdeal.primeCompl (Pi0 d hle)).restrictScalars B) hv'
      rw [Submodule.map_smul'', Submodule.map_top] at this
      have := Submodule.smul_mono (le_refl x.asIdeal) (le_top (a := LinearMap.range _)) this
      rwa [LinearMap.restrictScalars_apply, map_Pi0_Pi0inv] at this
    have hmem := one_tmul_mem_sup_of_stalkQuot_mem d x M v hv''
    have hvM' : (v : Fin 2 → K) ∈ M'.1 := by
      by_contra h
      exact hdx.2.2.1 v h hmem
    by_contra hne
    have h4 := hdx.2.2.2 ⟨v, hvM'⟩ (fun ⟨w, hw⟩ => hne ⟨w, w.2, hw⟩)
    have h5 := not_mem_sup_incl_of_not_mem_S0 d hle x h0 _ h4
    rw [inclBaseChange, LinearMap.baseChange_tmul] at h5
    exact h5 hmem
  · exact ((mem_S0_or_mem_S1 d hπ hle hπM hB x).elim h0 h1).elim

private theorem injective₁_loc (hπ : Irreducible π) (hle : M'.1 ≤ M.1)
    (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (hd : d.InEdgeChart π M' M) (x : PrimeSpectrum B)
    (v : ↥(loc₁ d hπ hπM x).1.1)
    (hv : (loc₁ d hπ hπM x).2 ((1 : locRing B x) ⊗ₜ[𝒪] v) ∈
      (LinearMap.range (LocalizedModule.map x.asIdeal.primeCompl (Pi0 d hle))).restrictScalars B ⊔
        x.asIdeal • (⊤ : Submodule B (stalk B x (T1 d M)))) :
    (v : Fin 2 → K) ∈ (loc₀ d hle x).1.1 := by
  classical
  have hdx := hd x.asIdeal x.isPrime
  by_cases h0 : x ∈ S0 d (M := M) hle <;> by_cases h1 : x ∈ S1 d hπ hπM
  · revert v hv
    rw [loc₀_eq_of_mem d hle h0, loc₁_eq_of_mem d hπ hπM h1]
    intro v hv
    have hv' := (sup_le (range_map_le_smul_top (Pi0 d hle) x h0) le_rfl) hv
    have hmem := one_tmul_mem_sup_of_stalkQuot_mem d x M v hv'
    by_contra h
    exact hdx.2.2.1 v h hmem
  · revert v hv
    rw [loc₀_eq_of_mem d hle h0, loc₁_eq_of_not_mem d hπ hπM h1]
    intro v hv
    have hv' := (sup_le (range_map_le_smul_top (Pi0 d hle) x h0) le_rfl) hv
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hv'
    have hv'' : stalkQuot x M' (d.line M') (sPi hπ M' x ((1 : locRing B x) ⊗ₜ[𝒪] v)) ∈
        x.asIdeal • (⊤ : Submodule B (stalk B x (T0 d M'))) := by
      have := Submodule.mem_map_of_mem
        (f := (LocalizedModule.map x.asIdeal.primeCompl (Pi1 d hπ hπM)).restrictScalars B) hv'
      rw [Submodule.map_smul'', Submodule.map_top] at this
      have := Submodule.smul_mono (le_refl x.asIdeal) (le_top (a := LinearMap.range _)) this
      rwa [LinearMap.restrictScalars_apply, map_Pi1_Pi1inv] at this
    rw [sPi, LinearMap.baseChange_tmul] at hv''
    have hmem := one_tmul_mem_sup_of_stalkQuot_mem d x M' _ hv''
    have hvM : (v : Fin 2 → K) ∈ M.1 := by
      by_contra hvM
      refine hdx.2.2.2 (smulInto π (smul_mem_of_mem_Mpi (K := K) hπ M') v) ?_ hmem
      rintro ⟨w, hw⟩
      rw [coe_smulInto_apply] at hw
      have hvw := smul_right_injective _ (hπK_of_irreducible (K := K) hπ) hw
      exact hvM (hvw ▸ w.2)
    by_contra hvM'
    have h3 := hdx.2.2.1 ⟨v, hvM⟩ hvM'
    have h5 := not_mem_sup_smul_of_not_mem_S1 d hπ hπM x h1 _ h3
    rw [LinearMap.baseChange_tmul] at h5
    have he : smulInto π hπM ⟨(v : Fin 2 → K), hvM⟩ = smulInto π
        (smul_mem_of_mem_Mpi (K := K) hπ M') v :=
      Subtype.ext rfl
    rw [he] at h5
    exact h5 hmem
  · revert v hv
    rw [loc₀_eq_of_not_mem d hle h0, loc₁_eq_of_mem d hπ hπM h1]
    intro v _
    exact v.2
  · exact ((mem_S0_or_mem_S1 d hπ hle hπM hB x).elim h0 h1).elim

end Local2

private theorem solution_of_ne
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    {M' M : FullLattice 𝒪 K} (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (h0 : HasDetIndex π M'.1 0)
    (d : DeligneDatum (K := K) π B) (hd : d.InEdgeChart π M' M) (hMM : M'.1 ≠ M.1) :
    ∃ Q : DrinfeldDatum (K := K) π B, Q.IsQuadrupleOf d := by
  classical
  refine ⟨{
    N₀ := fun x => (loc₀ d hle x).1.1
    N₁ := fun x => (loc₁ d hπ hπM x).1.1
    full₀ := fun x => (loc₀ d hle x).1.2
    full₁ := fun x => (loc₁ d hπ hπM x).1.2
    le := fun x => loc_le d hπ hle hπM x
    smul_le := fun x => loc_smul_le d hπ hle hπM x
    isOpen_setOf_mem₀ := ?open0
    isOpen_setOf_mem₁ := ?open1
    T₀ := T0 d M'
    T₁ := T1 d M
    invertible₀ := inferInstance
    invertible₁ := inferInstance
    Pi₀ := Pi0 d hle
    Pi₁ := Pi1 d hπ hπM
    Pi₁_Pi₀ := Pi1_Pi0 d hπ hle hπM
    Pi₀_Pi₁ := Pi0_Pi1 d hπ hle hπM
    u₀ := fun x => (loc₀ d hle x).2
    u₁ := fun x => (loc₁ d hπ hπM x).2
    u₁_incl := fun x w => u₁_incl_loc d hπ hle hπM x (loc_le d hπ hle hπM x) w
    u₀_smul := fun x w => u₀_smul_loc d hπ hle hπM x (loc_smul_le d hπ hle hπM x) w
    u₀_surjective := fun x => loc₀_surjective d hle x
    u₁_surjective := fun x => loc₁_surjective d hπ hπM x
    u₀_continuous := ?cont0
    u₁_continuous := ?cont1
    locallyConstant₀ := ?lc0
    locallyConstant₁ := ?lc1
    injective₀ := ?inj0
    injective₁ := ?inj1
    hasDetIndex₀ := ?det0
    hasDetIndex₁ := ?det1 }, ?quad⟩
  case quad =>
    intro x
    exact ⟨edgeNondegAt_loc d hπ hle hπM hB hd x, ker_loc₀ d hle x, ker_loc₁ d hπ hπM x⟩
  case open0 => exact fun v => isOpen_setOf_mem_loc₀ d hle v
  case open1 => exact fun v => isOpen_setOf_mem_loc₁ d hπ hπM v
  case cont0 => exact fun x v hvx => u₀_continuous_loc d hle x v hvx
  case cont1 => exact fun x v hvx => u₁_continuous_loc d hπ hπM x v hvx
  case lc0 => exact fun x hx => locallyConstant_loc₀ d hle x hx
  case lc1 => exact fun x hx => locallyConstant_loc₁ d hπ hπM x hx
  case inj0 => exact fun x v hv => injective₀_loc d hπ hle hπM hB hd x v hv
  case inj1 => exact fun x v hv => injective₁_loc d hπ hle hπM hB hd x v hv
  case det0 => exact fun x hx => hasDetIndex₀_loc d hle h0 x hx
  case det1 => exact fun x hx => hasDetIndex₁_loc d hπ hle hπM h0 hMM x hx

end CerednikDrinfeld.FormalOmega.QuadrupleLocal

open CerednikDrinfeld.FormalOmega.QuadrupleLocal in
/-- Local construction of a Drinfeld datum from a Deligne datum in an edge chart. -/
theorem CerednikDrinfeld.FormalOmega.DeligneDatum.exists_drinfeldDatum_isQuadrupleOf_of_inEdgeChart
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    {M' M : FullLattice 𝒪 K} (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (h0 : HasDetIndex π M'.1 0)
    (d : DeligneDatum (K := K) π B) (hd : d.InEdgeChart π M' M) :
    ∃ Q : DrinfeldDatum (K := K) π B, Q.IsQuadrupleOf d := by
  by_cases hMM : M'.1 = M.1
  · obtain rfl : M' = M := Subtype.ext hMM
    exact solution_of_ne hπ hB (le_Mpi hπ hπM) (smul_mem_of_mem_Mpi (K := K) hπ _) h0 d
      (inEdgeChart_Mpi_of_inEdgeChart_self d hπ _ hπM hd) (fst_ne_Mpi_fst hπ _ h0)
  · exact solution_of_ne hπ hB hle hπM h0 d hd hMM

end
