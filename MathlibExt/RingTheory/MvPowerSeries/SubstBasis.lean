/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_MvPowerSeries_existsUnique_eq_sum_subst_mul_of_basis_residueField_tensor_
quotient.lean`,
`P2M/Sol/S_MvPowerSeries_existsUnique_eq_sum_subst_mul_of_basis_residueField_tensor_quotient.lean`,
`Theorems/Thm_MvPowerSeries_exists_basis_subst_of_finite_quotient_of_isLocalRing.lean`,
`P2M/Sol/S_MvPowerSeries_exists_basis_subst_of_finite_quotient_of_isLocalRing.lean`,
`Theorems/Thm_MvPowerSeries_eq_of_sum_subst_mul_eq_of_basis_quotient_map_residue.lean`,
`P2M/Sol/S_MvPowerSeries_eq_of_sum_subst_mul_eq_of_basis_quotient_map_residue.lean`,
`Theorems/Thm_MvPowerSeries_exists_eq_sum_subst_mul_of_span_quotient_eq_top.lean`,
`P2M/Sol/S_MvPowerSeries_exists_eq_sum_subst_mul_of_span_quotient_eq_top.lean`,
`Theorems/Thm_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.lean`,
`P2M/Sol/S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.lean`,
`Theorems/Thm_Module_Finite_of_isAdicComplete_of_isHausdorff_of_quotient.lean`,
`P2M/Sol/S_Module_Finite_of_isAdicComplete_of_isHausdorff_of_quotient.lean`
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
removed and the names restated in Mathlib style. The upstream flatness step,
which goes through miracle flatness for regular local rings, is replaced here
by a freeness argument: power series over a field are Cohen--Macaulay, so a
system of parameters is a regular sequence, and a finite
module on which a sequence generating the maximal ideal is weakly regular is free.
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.RingHom.Flat
import MathlibExt.RingTheory.Depth.CohenMacaulaySystemOfParameters
import MathlibExt.RingTheory.MvPowerSeries.RegularLocalRing
import MathlibExt.RingTheory.MvPowerSeries.Span
import MathlibExt.RingTheory.MvPowerSeries.TensorProductQuotientSpan
import MathlibExt.RingTheory.PowerSeries.RegularLocalRing
import MathlibExt.RingTheory.Regular.FreeOfRegularSequence

@[expose] public section

/-!
# Power series as a finite free module over a substituted copy

Let `B` be a Noetherian local ring and `ρ : Fin n → B⟦X₁, …, Xₙ⟧` have zero constant
terms, with some power of every variable in `(ρ)` and `B⟦X⟧ ⧸ (ρ)` finite over `B`.
Then every power series `f` is uniquely `∑ⱼ subst ρ (cⱼ) * bⱼ`, where the `bⱼ` lift a
basis of the fiber `k ⊗[B] (B⟦X⟧ ⧸ (ρ))` over the residue field `k` of `B`.
-/

universe u v

namespace MvPowerSeries.SubstBasisAux

/- Proof outline. Existence (`exists_eq_sum_subst_mul_of_span_quotient_eq_top`) is successive
approximation in the `(X)`-adic topology (`exists_eq_sum_smul`). Uniqueness
(`eq_of_sum_subst_mul_eq_of_basis_quotient_map_residue`) reduces to the residue field by a
dévissage on the ideals of coefficients (`eq_zero_of_sum_subst_mul_eq_zero_of_residue`). Over a
field `k`, `k⟦X⟧` is Cohen–Macaulay, so the parameters form a regular sequence and `k⟦X⟧`, viewed
over itself through the substitution, is free
(`finite_flat_exists_basis_substAlgHom_of_finite_quotient`). -/

section Support

variable {σ : Type*} {R : Type*} [CommRing R]

private def upperPart (i : σ) (N : ℕ) (h : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun m => if N ≤ m i then coeff m h else 0

private theorem coeff_upperPart (i : σ) (N : ℕ) (h : MvPowerSeries σ R) (m : σ →₀ ℕ) :
    coeff m (upperPart i N h) = if N ≤ m i then coeff m h else 0 := rfl

private theorem X_pow_dvd_upperPart (i : σ) (N : ℕ) (h : MvPowerSeries σ R) :
    (X i : MvPowerSeries σ R) ^ N ∣ upperPart i N h :=
  X_pow_dvd_iff.mpr fun m hm => by rw [coeff_upperPart, ite_eq_right (not_le.mpr hm)]

private theorem coeff_sub_upperPart_of_le {i : σ} {N : ℕ} (h : MvPowerSeries σ R) {m : σ →₀ ℕ}
    (hm : N ≤ m i) :
    coeff m (h - upperPart i N h) = 0 := by
  rw [map_sub, coeff_upperPart, ite_eq_left hm, sub_self]

private theorem coeff_sub_upperPart_of_lt {i : σ} {N : ℕ} (h : MvPowerSeries σ R) {m : σ →₀ ℕ}
    (hm : m i < N) :
    coeff m (h - upperPart i N h) = coeff m h := by
  rw [map_sub, coeff_upperPart, ite_eq_right (not_le.mpr hm), sub_zero]

private theorem coeff_eq_zero_of_mem_span (T : Set σ) (N : σ → ℕ) {h : MvPowerSeries σ R}
    (hmem : h ∈ Ideal.span ((fun i => (X i : MvPowerSeries σ R) ^ N i) '' T))
    (m : σ →₀ ℕ) (hm : ∀ i ∈ T, m i < N i) : coeff m h = 0 := by
  classical
  induction hmem using Submodule.span_induction generalizing m with
  | mem p hp =>
    obtain ⟨i, hi, rfl⟩ := hp
    rw [coeff_X_pow, ite_eq_right]
    intro hmi
    have := hm i hi
    rw [hmi, Finsupp.single_eq_same] at this
    exact lt_irrefl _ this
  | zero => exact map_zero _
  | add p q _ _ hp hq => rw [map_add, hp m hm, hq m hm, add_zero]
  | smul a p _ hp =>
    rw [smul_eq_mul, coeff_mul]
    refine Finset.sum_eq_zero fun uv huv => ?_
    rw [hp uv.2 (fun i hi => lt_of_le_of_lt ?_ (hm i hi)), mul_zero]
    have := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
    rw [← this, Finsupp.add_apply]
    exact Nat.le_add_left _ _

private theorem mem_span_X_pow_iff (S : Finset σ) (N : σ → ℕ) (h : MvPowerSeries σ R) :
    h ∈ Ideal.span ((fun i => (X i : MvPowerSeries σ R) ^ N i) '' (↑S : Set σ)) ↔
      ∀ m : σ →₀ ℕ, (∀ i ∈ S, m i < N i) → coeff m h = 0 := by
  classical
  refine ⟨fun hmem m hm => coeff_eq_zero_of_mem_span _ N hmem m (fun i hi => hm i hi), ?_⟩
  induction S using Finset.induction_on generalizing h with
  | empty =>
    intro H
    have : h = 0 := MvPowerSeries.ext fun m =>
        by rw [H m (fun i hi => absurd hi (Finset.notMem_empty i)), map_zero]
    rw [this]
    exact Submodule.zero_mem _
  | insert i S hi IH =>
    intro H
    have h1 : upperPart i (N i) h ∈
        Ideal.span ((fun i => (X i : MvPowerSeries σ R) ^ N i) '' (↑(insert i S) : Set σ)) := by
      obtain ⟨q, hq⟩ := X_pow_dvd_upperPart i (N i) h
      rw [hq]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, Finset.mem_insert_self i S, rfl⟩)
    have h2 : h - upperPart i (N i) h ∈
        Ideal.span ((fun i => (X i : MvPowerSeries σ R) ^ N i) '' (↑(insert i S) : Set σ)) := by
      refine Ideal.span_mono (Set.image_mono (Finset.coe_subset.mpr (Finset.subset_insert i S)))
          (IH _ ?_)
      intro m hm
      by_cases hle : N i ≤ m i
      · exact coeff_sub_upperPart_of_le h hle
      · rw [coeff_sub_upperPart_of_lt h (not_le.mp hle)]
        exact H m fun j hj => by
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact not_le.mp hle
          · exact hm j hj
    have := add_mem h2 h1
    rwa [sub_add_cancel] at this

end Support

section Regular

variable {R : Type*} [CommRing R]

private theorem isSMulRegular_quotient_ideal (I : Ideal R) (r : R) (H : ∀ h, r * h ∈ I → h ∈ I) :
    IsSMulRegular (R ⧸ (I • ⊤ : Submodule R R)) r := by
  have hI : (I • ⊤ : Submodule R R) = I := by rw [Ideal.smul_eq_mul, Ideal.mul_top]
  intro a b hab
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  change r • Submodule.Quotient.mk a = r • Submodule.Quotient.mk b at hab
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq,
    ← smul_sub, hI, smul_eq_mul] at hab
  rw [Submodule.Quotient.eq, hI]
  exact H _ hab

variable {n : ℕ}

private theorem setOf_mem_take_ofFn {α : Type*} (y : Fin n → α) (j : ℕ) :
    {r | r ∈ (List.ofFn y).take j} = y '' {i : Fin n | (i : ℕ) < j} := by
  ext r
  simp only [Set.mem_ofPred_eq, Set.mem_image, List.mem_iff_getElem, List.length_take,
    List.length_ofFn, List.getElem_take, List.getElem_ofFn]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, (lt_min_iff.mp hi).2⟩, (lt_min_iff.mp hi).1, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, lt_min_iff.mpr ⟨hi, i.2⟩, rfl⟩

private theorem isWeaklyRegular_X_pow (N : Fin n → ℕ) :
    RingTheory.Sequence.IsWeaklyRegular (MvPowerSeries (Fin n) R)
      (List.ofFn fun i : Fin n => (X i : MvPowerSeries (Fin n) R) ^ N i) := by
  classical
  refine (RingTheory.Sequence.isWeaklyRegular_iff_Fin _ _).mpr fun j => ?_
  rw [Fin.getElem_fin, List.getElem_ofFn]
  apply isSMulRegular_quotient_ideal
  intro h hmem
  have hS : {r | r ∈ (List.ofFn fun i : Fin n => (X i : MvPowerSeries (Fin n) R) ^ N i).take j} =
      (fun i => (X i : MvPowerSeries (Fin n) R) ^ (N i)) ''
        (↑(Finset.univ.filter fun i : Fin n => (i : ℕ) < j) : Set (Fin n)) := by
    rw [setOf_mem_take_ofFn, Finset.coe_filter]
    simp
  dsimp only [Ideal.ofList] at hmem ⊢
  rw [hS, mem_span_X_pow_iff (N := fun i => N i)] at hmem ⊢
  intro m hm
  have hjn : (j : ℕ) < n := by simpa using j.2
  have key := hmem (Finsupp.single (⟨j, hjn⟩ : Fin n) (N ⟨j, hjn⟩) + m) fun i hi => by
    have hij : (i : ℕ) < j := (Finset.mem_filter.mp hi).2
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne, zero_add]
    · exact hm i hi
    · intro h'; rw [h'] at hij; exact lt_irrefl (j : ℕ) hij
  rwa [X_pow_eq, coeff_add_monomial_mul, one_mul] at key

end Regular

section VariableIdeal

variable {σ R : Type*} [CommRing R]

private theorem span_range_le_ker {ι : Type*} {g : ι → MvPowerSeries σ R}
    (hg : ∀ i, constantCoeff (g i) = 0) :
    Ideal.span (Set.range g) ≤ RingHom.ker (constantCoeff : MvPowerSeries σ R →+* R) := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact hg i

private theorem span_range_ne_top [Nontrivial R] {ι : Type*} {g : ι → MvPowerSeries σ R}
    (hg : ∀ i, constantCoeff (g i) = 0) : Ideal.span (Set.range g) ≠ ⊤ := fun htop => by
  have h1 := span_range_le_ker hg (htop ▸ Submodule.mem_top : (1 : MvPowerSeries σ R) ∈ _)
  rw [RingHom.mem_ker, map_one] at h1
  exact one_ne_zero h1

private theorem ofList_ofFn {A : Type*} [CommRing A] {d : ℕ} (g : Fin d → A) :
    Ideal.ofList (List.ofFn g) = Ideal.span (Set.range g) := by
  rw [Ideal.ofList]
  congr 1
  ext f
  simp [List.mem_ofFn, eq_comm]

end VariableIdeal

-- `A` as an algebra over itself through a ring endomorphism `φ`: the module structures
-- over a substituted copy are all of this form.
private def Tgt {A : Type u} [CommRing A] (_φ : A →+* A) : Type u := A

private noncomputable local instance {A : Type u} [CommRing A] (φ : A →+* A) :
    CommRing (Tgt φ) :=
  inferInstanceAs (CommRing A)

private def toTgt {A : Type u} [CommRing A] (φ : A →+* A) : A →+* Tgt φ := φ

private noncomputable local instance {A : Type u} [CommRing A] (φ : A →+* A) :
    Algebra A (Tgt φ) :=
  (toTgt φ).toAlgebra

private noncomputable def ofT {A : Type u} [CommRing A] (φ : A →+* A) : Tgt φ ≃+* A :=
  RingEquiv.refl _

private theorem ofT_algebraMap {A : Type u} [CommRing A] (φ : A →+* A) (r : A) :
    ofT φ (algebraMap A (Tgt φ) r) = φ r := rfl

private theorem ofT_smul {A : Type u} [CommRing A] (φ : A →+* A) (r : A) (t : Tgt φ) :
    ofT φ (r • t) = φ r * ofT φ t := by
  rw [Algebra.smul_def, map_mul, ofT_algebraMap]

private theorem ringKrullDim_mvPowerSeries_fin (k : Type u) [Field k] (n : ℕ) :
    ringKrullDim (MvPowerSeries (Fin n) k) = n := by
  induction n with
  | zero =>
    rw [ringKrullDim_eq_of_ringEquiv (MvPowerSeries.isEmptyEquiv (Fin 0) k).toRingEquiv,
      ringKrullDim_eq_zero_of_field]
    simp
  | succ n ih =>
    have := IsRegularLocalRing.mvPowerSeries_fin k n
    rw [ringKrullDim_eq_of_ringEquiv (MvPowerSeries.finSuccEquiv k n).toRingEquiv,
      PowerSeries.ringKrullDim_powerSeries, ih]
    push_cast
    rfl

private theorem span_range_X_eq_maximalIdeal (k : Type u) [Field k] (d : ℕ) :
    Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) k)) =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) k) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff,
      constantCoeff_X, isUnit_iff_ne_zero]
    exact fun h => h rfl
  · intro f hf
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff,
      isUnit_iff_ne_zero, not_not] at hf
    exact (span_range_X_eq_ker_constantCoeff d).ge (RingHom.mem_ker.mpr hf)

private theorem isRegular_X (k : Type u) [Field k] (n : ℕ) :
    RingTheory.Sequence.IsRegular (MvPowerSeries (Fin n) k)
      (List.ofFn (X : Fin n → MvPowerSeries (Fin n) k)) := by
  refine ⟨by simpa using isWeaklyRegular_X_pow (R := k) (n := n) (fun _ => 1), ?_⟩
  rw [smul_eq_mul, Ideal.mul_top, ofList_ofFn]
  exact (span_range_ne_top (g := (X : Fin n → MvPowerSeries (Fin n) k))
    fun i => constantCoeff_X i).symm

private theorem depth_mvPowerSeries_fin (k : Type u) [Field k] (n : ℕ) :
    (IsLocalRing.depth (ModuleCat.of (MvPowerSeries (Fin n) k) (MvPowerSeries (Fin n) k)) :
      WithBot ℕ∞) = ringKrullDim (MvPowerSeries (Fin n) k) := by
  have := IsRegularLocalRing.mvPowerSeries_fin k n
  rw [ringKrullDim_mvPowerSeries_fin, IsLocalRing.depth_eq_sSup_length_isRegular]
  have hS : sSup {(List.length rs : ℕ∞) | (rs : List (MvPowerSeries (Fin n) k))
      (_ : RingTheory.Sequence.IsRegular (ModuleCat.of (MvPowerSeries (Fin n) k)
        (MvPowerSeries (Fin n) k)) rs)
      (_ : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) k))} = (n : ℕ∞) := by
    apply le_antisymm
    · refine sSup_le ?_
      rintro _ ⟨rs, hreg, -, rfl⟩
      have h := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular rs hreg
      have hne : Ideal.ofList rs ≠ ⊤ := fun htop =>
        hreg.top_ne_smul (by rw [htop, Submodule.top_smul])
      have : Nontrivial (MvPowerSeries (Fin n) k ⧸ Ideal.ofList rs) :=
        Ideal.Quotient.nontrivial_iff.mpr hne
      have hle := le_add_of_nonneg_left (a := (rs.length : WithBot ℕ∞))
        (ringKrullDim_nonneg_of_nontrivial (R := MvPowerSeries (Fin n) k ⧸ Ideal.ofList rs))
      rw [h, ringKrullDim_mvPowerSeries_fin] at hle
      exact_mod_cast hle
    · refine le_sSup ⟨List.ofFn (X : Fin n → MvPowerSeries (Fin n) k), isRegular_X k n, ?_, by simp⟩
      intro r hr
      rw [← span_range_X_eq_maximalIdeal, ← ofList_ofFn]
      exact Ideal.subset_span hr
  rw [hS]
  rfl

private theorem isRegular_ofFn_of_finite_quotient {k : Type u} [Field k] {d : ℕ}
    (g : Fin d → MvPowerSeries (Fin d) k) (hg : ∀ i, constantCoeff (g i) = 0)
    (hfin : Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g))) :
    RingTheory.Sequence.IsRegular (MvPowerSeries (Fin d) k) (List.ofFn g) := by
  have := IsRegularLocalRing.mvPowerSeries_fin k d
  have : Nontrivial (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g)) :=
    Ideal.Quotient.nontrivial_iff.mpr (span_range_ne_top hg)
  have : IsArtinianRing (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g)) :=
    IsArtinianRing.of_finite k _
  refine IsLocalRing.isRegular_of_systemOfParameters (depth_mvPowerSeries_fin k d)
    (ringKrullDim_mvPowerSeries_fin k d) (List.ofFn g) (by simp) ?_ ?_
  · intro y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff, hg i]
    exact not_isUnit_zero
  · rw [ofList_ofFn]
    exact (ringKrullDimZero_iff_ringKrullDim_eq_zero).mp inferInstance

section Completion

variable {R : Type*} [CommRing R] (I : Ideal R) {M : Type*} [AddCommGroup M] [Module R M]

private theorem smul_top_pow_succ (k : ℕ) :
    I ^ k • (I • (⊤ : Submodule R M)) = I ^ (k + 1) • ⊤ := by
  rw [← Submodule.smul_assoc, Ideal.smul_eq_mul, ← pow_succ]

private theorem step {d : ℕ} (m : Fin d → M)
    (hgen : ∀ x : M, ∃ a : Fin d → R, x - ∑ j, a j • m j ∈ I • (⊤ : Submodule R M))
    (k : ℕ) (x : M) (hx : x ∈ I ^ k • (⊤ : Submodule R M)) :
    ∃ a : Fin d → R, (∀ j, a j ∈ I ^ k) ∧
      x - ∑ j, a j • m j ∈ I ^ (k + 1) • (⊤ : Submodule R M) := by
  classical
  induction hx using Submodule.smul_induction_on' with
  | smul r hr y _ =>
    obtain ⟨a, ha⟩ := hgen y
    refine ⟨fun j => r * a j, fun j => Ideal.mul_mem_right _ _ hr, ?_⟩
    have : r • y - ∑ j, (r * a j) • m j = r • (y - ∑ j, a j • m j) := by
      rw [smul_sub, Finset.smul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => (smul_smul r (a j) (m j)).symm
    rw [this, ← smul_top_pow_succ]
    exact Submodule.smul_mem_smul hr ha
  | add x hx y hy ihx ihy =>
    obtain ⟨a, ha, hax⟩ := ihx
    obtain ⟨a', ha', hay⟩ := ihy
    refine ⟨a + a', fun j => Ideal.add_mem _ (ha j) (ha' j), ?_⟩
    have : x + y - ∑ j, (a + a') j • m j = (x - ∑ j, a j • m j) + (y - ∑ j, a' j • m j) := by
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]; abel
    rw [this]
    exact Submodule.add_mem _ hax hay

private theorem exists_eq_sum_smul [IsAdicComplete I R] [IsHausdorff I M] {d : ℕ} (m : Fin d → M)
    (hgen : ∀ x : M, ∃ a : Fin d → R, x - ∑ j, a j • m j ∈ I • (⊤ : Submodule R M)) (x : M) :
    ∃ c : Fin d → R, x = ∑ j, c j • m j := by
  classical
  have hstep : ∀ (k : ℕ) (z : {z : M // z ∈ I ^ k • (⊤ : Submodule R M)}),
      ∃ a : Fin d → R, (∀ j, a j ∈ I ^ k) ∧ z.1 - ∑ j, a j • m j ∈ I ^ (k + 1) •
          (⊤ : Submodule R M) :=
    fun k z => step I m hgen k z.1 z.2
  choose A hAI hAnext using hstep
  let seq : (k : ℕ) → {z : M // z ∈ I ^ k • (⊤ : Submodule R M)} :=
    fun k => Nat.rec (motive := fun k => {z : M // z ∈ I ^ k • (⊤ : Submodule R M)})
      ⟨x, by rw [pow_zero, one_smul]; exact Submodule.mem_top⟩
      (fun k z => ⟨z.1 - ∑ j, A k z j • m j, hAnext k z⟩) k
  have hseq0 : (seq 0).1 = x := rfl
  have hseqS : ∀ k, (seq (k + 1)).1 = (seq k).1 - ∑ j, A k (seq k) j • m j := fun k => rfl
  let a : ℕ → Fin d → R := fun k => A k (seq k)
  have haI : ∀ k j, a k j ∈ I ^ k := fun k j => hAI k (seq k) j
  let s : ℕ → Fin d → R := fun K j => ∑ k ∈ Finset.range K, a k j
  have hpartial : ∀ K, x = ∑ j, s K j • m j + (seq K).1 := by
    intro K
    induction K with
    | zero => simp [s, hseq0]
    | succ K ih =>
      rw [hseqS, ih]
      simp only [s, Finset.sum_range_succ, add_smul, Finset.sum_add_distrib]
      abel
  have hcauchy : ∀ j, ∀ {m' n' : ℕ}, m' ≤ n' → s m' j ≡ s n' j
      [SMOD (I ^ m' • ⊤ : Submodule R R)] := by
    intro j m' n' hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    have : s m' j - s n' j = -∑ k ∈ Finset.Ico m' n', a k j := by
      simp only [s]
      rw [← Finset.sum_range_add_sum_Ico _ hmn]
      abel
    rw [this, neg_mem_iff]
    exact Ideal.sum_mem _ fun k hk => Ideal.pow_le_pow_right (Finset.mem_Ico.mp hk).1 (haI k j)
  have hlim : ∀ j, ∃ c : R, ∀ K, s K j ≡ c [SMOD (I ^ K • ⊤ : Submodule R R)] :=
    fun j => IsPrecomplete.prec' _ (hcauchy j)
  choose c hc using hlim
  refine ⟨c, ?_⟩
  apply eq_of_sub_eq_zero
  refine IsHausdorff.haus' (I := I) _ fun K => ?_
  rw [SModEq.sub_mem, sub_zero]
  have hdiff : x - ∑ j, c j • m j = (seq K).1 - ∑ j, (c j - s K j) • m j := by
    conv_lhs => rw [hpartial K]
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel
  rw [hdiff]
  refine Submodule.sub_mem _ (seq K).2 (Submodule.sum_mem _ fun j _ => ?_)
  have hcj : c j - s K j ∈ I ^ K := by
    have := (hc j K).symm
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
    exact this
  exact Submodule.smul_mem_smul hcj Submodule.mem_top

end Completion

-- A module over an `I`-adically complete ring that is `I`-adically Hausdorff and finite
-- modulo `I` is finite.
private theorem finite_of_isAdicComplete_of_isHausdorff_of_quotient
    {R : Type u} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : Type v) [AddCommGroup M] [Module R M] [IsHausdorff I M]
    (h : Module.Finite R (M ⧸ (I • ⊤ : Submodule R M))) :
    Module.Finite R M := by
  classical
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin (R := R) (M := M ⧸ (I • ⊤ : Submodule R M))
  choose s hs using fun i => Submodule.mkQ_surjective (I • ⊤ : Submodule R M) (f i)
  have hgen : ∀ x : M, ∃ a : Fin n → R, x - ∑ j, a j • s j ∈ I • (⊤ : Submodule R M) := by
    intro x
    have hx : (I • ⊤ : Submodule R M).mkQ x ∈ Submodule.span R (Set.range f) := by
      rw [hf]; exact Submodule.mem_top
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hx
    refine ⟨a, ?_⟩
    rw [← Submodule.ker_mkQ (I • ⊤ : Submodule R M), LinearMap.mem_ker, map_sub, map_sum,
      sub_eq_zero, ← ha]
    simp only [map_smul, hs]
  rw [Module.finite_def]
  refine ⟨Finset.univ.image s, eq_top_iff.mpr fun x _ => ?_⟩
  obtain ⟨c, rfl⟩ := exists_eq_sum_smul I s hgen x
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

-- Over a field `k`, substitution by `g` with finite quotient makes `k⟦X⟧` finite and flat
-- over itself, with an explicit basis.
private theorem finite_flat_exists_basis_substAlgHom_of_finite_quotient
    {k : Type u} [Field k] {d : ℕ} (g : Fin d → MvPowerSeries (Fin d) k)
    (hg : ∀ i, MvPowerSeries.constantCoeff (g i) = 0)
    (hfin : Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g))) :
    RingHom.Finite (A := MvPowerSeries (Fin d) k) (B := MvPowerSeries (Fin d) k)
      (MvPowerSeries.substAlgHom (R := k) (MvPowerSeries.hasSubst_of_constantCoeff_zero
          hg)).toRingHom ∧
    RingHom.Flat (R := MvPowerSeries (Fin d) k) (S := MvPowerSeries (Fin d) k)
      (MvPowerSeries.substAlgHom (R := k) (MvPowerSeries.hasSubst_of_constantCoeff_zero
          hg)).toRingHom ∧
    ∃ b : Fin (Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g))) →
        MvPowerSeries (Fin d) k,
      ∀ x : MvPowerSeries (Fin d) k,
        ∃! c : Fin (Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g))) →
            MvPowerSeries (Fin d) k,
          x = ∑ i, MvPowerSeries.subst g (c i) * b i := by
  classical
  let φa : MvPowerSeries (Fin d) k →ₐ[k] MvPowerSeries (Fin d) k :=
    MvPowerSeries.substAlgHom (R := k) (MvPowerSeries.hasSubst_of_constantCoeff_zero hg)
  let φ : MvPowerSeries (Fin d) k →+* MvPowerSeries (Fin d) k := φa.toRingHom
  have hφ : ∀ x, φ x = MvPowerSeries.subst g x := fun x => by
    change φa x = _
    rw [MvPowerSeries.coe_substAlgHom]
  have hφX : ∀ i, φ (MvPowerSeries.X i) = g i := fun i => by
    rw [hφ, MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hg)]
  have hφC : ∀ c : k, φ (MvPowerSeries.C c) = MvPowerSeries.C c := fun c => by
    change φa (MvPowerSeries.C c) = _
    rw [MvPowerSeries.c_eq_algebraMap, AlgHom.commutes]
  let T := Tgt φ
  let e : T ≃+* MvPowerSeries (Fin d) k := ofT φ
  have he_smul : ∀ (r : MvPowerSeries (Fin d) k) (t : T), e (r • t) = φ r * e t :=
    ofT_smul φ
  have he_symm : ∀ x, e (e.symm x) = x := (ofT φ).apply_symm_apply
  let 𝔫 : Ideal (MvPowerSeries (Fin d) k) := Ideal.span (Set.range MvPowerSeries.X)
  have hrg : (⇑φ) '' Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) k) =
      Set.range g := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext hφX)
  have hmap : Ideal.map (algebraMap (MvPowerSeries (Fin d) k) T) 𝔫 =
      Ideal.comap e (Ideal.span (Set.range g)) := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, Ideal.mem_comap, ofT_algebraMap, ← Ideal.mem_comap]
      have : 𝔫 ≤ Ideal.comap φ (Ideal.span (Set.range g)) := by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_span, hrg]
      exact this hr
    · intro t ht
      rw [Ideal.mem_comap] at ht
      have hsurj : ∀ y ∈ Ideal.span (Set.range g), e.symm y ∈
          Ideal.map (algebraMap (MvPowerSeries (Fin d) k) T) 𝔫 := by
        intro y hy
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
        · rintro _ ⟨i, rfl⟩
          rw [← hφX]
          exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)
        · rw [map_zero]; exact Ideal.zero_mem _
        · intro a b _ _ ha hb; rw [map_add]; exact Ideal.add_mem _ ha hb
        · intro a b _ hb; rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ hb
      have := hsurj (e t) ht
      rwa [RingEquiv.symm_apply_apply] at this
  have hsmul : ∀ (n : ℕ) (t : T),
      t ∈ (𝔫 ^ n • ⊤ : Submodule (MvPowerSeries (Fin d) k) T) ↔
        e t ∈ (Ideal.span (Set.range g) : Ideal (MvPowerSeries (Fin d) k)) ^ n := by
    intro n t
    rw [Ideal.smul_top_eq_map, Ideal.map_pow, hmap, Submodule.restrictScalars_mem, ← Ideal.map_symm,
      ← Ideal.map_pow, Ideal.map_symm, Ideal.mem_comap]
  have hgne : (Ideal.span (Set.range g) : Ideal (MvPowerSeries (Fin d) k)) ≠ ⊤ :=
    span_range_ne_top hg
  have hhaus : IsHausdorff 𝔫 T := by
    refine ⟨fun z hz => ?_⟩
    have hz' : ∀ n : ℕ, e z ∈ (Ideal.span (Set.range g) : Ideal _) ^ n := fun n => by
      have h := hz n
      rw [SModEq.sub_mem, sub_zero] at h
      exact (hsmul n z).mp h
    have hmem : e z ∈ ⨅ n : ℕ, (Ideal.span (Set.range g) : Ideal _) ^ n := Ideal.mem_iInf.mpr hz'
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ hgne, Ideal.mem_bot] at hmem
    exact e.map_eq_zero_iff.mp hmem
  have hfinq : Module.Finite (MvPowerSeries (Fin d) k)
      (T ⧸ (𝔫 • ⊤ : Submodule (MvPowerSeries (Fin d) k) T)) := by
    obtain ⟨m, f, hf⟩ :=
      Module.Finite.exists_fin (R := k) (M := MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g))
    choose t ht using fun j => Ideal.Quotient.mk_surjective (I := Ideal.span (Set.range g)) (f j)
    rw [Module.finite_def]
    refine ⟨(Finset.univ : Finset (Fin m)).image fun j =>
      Submodule.Quotient.mk (p := (𝔫 • ⊤ : Submodule (MvPowerSeries (Fin d) k) T)) (e.symm (t j)),
        eq_top_iff.mpr ?_⟩
    rintro y -
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hx : Ideal.Quotient.mk (Ideal.span (Set.range g))
        (e x) ∈ Submodule.span k (Set.range f) := by
      rw [hf]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hx
    have hdiff : e x - ∑ j, c j • t j ∈ Ideal.span (Set.range g) := by
      rw [← Ideal.Quotient.eq, map_sum, ← hc]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← ht j]
      simp only [← Ideal.Quotient.mkₐ_eq_mk k, map_smul]
    have hdiff' : x - ∑ j, (MvPowerSeries.C (c j) : MvPowerSeries (Fin d) k) • e.symm (t j) ∈
        (𝔫 • ⊤ : Submodule (MvPowerSeries (Fin d) k) T) := by
      rw [show (𝔫 • ⊤ : Submodule (MvPowerSeries (Fin d) k) T) = 𝔫 ^ 1 • ⊤ by rw [pow_one],
        hsmul 1, pow_one, map_sub, map_sum]
      convert hdiff using 2
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [he_smul, he_symm, hφC, MvPowerSeries.smul_eq_C_mul]
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    have hquot : Submodule.Quotient.mk (p := (𝔫 • ⊤ : Submodule (MvPowerSeries (Fin d) k) T)) x =
        ∑ j, (MvPowerSeries.C (c j) : MvPowerSeries (Fin d) k) •
          Submodule.Quotient.mk (p := (𝔫 • ⊤ : Submodule (MvPowerSeries (Fin d) k) T))
              (e.symm (t j)) := by
      have h0 : (𝔫 • ⊤ : Submodule (MvPowerSeries (Fin d) k) T).mkQ
          (x - ∑ j, (MvPowerSeries.C (c j) : MvPowerSeries (Fin d) k) • e.symm (t j)) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr hdiff'
      rw [map_sub, map_sum] at h0
      simp only [map_smul, Submodule.mkQ_apply] at h0
      exact sub_eq_zero.mp h0
    rw [hquot]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hfinT : Module.Finite (MvPowerSeries (Fin d) k) T :=
    finite_of_isAdicComplete_of_isHausdorff_of_quotient 𝔫 T hfinq
  have hreg : IsRegularLocalRing (MvPowerSeries (Fin d) k) :=
    IsRegularLocalRing.mvPowerSeries_fin k d
  have hmaxX : Ideal.ofList (List.ofFn (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) k)) =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) k) := by
    rw [ofList_ofFn]
    exact span_range_X_eq_maximalIdeal k d
  have hfree : Module.Free (MvPowerSeries (Fin d) k) T := by
    refine Module.free_of_isWeaklyRegular_of_span_eq_maximalIdeal _ hmaxX T ?_
    rw [← RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff T T]
    have hmap : (List.ofFn (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) k)).map
        (algebraMap (MvPowerSeries (Fin d) k) T) = List.ofFn g := by
      rw [List.map_ofFn]
      congr 1
      funext i
      exact hφX i
    rw [hmap]
    exact (isRegular_ofFn_of_finite_quotient g hg hfin).toIsWeaklyRegular
  have hflat : Module.Flat (MvPowerSeries (Fin d) k) T := Module.Flat.of_free
  let ι := Module.Free.ChooseBasisIndex (MvPowerSeries (Fin d) k) T
  let b : Module.Basis ι (MvPowerSeries (Fin d) k) T := Module.Free.chooseBasis _ _
  have huniqT : ∀ a a' : ι → MvPowerSeries (Fin d) k,
      ∑ i, a i • b i = ∑ i, a' i • b i → a = a' := by
    intro a a' h
    have hli := b.linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    have h0 : ∑ i, (a i - a' i) • b i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]
    funext i
    exact sub_eq_zero.mp (hli _ h0 i)
  have hexp : ∀ x : MvPowerSeries (Fin d) k, x = ∑ i, φ (b.repr (e.symm x) i) * e (b i) := by
    intro x
    conv_lhs => rw [← he_symm x, ← b.sum_repr (e.symm x)]
    rw [map_sum]
    simp only [he_smul]
  have huniq : ∀ a a' : ι → MvPowerSeries (Fin d) k,
      ∑ i, φ (a i) * e (b i) = ∑ i, φ (a' i) * e (b i) → a = a' := by
    intro a a' h
    refine huniqT a a' (e.injective ?_)
    rw [map_sum, map_sum]
    simp only [he_smul]
    exact h
  let πg := Ideal.Quotient.mk (Ideal.span (Set.range g))
  have hπC : ∀ c : k, πg (MvPowerSeries.C c) = algebraMap k _ c := fun c => by
    rw [IsScalarTower.algebraMap_apply k (MvPowerSeries (Fin d) k)
        (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g)),
      Ideal.Quotient.algebraMap_eq, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self,
          RingHom.id_apply]
  have hφmod : ∀ r, πg (φ r) = algebraMap k _ (MvPowerSeries.constantCoeff r) := by
    intro r
    have hr : r - MvPowerSeries.C (MvPowerSeries.constantCoeff r) ∈ 𝔫 :=
      (span_range_X_eq_ker_constantCoeff d).ge
        (RingHom.mem_ker.mpr (by rw [map_sub, MvPowerSeries.constantCoeff_C, sub_self]))
    have h1 : φ r - MvPowerSeries.C (MvPowerSeries.constantCoeff r) ∈ Ideal.span (Set.range g) := by
      rw [← hφC, ← map_sub]
      have h2 := Ideal.mem_map_of_mem φ hr
      rwa [Ideal.map_span, hrg] at h2
    rw [← hπC, eq_comm, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    rw [← Ideal.neg_mem_iff, neg_sub]
    exact h1
  let ev : ι → MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g) := fun i => πg (e (b i))
  have hspan : ⊤ ≤ Submodule.span k (Set.range ev) := by
    rintro y -
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hexp x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_mul, hφmod, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hli : LinearIndependent k ev := by
    rw [Fintype.linearIndependent_iff]
    intro l hl i
    have hz : ∑ i, MvPowerSeries.C (l i) * e (b i) ∈ Ideal.span (Set.range g) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum, ← hl]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hπC, ← Algebra.smul_def]
    have hw : ∑ i, (MvPowerSeries.C (l i) : MvPowerSeries (Fin d) k) • b i ∈
        (𝔫 • ⊤ : Submodule (MvPowerSeries (Fin d) k) T) := by
      rw [show (𝔫 • ⊤ : Submodule (MvPowerSeries (Fin d) k) T) = 𝔫 ^ 1 • ⊤ by rw [pow_one],
        hsmul 1, pow_one, map_sum]
      simp only [he_smul, hφC]
      exact hz
    rw [← b.span_eq, Submodule.mem_ideal_smul_span_iff_exists_sum] at hw
    obtain ⟨a, ha, hsum⟩ := hw
    rw [Finsupp.sum_fintype a (fun i c => c • b i) (fun i => zero_smul (MvPowerSeries (Fin d) k)
        (b i))] at hsum
    have heq : (⇑a) = fun i => MvPowerSeries.C (l i) := huniqT _ _ hsum
    have hai : MvPowerSeries.C (l i) ∈ 𝔫 := by
      rw [← congrFun heq i]
      exact ha i
    have := (span_range_X_eq_ker_constantCoeff d).le hai
    rwa [RingHom.mem_ker, MvPowerSeries.constantCoeff_C] at this
  have hcard : Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g)) =
      Fintype.card ι :=
    Module.finrank_eq_card_basis (Module.Basis.mk hli hspan)
  let σe : ι ≃ Fin (Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g))) :=
    Fintype.equivFinOfCardEq hcard.symm
  refine ⟨hfinT, hflat, fun j => e (b (σe.symm j)), fun x =>
      ⟨fun j => b.repr (e.symm x) (σe.symm j), ?_, ?_⟩⟩
  · change x = ∑ j, MvPowerSeries.subst g (b.repr (e.symm x) (σe.symm j)) * e (b (σe.symm j))
    simp only [← hφ]
    rw [Equiv.sum_comp σe.symm (fun i => φ (b.repr (e.symm x) i) * e (b i))]
    exact hexp x
  · intro c' hc'
    simp only [← hφ] at hc'
    have h1 : ∑ i, φ (c' (σe i)) * e (b i) = ∑ i, φ (b.repr (e.symm x) i) * e (b i) := by
      rw [← hexp x, hc', ← Equiv.sum_comp σe.symm (fun i => φ (c' (σe i)) * e (b i))]
      simp only [Equiv.apply_symm_apply]
    have h2 := huniq _ _ h1
    funext j
    have := congrFun h2 (σe.symm j)
    simpa only [Equiv.apply_symm_apply] using this

section Residue

open MvPowerSeries IsLocalRing

section Devissage

variable {B : Type*} [CommRing B]

section CoeffIn

variable {σ : Type*}

private def CoeffIn (I : Ideal B) (f : MvPowerSeries σ B) : Prop := ∀ d : σ →₀ ℕ, coeff d f ∈ I

private theorem CoeffIn.top (f : MvPowerSeries σ B) : CoeffIn ⊤ f := fun _ => Submodule.mem_top

private theorem CoeffIn.sum {I : Ideal B} {κ : Type*} (s : Finset κ) {f : κ → MvPowerSeries σ B}
    (hf : ∀ l ∈ s, CoeffIn I (f l)) : CoeffIn I (∑ l ∈ s, f l) := fun d => by
  rw [map_sum]; exact I.sum_mem fun l hl => hf l hl d

private theorem CoeffIn.smul_mem {I J : Ideal B} {r : B} (hr : r ∈ J) {f : MvPowerSeries σ B}
    (hf : CoeffIn I f) :
    CoeffIn (J * I) (r • f) :=
  fun d => by rw [map_smul, smul_eq_mul]; exact Ideal.mul_mem_mul hr (hf d)

private theorem coeffIn_maximalIdeal_iff [IsLocalRing B] (f : MvPowerSeries σ B) :
    CoeffIn (maximalIdeal B) f ↔ map (residue B) f = 0 := by
  rw [MvPowerSeries.ext_iff]
  refine forall_congr' fun d => ?_
  rw [coeff_map, coeff_zero, residue_eq_zero_iff]

private theorem eq_zero_of_forall_coeffIn_pow [IsNoetherianRing B] [IsLocalRing B]
    (f : MvPowerSeries σ B)
    (h : ∀ j : ℕ, CoeffIn (maximalIdeal B ^ j) f) : f = 0 := by
  ext d
  rw [coeff_zero]
  have hmem : coeff d f ∈ ⨅ j : ℕ, maximalIdeal B ^ j := Ideal.mem_iInf.mpr fun j => h j d
  rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal B).ne_top,
      Ideal.mem_bot] at hmem

end CoeffIn

private theorem exists_minimal_generators [IsNoetherianRing B] [IsLocalRing B] (I : Ideal B) :
    ∃ (s : ℕ) (b : Fin s → B), Ideal.span (Set.range b) = I ∧
      ∀ c : Fin s → B, ∑ l, c l * b l ∈ maximalIdeal B * I → ∀ l, c l ∈ maximalIdeal B := by
  classical
  have hex : ∃ s : ℕ, ∃ b : Fin s → B, Ideal.span (Set.range b) = I := by
    obtain ⟨s, b, hb⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
        (IsNoetherian.noetherian I)
    exact ⟨s, b, hb⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).choose, (Nat.find_spec hex).choose_spec, ?_⟩
  set s := Nat.find hex with hs
  set b : Fin s → B := (Nat.find_spec hex).choose with hb
  have hbI : Ideal.span (Set.range b) = I := (Nat.find_spec hex).choose_spec
  intro c hc
  by_contra hcon
  push Not at hcon
  obtain ⟨l₀, hl₀⟩ := hcon
  have hu : IsUnit (c l₀) := by
    by_contra h; exact hl₀ ((mem_maximalIdeal _).mpr h)
  obtain ⟨u, hu⟩ := hu
  obtain ⟨s', hs'⟩ : ∃ s', s = s' + 1 := ⟨s - 1, (Nat.succ_pred_eq_of_pos (Fin.pos l₀)).symm⟩
  let ε : Fin (s' + 1) ≃ Fin s := finCongr hs'.symm
  let l₁ : Fin (s' + 1) := ε.symm l₀
  let b' : Fin s' → B := fun l => b (ε (l₁.succAbove l))
  have hb'I : Ideal.span (Set.range b') = I := by
    apply le_antisymm
    · rw [← hbI]
      exact Ideal.span_mono (by rintro _ ⟨l, rfl⟩; exact ⟨_, rfl⟩)
    · have hle : (I : Submodule B B) ≤ Ideal.span (Set.range b') ⊔ maximalIdeal B • I := by
        suffices h : Ideal.span (Set.range b) ≤ Ideal.span (Set.range b') ⊔ maximalIdeal B • I by
          rwa [hbI] at h
        rw [Ideal.span_le]
        rintro _ ⟨l, rfl⟩
        by_cases hll : l = l₀
        · rw [hll]
          have hsplit : ∑ l, c l * b l = c l₀ * b l₀ + ∑ l, c (ε (l₁.succAbove l)) * b' l := by
            rw [← Equiv.sum_comp ε (fun l => c l * b l), Fin.sum_univ_succAbove _ l₁]
            simp [l₁, b']
          have heq : b l₀ = ↑u⁻¹ * (∑ l, c l * b l - ∑ l, c (ε (l₁.succAbove l)) * b' l) := by
            rw [hsplit, add_sub_cancel_right, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
          rw [heq]
          refine Ideal.mul_mem_left _ _ (Submodule.sub_mem _ ?_ ?_)
          · refine Submodule.mem_sup_right ?_
            rw [Ideal.smul_eq_mul]
            exact hc
          · refine Submodule.mem_sup_left (Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ ?_)
            exact Ideal.subset_span ⟨l, rfl⟩
        · refine Submodule.mem_sup_left (Ideal.subset_span ?_)
          obtain ⟨l', hl'⟩ := Fin.exists_succAbove_eq (x := ε.symm l) (y := l₁)
            (by intro h; exact hll (by simpa [l₁] using congrArg ε h))
          exact ⟨l', by simp [b', hl']⟩
      exact Submodule.le_of_le_smul_of_le_jacobson (IsNoetherian.noetherian I)
        (ringJacobson_eq_maximalIdeal _).ge hle
  have hmin := Nat.find_min hex (m := s') (by omega)
  exact hmin ⟨b', hb'I⟩

section SumSubst

variable [IsNoetherianRing B] [IsLocalRing B] {σ τ ι : Type*} [Finite σ] [Fintype ι]

private theorem eq_zero_of_sum_subst_mul_eq_zero_of_residue
    {a : σ → MvPowerSeries τ B} (ha0 : ∀ s, constantCoeff (a s) = 0) (e : ι → MvPowerSeries τ B)
    (hres : ∀ w : ι → MvPowerSeries σ (ResidueField B),
      ∑ i, subst (fun s => map (residue B) (a s)) (w i) * map (residue B) (e i) = 0 → w = 0)
    (c : ι → MvPowerSeries σ B) (hc : ∑ i, subst a (c i) * e i = 0) : c = 0 := by
  classical
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  let Ψ : (ι → MvPowerSeries σ B) →ₗ[B] MvPowerSeries τ B :=
    ∑ i, (LinearMap.mulRight B (e i)).comp ((substAlgHom ha).toLinearMap.comp (LinearMap.proj i))
  have hΨ : ∀ w : ι → MvPowerSeries σ B, Ψ w = ∑ i, subst a (w i) * e i := by
    intro w
    simp only [Ψ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      AlgHom.toLinearMap_apply, substAlgHom_apply, LinearMap.mulRight_apply]
  have hΨres : ∀ w : ι → MvPowerSeries σ B,
      CoeffIn (maximalIdeal B) (Ψ w) → ∀ i, CoeffIn (maximalIdeal B) (w i) := by
    intro w hw i
    rw [coeffIn_maximalIdeal_iff] at hw ⊢
    rw [hΨ, map_sum] at hw
    simp only [map_mul, map_subst ha] at hw
    exact congrFun (hres (fun i => map (residue B) (w i)) hw) i
  have main : ∀ t : ℕ, ∀ i, CoeffIn (maximalIdeal B ^ t) (c i) := by
    intro t
    induction t with
    | zero => intro i; rw [pow_zero, Ideal.one_eq_top]; exact CoeffIn.top _
    | succ t ih =>
      obtain ⟨s, g, hgI, hgind⟩ := exists_minimal_generators (maximalIdeal B ^ t)
      have hgl : ∀ l, g l ∈ maximalIdeal B ^ t := fun l => by
        rw [← hgI]; exact Ideal.subset_span ⟨l, rfl⟩
      have hdec : ∀ (i : ι) (d : σ →₀ ℕ), ∃ γ : Fin s → B, ∑ l, γ l • g l = coeff d (c i) := by
        intro i d
        have h := ih i d
        rw [← hgI] at h
        exact (Submodule.mem_span_range_iff_exists_fun B).mp h
      choose γ hγ using hdec
      let w : Fin s → ι → MvPowerSeries σ B := fun l i => fun d => γ i d l
      have hw : ∀ l i (d : σ →₀ ℕ), coeff d (w l i) = γ i d l := fun _ _ _ => rfl
      have hcw : c = ∑ l, g l • w l := by
        funext i; ext d
        rw [← hγ i d, Finset.sum_apply, map_sum]
        simp only [Pi.smul_apply, map_smul, hw, smul_eq_mul, mul_comm]
      have hsum : ∑ l, g l • Ψ (w l) = 0 := by
        have : Ψ c = 0 := by rw [hΨ]; exact hc
        rw [← this, hcw, map_sum]
        simp only [map_smul]
      have hwm : ∀ l, CoeffIn (maximalIdeal B) (Ψ (w l)) := by
        intro l d
        have h1 : ∑ l, coeff d (Ψ (w l)) * g l ∈ maximalIdeal B * maximalIdeal B ^ t := by
          have h2 : ∑ l, coeff d (Ψ (w l)) * g l = coeff d (∑ l, g l • Ψ (w l)) := by
            rw [map_sum]
            simp only [map_smul, smul_eq_mul, mul_comm]
          rw [h2, hsum, map_zero]
          exact Ideal.zero_mem _
        exact hgind _ h1 l
      intro i
      rw [congrFun hcw i, Finset.sum_apply, pow_succ]
      refine CoeffIn.sum _ fun l _ => ?_
      rw [Pi.smul_apply]
      exact CoeffIn.smul_mem (hgl l) (hΨres _ (hwm l) i)
  funext i
  exact eq_zero_of_forall_coeffIn_pow _ fun t => main t i

end SumSubst

end Devissage

section FieldCase

private theorem eq_zero_of_sum_subst_mul_eq_zero_field {k : Type u} [Field k] {n d : ℕ}
    (g : Fin n → MvPowerSeries (Fin n) k) (hg : ∀ i, constantCoeff (g i) = 0)
    (e : Fin d → MvPowerSeries (Fin n) k)
    (β : Module.Basis (Fin d) k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range g)))
    (hβ : ∀ j, β j = Ideal.Quotient.mk (Ideal.span (Set.range g)) (e j))
    (w : Fin d → MvPowerSeries (Fin n) k) (hw : ∑ j, subst g (w j) * e j = 0) : w = 0 := by
  classical
  have : Module.Finite k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range g)) :=
      Module.Finite.of_basis β
  obtain ⟨hfinT, -, b₀, hb₀⟩ :=
    finite_flat_exists_basis_substAlgHom_of_finite_quotient g hg inferInstance
  have hgs : HasSubst g := hasSubst_of_constantCoeff_zero hg
  let φa : MvPowerSeries (Fin n) k →ₐ[k] MvPowerSeries (Fin n) k := substAlgHom (R := k) hgs
  let φ : MvPowerSeries (Fin n) k →+* MvPowerSeries (Fin n) k := φa.toRingHom
  have hφ : ∀ x, φ x = subst g x := fun x => by
    change φa x = _
    rw [coe_substAlgHom]
  have hφC : ∀ c : k, φ (C c) = C c := fun c => by
    change φa (C c) = _
    rw [c_eq_algebraMap, AlgHom.commutes]
  let S := MvPowerSeries (Fin n) k
  let T := Tgt φ
  let ε : T ≃+* MvPowerSeries (Fin n) k := ofT φ
  have hε_smul : ∀ (r : S) (t : T), ε (r • t) = φ r * ε t := ofT_smul φ
  have hε_symm : ∀ x, ε (ε.symm x) = x := fun x => rfl
  have hfinM : Module.Finite S T := hfinT
  have hr : Module.finrank k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range g)) = d := by
    rw [Module.finrank_eq_card_basis β, Fintype.card_fin]
  let L₀ : (Fin (Module.finrank k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range g))) → S) →ₗ[S]
      T :=
    Fintype.linearCombination S (fun i => ε.symm (b₀ i))
  have hL₀ : ∀ c, ε (L₀ c) = ∑ i, subst g (c i) * b₀ i := by
    intro c
    rw [Fintype.linearCombination_apply, map_sum]
    simp only [hε_smul, hε_symm, hφ]
  have hL₀bij : Function.Bijective L₀ := by
    constructor
    · intro c c' h
      exact (hb₀ (ε (L₀ c))).unique (hL₀ c) (by rw [h, hL₀])
    · intro t
      obtain ⟨c, hc, -⟩ := hb₀ (ε t)
      exact ⟨c, ε.injective (by rw [hL₀, ← hc])⟩
  let E₀ : (Fin (Module.finrank k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range g))) → S) ≃ₗ[S]
      T :=
    LinearEquiv.ofBijective L₀ hL₀bij
  let L : (Fin d → S) →ₗ[S] T := Fintype.linearCombination S (fun j => ε.symm (e j))
  have hL : ∀ w, ε (L w) = ∑ j, subst g (w j) * e j := by
    intro w
    rw [Fintype.linearCombination_apply, map_sum]
    simp only [hε_smul, hε_symm, hφ]
  have hX : ∀ i : Fin n, (X i : S) ∈ maximalIdeal S := fun i => by
    rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff, constantCoeff_X,
        isUnit_iff_ne_zero]
    exact fun h => h rfl
  have hgm : ∀ y ∈ Ideal.span (Set.range g), ε.symm y ∈ (maximalIdeal S • ⊤ : Submodule S T) := by
    intro y hy
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
    have hle : Ideal.map (ε.symm : MvPowerSeries (Fin n) k →+* T) (Ideal.span (Set.range g)) ≤
        Ideal.map (algebraMap S T) (maximalIdeal S) := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      have : (ε.symm : MvPowerSeries (Fin n) k →+* T) (g i) = algebraMap S T (X i) := by
        apply ε.injective
        change ε (ε.symm (g i)) = ε (algebraMap S T (X i))
        rw [hε_symm, ofT_algebraMap, hφ, subst_X hgs]
      rw [this]
      exact Ideal.mem_map_of_mem _ (hX i)
    exact hle (Ideal.mem_map_of_mem _ hy)
  have hspan : (⊤ : Submodule S T) ≤ Submodule.span S (Set.range fun j => ε.symm (e j)) := by
    refine Submodule.le_of_le_smul_of_le_jacobson Module.Finite.fg_top
      (ringJacobson_eq_maximalIdeal _).ge ?_
    rintro t -
    let x : MvPowerSeries (Fin n) k := ε t
    have hx : Ideal.Quotient.mk (Ideal.span (Set.range g)) x =
        Ideal.Quotient.mk (Ideal.span (Set.range g)) (∑ j,
            C (β.repr (Ideal.Quotient.mk _ x) j) * e j) := by
      conv_lhs => rw [← β.sum_repr (Ideal.Quotient.mk (Ideal.span (Set.range g)) x)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hβ, ← smul_eq_C_mul, ← Ideal.Quotient.mkₐ_eq_mk k, map_smul]
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hx
    have ht : t = (∑ j, (C (β.repr (Ideal.Quotient.mk _ x) j) : S) • ε.symm (e j)) +
        ε.symm (x - ∑ j, C (β.repr (Ideal.Quotient.mk _ x) j) * e j) := by
      apply ε.injective
      rw [map_add, map_sum, hε_symm]
      simp only [hε_smul, hε_symm, hφC]
      show ε t = _
      ring
    rw [ht]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))) (Submodule.mem_sup_right (hgm _ hx))
  have hLsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact top_le_iff.mp hspan
  let G : T ≃ₗ[S] (Fin d → S) :=
    E₀.symm.trans (LinearEquiv.funCongrLeft S S (finCongr hr).symm)
  have hF : Function.Injective (G.toLinearMap.comp L) :=
    OrzechProperty.injective_of_surjective_endomorphism _ (G.surjective.comp hLsurj)
  have hLinj : Function.Injective L := by
    rw [LinearMap.coe_comp] at hF
    exact hF.of_comp
  have hLw : L w = 0 := ε.injective (by rw [hL, hw, map_zero])
  exact hLinj (hLw.trans (map_zero L).symm)

end FieldCase

-- Uniqueness: if the residues of the `b j` form a basis of `k⟦X⟧ ⧸ (ρ)` over the residue field
-- `k`, the coefficients of `∑ j, subst ρ (c j) * b j` are unique.
private theorem eq_of_sum_subst_mul_eq_of_basis_quotient_map_residue
    {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] {n d : ℕ}
    (ρ : Fin n → MvPowerSeries (Fin n) B) (hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0)
    (b : Fin d → MvPowerSeries (Fin n) B)
    (β : Module.Basis (Fin d) (IsLocalRing.ResidueField B)
      (MvPowerSeries (Fin n) (IsLocalRing.ResidueField B) ⧸
        Ideal.span (Set.range fun i => MvPowerSeries.map (IsLocalRing.residue B) (ρ i))))
    (hβ : ∀ j, β j = Ideal.Quotient.mk
      (Ideal.span (Set.range fun i => MvPowerSeries.map (IsLocalRing.residue B) (ρ i)))
      (MvPowerSeries.map (IsLocalRing.residue B) (b j)))
    (c c' : Fin d → MvPowerSeries (Fin n) B)
    (h : ∑ j, MvPowerSeries.subst ρ (c j) * b j = ∑ j, MvPowerSeries.subst ρ (c' j) * b j) :
        c = c' := by
  have hρ : MvPowerSeries.HasSubst ρ := MvPowerSeries.hasSubst_of_constantCoeff_zero hρ0
  have h0 : ∑ j, MvPowerSeries.subst ρ ((c - c') j) * b j = 0 := by
    simp only [Pi.sub_apply, MvPowerSeries.subst_sub hρ, sub_mul, Finset.sum_sub_distrib, h,
        sub_self]
  have hres : ∀ w : Fin d → MvPowerSeries (Fin n) (ResidueField B),
      ∑ i, subst (fun s => map (residue B) (ρ s)) (w i) * map (residue B) (b i) = 0 → w = 0 :=
    fun w hw => eq_zero_of_sum_subst_mul_eq_zero_field (fun i => map (residue B) (ρ i))
      (fun i => by rw [constantCoeff_map, hρ0, map_zero]) (fun j => map (residue B) (b j)) β hβ w hw
  exact sub_eq_zero.mp (eq_zero_of_sum_subst_mul_eq_zero_of_residue hρ0 b hres (c - c') h0)

end Residue

-- Existence: if the classes of the `b j` span `B⟦X⟧ ⧸ (ρ)` over `B`, every power series is
-- `∑ j, subst ρ (c j) * b j`.
private theorem exists_eq_sum_subst_mul_of_span_quotient_eq_top
    {B : Type u} [CommRing B] {n d : ℕ} (ρ : Fin n → MvPowerSeries (Fin n) B)
    (hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0)
    (b : Fin d → MvPowerSeries (Fin n) B)
    (hgen : Submodule.span B (Set.range (fun j => Ideal.Quotient.mk (Ideal.span (Set.range ρ))
        (b j))) = ⊤)
    (f : MvPowerSeries (Fin n) B) :
    ∃ c : Fin d → MvPowerSeries (Fin n) B, f = ∑ j, MvPowerSeries.subst ρ (c j) * b j := by
  classical
  set I : Ideal (MvPowerSeries (Fin n) B) := Ideal.span
      (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) B)) with hI
  have hsub := MvPowerSeries.hasSubst_of_constantCoeff_zero hρ0
  let φ : MvPowerSeries (Fin n) B →+* MvPowerSeries (Fin n) B :=
    (MvPowerSeries.substAlgHom hsub : MvPowerSeries (Fin n) B →ₐ[B] _).toRingHom
  have hφ : ∀ g, φ g = MvPowerSeries.subst ρ g := fun g => by
    change (MvPowerSeries.substAlgHom hsub) g = _
    rw [← MvPowerSeries.coe_substAlgHom hsub]
  let e : Tgt φ ≃+* MvPowerSeries (Fin n) B := ofT φ
  have he_smul : ∀ (r : MvPowerSeries (Fin n) B) (t : Tgt φ),
      e (r • t) = MvPowerSeries.subst ρ r * e t := fun r t => by
    rw [← hφ]
    exact ofT_smul φ r t
  have hmapI : ∀ k : ℕ, ∀ c ∈ I ^ k, MvPowerSeries.subst ρ c ∈ I ^ k := by
    intro k c hc
    have h1 : I.map φ ≤ I := by
      rw [hI, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      rw [hφ, MvPowerSeries.subst_X hsub]
      exact (span_range_X_eq_ker_constantCoeff n).ge (RingHom.mem_ker.mpr (hρ0 i))
    have h2 : (I ^ k).map φ ≤ I ^ k := by rw [Ideal.map_pow]; exact Ideal.pow_right_mono h1 k
    have h3 := h2 (Ideal.mem_map_of_mem φ hc)
    rwa [hφ] at h3
  have hsmul_le : ∀ (k : ℕ) (z : Tgt φ),
      z ∈ I ^ k • (⊤ : Submodule (MvPowerSeries (Fin n) B) (Tgt φ)) → e z ∈ I ^ k := by
    intro k z hz
    induction hz using Submodule.smul_induction_on' with
    | smul r hr y _ =>
      rw [he_smul]
      exact Ideal.mul_mem_right _ _ (hmapI k r hr)
    | add x hx y hy ihx ihy =>
      rw [map_add]
      exact Ideal.add_mem _ ihx ihy
  have : IsHausdorff I (Tgt φ) := ⟨fun z hz => by
    refine e.injective ((IsHausdorff.haus' (I := I) (e z) fun N => ?_).trans (map_zero e).symm)
    have h := hz N
    rw [SModEq.sub_mem, sub_zero] at h
    rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
    exact hsmul_le N z h⟩
  have hρI : ∀ w ∈ Ideal.span (Set.range ρ),
      e.symm w ∈ I • (⊤ : Submodule (MvPowerSeries (Fin n) B) (Tgt φ)) := by
    intro w hw
    obtain ⟨g, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hw
    rw [map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : e.symm (g i * ρ i) =
        (MvPowerSeries.X i : MvPowerSeries (Fin n) B) • e.symm (g i) := by
      apply e.injective
      rw [he_smul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
        MvPowerSeries.subst_X hsub, mul_comm]
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.subset_span ⟨i, rfl⟩) Submodule.mem_top
  have hsC : ∀ c : B, MvPowerSeries.subst ρ (MvPowerSeries.C c : MvPowerSeries (Fin n) B) =
      MvPowerSeries.C c := fun c => by
    rw [← MvPowerSeries.coe_substAlgHom hsub, MvPowerSeries.c_eq_algebraMap, AlgHom.commutes]
  have hgen' : ∀ z : Tgt φ, ∃ a : Fin d → MvPowerSeries (Fin n) B,
      z - ∑ j, a j • e.symm (b j) ∈ I • (⊤ : Submodule (MvPowerSeries (Fin n) B) (Tgt φ)) := by
    intro z
    have hmem : Ideal.Quotient.mk (Ideal.span (Set.range ρ)) (e z) ∈ Submodule.span B
        (Set.range fun j => Ideal.Quotient.mk (Ideal.span (Set.range ρ)) (b j)) := by
      rw [hgen]; exact Submodule.mem_top
    obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp hmem
    refine ⟨fun j => (MvPowerSeries.C (β j) : MvPowerSeries (Fin n) B), ?_⟩
    have hdiff : e z - ∑ j, (MvPowerSeries.C (β j) : MvPowerSeries (Fin n) B) *
        b j ∈ Ideal.span (Set.range ρ) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sum, sub_eq_zero, ← hβ]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hj : Ideal.Quotient.mkₐ B (Ideal.span (Set.range ρ))
          ((MvPowerSeries.C (β j) : MvPowerSeries (Fin n) B) * b j) =
          β j • Ideal.Quotient.mkₐ B (Ideal.span (Set.range ρ)) (b j) := by
        rw [← MvPowerSeries.smul_eq_C_mul, map_smul]
      simpa only [Ideal.Quotient.mkₐ_eq_mk] using hj.symm
    have : z - ∑ j, (MvPowerSeries.C (β j) : MvPowerSeries (Fin n) B) • e.symm (b j) =
        e.symm (e z - ∑ j, (MvPowerSeries.C (β j) : MvPowerSeries (Fin n) B) * b j) := by
      apply e.injective
      simp only [map_sub, map_sum, he_smul, RingEquiv.apply_symm_apply, hsC]
    rw [this]
    exact hρI _ hdiff
  obtain ⟨c, hc⟩ := exists_eq_sum_smul I (fun j => e.symm (b j)) hgen' (e.symm f)
  refine ⟨c, ?_⟩
  have := congrArg e hc
  simpa only [map_sum, he_smul, RingEquiv.apply_symm_apply] using this

end MvPowerSeries.SubstBasisAux

open scoped TensorProduct

namespace MvPowerSeries

/-- Let `B` be a Noetherian local ring with residue field `k`, and let
`ρ : Fin n → B⟦X⟧` have zero constant coefficients, with some power of every variable
in the ideal `(ρ)` and `B⟦X⟧ ⧸ (ρ)` finite over `B`. If the images of `b₁, …, b_d`
form a `k`-basis of `k ⊗[B] (B⟦X⟧ ⧸ (ρ))`, then every power series `f` is uniquely
`∑ⱼ subst ρ (cⱼ) * bⱼ`. -/
public theorem existsUnique_eq_sum_subst_mul_of_basis_residueField_tensor_quotient
    {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] {n d : ℕ}
    (ρ : Fin n → MvPowerSeries (Fin n) B)
    (hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0)
    (hN : ∃ N : ℕ, ∀ i : Fin n,
      (MvPowerSeries.X i : MvPowerSeries (Fin n) B) ^ N ∈ Ideal.span (Set.range ρ))
    (hfin : Module.Finite B (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ)))
    (b : Fin d → MvPowerSeries (Fin n) B)
    (β : Module.Basis (Fin d) (IsLocalRing.ResidueField B)
      (TensorProduct B (IsLocalRing.ResidueField B)
        (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ))))
    (hb : ∀ j, β j = TensorProduct.tmul B (1 : IsLocalRing.ResidueField B)
      (Ideal.Quotient.mk (Ideal.span (Set.range ρ)) (b j)))
    (f : MvPowerSeries (Fin n) B) :
    ∃! c : Fin d → MvPowerSeries (Fin n) B, f = ∑ j, MvPowerSeries.subst ρ (c j) * b j := by
  classical
  have := hfin
  have hgen : Submodule.span B
      (Set.range (fun j => Ideal.Quotient.mk (Ideal.span (Set.range ρ)) (b j))) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis (R := B)
      (f := fun j => Ideal.Quotient.mk (Ideal.span (Set.range ρ)) (b j)) β (fun j => (hb j).symm)
  obtain ⟨e, he⟩ := MvPowerSeries.exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem
    (S := IsLocalRing.ResidueField B) ρ hN
  let β' : Module.Basis (Fin d) (IsLocalRing.ResidueField B)
      (MvPowerSeries (Fin n) (IsLocalRing.ResidueField B) ⧸
        Ideal.span (Set.range fun i => MvPowerSeries.map (IsLocalRing.residue B) (ρ i))) :=
    β.map e.toLinearEquiv
  have hβ' : ∀ j, β' j = Ideal.Quotient.mk
      (Ideal.span (Set.range fun i => MvPowerSeries.map (IsLocalRing.residue B) (ρ i)))
      (MvPowerSeries.map (IsLocalRing.residue B) (b j)) := by
    intro j
    change e.toLinearEquiv (β j) = _
    rw [hb j, AlgEquiv.toLinearEquiv_apply, he, one_smul]
    rfl
  obtain ⟨c, hc⟩ := SubstBasisAux.exists_eq_sum_subst_mul_of_span_quotient_eq_top ρ hρ0 b hgen f
  refine ⟨c, hc, fun c' hc' => ?_⟩
  exact SubstBasisAux.eq_of_sum_subst_mul_eq_of_basis_quotient_map_residue ρ hρ0 b β' hβ' c' c
    (hc' ▸ hc ▸ rfl)

/-- Let `B` be a Noetherian local ring and let `ρ : Fin n → B⟦X⟧` have zero constant
coefficients, with some power of every variable in the ideal `(ρ)` and `B⟦X⟧ ⧸ (ρ)`
finite over `B`. Then there are finitely many power series `b₁, …, b_d` such that
every power series `f` is uniquely `∑ⱼ subst ρ (cⱼ) * bⱼ`. -/
public theorem exists_basis_subst_of_finite_quotient_of_isLocalRing
    {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] {n : ℕ}
    (ρ : Fin n → MvPowerSeries (Fin n) B)
    (hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0)
    (hN : ∃ N : ℕ, ∀ i : Fin n,
      (MvPowerSeries.X i : MvPowerSeries (Fin n) B) ^ N ∈ Ideal.span (Set.range ρ))
    (hfin : Module.Finite B (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ))) :
    ∃ (d : ℕ) (b : Fin d → MvPowerSeries (Fin n) B),
      ∀ f : MvPowerSeries (Fin n) B,
        ∃! c : Fin d → MvPowerSeries (Fin n) B, f = ∑ j, MvPowerSeries.subst ρ (c j) * b j := by
  classical
  let C := MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ)
  let k := IsLocalRing.ResidueField B
  have : Module.Finite B C := hfin
  have : Module.Free k (k ⊗[B] C) := Module.Free.of_divisionRing k (k ⊗[B] C)
  have : Module.Finite k (k ⊗[B] C) := Module.Finite.base_change B k C
  let β := Module.finBasis k (k ⊗[B] C)
  have hs : Function.Surjective (TensorProduct.mk B k C 1) := by
    rw [← LinearMap.range_eq_top, ← Submodule.map_top]
    exact IsLocalRing.map_tensorProduct_mk_eq_top.2 rfl
  choose x hx using fun j => hs (β j)
  choose b hb using fun j => Ideal.Quotient.mk_surjective (x j)
  refine ⟨Module.finrank k (k ⊗[B] C), b, fun f => ?_⟩
  exact existsUnique_eq_sum_subst_mul_of_basis_residueField_tensor_quotient ρ hρ0 hN hfin b β
    (fun j => by rw [hb j]; exact (hx j).symm) f

end MvPowerSeries
