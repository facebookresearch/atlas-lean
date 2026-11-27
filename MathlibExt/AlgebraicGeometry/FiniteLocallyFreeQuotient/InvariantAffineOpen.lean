/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finiteLocallyFree_equivalenceRelation.lean`
and
`P2M/Sol/S_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finiteLocallyFree_equivalenceRelation.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-!
# Invariant affine neighborhoods for finite locally free equivalence relations

If the equivalence class of a point lies in an affine open, then the point has an
affine open neighborhood inside it that is saturated for the relation.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme

namespace InvariantAffineOpenAux

variable {X R : Scheme.{u}} (s t : R ⟶ X)

private def cls (w : X) : Set X := {w' | ∃ r : R, s r = w ∧ t r = w'}

section points

variable (hequiv : ∀ T : Scheme.{u},
  _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
include hequiv

private theorem mem_cls_self (w : X) : w ∈ cls s t w := by
  obtain ⟨e, hes, het⟩ := (hequiv X).refl (𝟙 X)
  refine ⟨e w, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, hes]; rfl
  · rw [← Scheme.Hom.comp_apply, het]; rfl

private theorem exists_inv (r : R) : ∃ r' : R, s r' = t r ∧ t r' = s r := by
  obtain ⟨ι, hιs, hιt⟩ := (hequiv R).symm ⟨𝟙 R, Category.id_comp s, Category.id_comp t⟩
  exact ⟨ι r, by rw [← Scheme.Hom.comp_apply, hιs], by rw [← Scheme.Hom.comp_apply, hιt]⟩

private theorem cls_symm {w w' : X} (h : w' ∈ cls s t w) : w ∈ cls s t w' := by
  obtain ⟨r, rfl, rfl⟩ := h
  obtain ⟨r', h₁, h₂⟩ := exists_inv s t hequiv r
  exact ⟨r', h₁, h₂⟩

private theorem cls_trans {w w' w'' : X} (h : w' ∈ cls s t w) (h' : w'' ∈ cls s t w') :
    w'' ∈ cls s t w := by
  obtain ⟨r₁, rfl, rfl⟩ := h
  obtain ⟨r₂, h₂, rfl⟩ := h'
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback r₁ r₂ h₂.symm
  obtain ⟨c, hcs, hct⟩ := (hequiv (pullback t s)).trans
    (⟨pullback.fst t s, rfl, rfl⟩ : ∃ φ : pullback t s ⟶ R,
      φ ≫ s = pullback.fst t s ≫ s ∧ φ ≫ t = pullback.fst t s ≫ t)
    (⟨pullback.snd t s, pullback.condition.symm, rfl⟩ : ∃ φ : pullback t s ⟶ R,
      φ ≫ s = pullback.fst t s ≫ t ∧ φ ≫ t = pullback.snd t s ≫ t)
  refine ⟨c z, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, hcs, Scheme.Hom.comp_apply, hz₁]
  · rw [← Scheme.Hom.comp_apply, hct, Scheme.Hom.comp_apply, hz₂]

private theorem cls_eq_of_mem {w w' : X} (h : w' ∈ cls s t w) : cls s t w' = cls s t w :=
  Set.ext fun _ => ⟨fun h'' => cls_trans s t hequiv h h'',
    fun h'' => cls_trans s t hequiv (cls_symm s t hequiv h) h''⟩

end points

section S1

variable [IsFinite t] (U : X.Opens)

private def W' : X.Opens :=
  ⟨(t.base '' ((s ⁻¹ᵁ U ⊓ t ⁻¹ᵁ U : R.Opens) : Set R)ᶜ)ᶜ, by
    rw [isOpen_compl_iff]
    exact t.isClosedMap _ (isClosed_compl_iff.mpr (Opens.isOpen _))⟩

private theorem mem_W'_iff (w : X) : w ∈ W' s t U ↔ ∀ z : R, t z = w → s z ∈ U ∧ t z ∈ U := by
  change w ∈ (t.base '' _)ᶜ ↔ _
  simp only [Set.mem_compl_iff, Set.mem_image, not_exists, not_and, SetLike.mem_coe]
  constructor
  · intro h z hz
    by_contra hc
    exact h z (fun hm => hc hm) hz
  · intro h z hz hzw
    exact hz (h z hzw)

variable (hequiv : ∀ T : Scheme.{u},
  _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
include hequiv

private theorem W'_le : W' s t U ≤ U := by
  intro w hw
  have hw' : w ∈ W' s t U := hw
  rw [mem_W'_iff] at hw'
  obtain ⟨e, hes, het⟩ := (hequiv X).refl (𝟙 X)
  have h1 : s (e w) = w := by rw [← Scheme.Hom.comp_apply, hes]; rfl
  have h2 : t (e w) = w := by rw [← Scheme.Hom.comp_apply, het]; rfl
  simpa [h2] using (hw' (e w) h2).2

private theorem cls_subset_W' {x : X} (hx : cls s t x ⊆ (U : Set X)) :
    cls s t x ⊆ (W' s t U : Set X) := by
  intro w' hw'
  change w' ∈ W' s t U
  rw [mem_W'_iff]
  intro z hz
  refine ⟨hx ?_, hx (hz ▸ hw')⟩
  have : s z ∈ cls s t w' := cls_symm s t hequiv ⟨z, rfl, hz⟩
  rwa [cls_eq_of_mem s t hequiv hw'] at this

private theorem preimage_W'_le : s ⁻¹ᵁ W' s t U ≤ t ⁻¹ᵁ U := by
  intro r hr
  change s r ∈ W' s t U at hr
  rw [mem_W'_iff] at hr
  obtain ⟨r', h₁, h₂⟩ := exists_inv s t hequiv r
  have := (hr r' h₂).1
  rwa [h₁] at this

end S1

section S4

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
  [Module.Projective A B]

private theorem exists_norm : ∃ N : B → A, ∀ (b : B) (p : PrimeSpectrum A),
    N b ∉ p.asIdeal ↔ ∀ q : PrimeSpectrum B, q.comap (algebraMap A B) = p → b ∉ q.asIdeal := by
  classical
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' A B
  obtain ⟨ι, hι⟩ := Module.projective_lifting_property π (LinearMap.id) hπ
  let ψ : B → Module.End A (Fin n → A) := fun b =>
    ι ∘ₗ LinearMap.mulLeft A b ∘ₗ π + (LinearMap.id - ι ∘ₗ π)
  refine ⟨fun b => LinearMap.det (ψ b), fun b p => ?_⟩
  let κ := p.asIdeal.ResidueField
  have hker : ∀ a : A, algebraMap A κ a = 0 ↔ a ∈ p.asIdeal := fun a => by
    rw [Ideal.algebraMap_residueField_eq_zero]
  have key : ∀ {K : Type u} [CommRing K] [Algebra A K],
      Function.Bijective ((ψ b).baseChange K) ↔
        Function.Bijective ((LinearMap.mulLeft A b).baseChange K) := by
    intro K _ _
    set πK := π.baseChange K
    set ιK := ι.baseChange K
    set mK := (LinearMap.mulLeft A b).baseChange K
    have hιK : πK ∘ₗ ιK = LinearMap.id := by
      rw [← LinearMap.baseChange_comp, hι, LinearMap.baseChange_id]
    have hψK : (ψ b).baseChange K = ιK ∘ₗ mK ∘ₗ πK + (LinearMap.id - ιK ∘ₗ πK) := by
      simp only [ψ, LinearMap.baseChange_add, LinearMap.baseChange_sub, LinearMap.baseChange_comp,
        LinearMap.baseChange_id, πK, ιK, mK]
    rw [hψK]
    have hιK' : ∀ y, πK (ιK y) = y := fun y => LinearMap.congr_fun hιK y
    have hιinj : Function.Injective ιK := Function.LeftInverse.injective hιK'
    set Ψ := ιK ∘ₗ mK ∘ₗ πK + (LinearMap.id - ιK ∘ₗ πK) with hΨ
    have Ψι : ∀ y, Ψ (ιK y) = ιK (mK y) := fun y => by
      simp [hΨ, hιK']
    have Ψker : ∀ v, πK v = 0 → Ψ v = v := fun v hv => by
      simp [hΨ, hv]
    have πΨ : ∀ v, πK (Ψ v) = mK (πK v) := fun v => by
      simp [hΨ, hιK', map_sub]
    constructor
    · intro hΨb
      constructor
      · intro y₁ y₂ h
        apply hιinj
        apply hΨb.1
        rw [Ψι, Ψι, h]
      · intro y
        obtain ⟨v, hv⟩ := hΨb.2 (ιK y)
        refine ⟨πK v, ?_⟩
        rw [← πΨ, hv, hιK']
    · intro hm
      constructor
      · intro v₁ v₂ h
        have h1 : mK (πK v₁) = mK (πK v₂) := by rw [← πΨ, ← πΨ, h]
        have h2 : πK v₁ = πK v₂ := hm.1 h1
        have h3 : Ψ (v₁ - ιK (πK v₁)) = v₁ - ιK (πK v₁) := Ψker _ (by simp [hιK'])
        have h4 : Ψ (v₂ - ιK (πK v₂)) = v₂ - ιK (πK v₂) := Ψker _ (by simp [hιK'])
        have h5 : Ψ (v₁ - ιK (πK v₁)) = Ψ (v₂ - ιK (πK v₂)) := by
          rw [map_sub, map_sub, h, Ψι, Ψι, h2]
        rw [h3, h4, h2] at h5
        simpa using h5
      · intro v
        obtain ⟨y, hy⟩ := hm.2 (πK v)
        refine ⟨ιK y + (v - ιK (πK v)), ?_⟩
        rw [map_add, Ψι, Ψker _ (by simp [hιK']), hy]
        abel
  have h1 : LinearMap.det (ψ b) ∉ p.asIdeal ↔ Function.Bijective ((ψ b).baseChange κ) := by
    rw [← hker, ← LinearMap.det_baseChange, ← Module.End.isUnit_iff,
      LinearMap.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  rw [h1, key]
  have h2 : Function.Bijective ((LinearMap.mulLeft A b).baseChange κ) ↔
      IsUnit ((1 : κ) ⊗ₜ[A] b : κ ⊗[A] B) := by
    have hm : ((LinearMap.mulLeft A b).baseChange κ : κ ⊗[A] B → κ ⊗[A] B) =
        fun z => ((1 : κ) ⊗ₜ[A] b) * z := by
      funext z
      induction z using TensorProduct.inductionOn with
      | tmul x y => simp [Algebra.TensorProduct.tmul_mul_tmul]
      | add z₁ z₂ h₁ h₂ => simp only [map_add, mul_add, h₁, h₂]
    rw [hm]
    constructor
    · intro hb
      obtain ⟨c, hc⟩ := hb.2 1
      exact isUnit_iff_exists_inv.mpr ⟨c, hc⟩
    · intro hu
      exact ⟨fun z₁ z₂ h => hu.mul_left_cancel h, fun z => ⟨hu.unit⁻¹ * z, by simp [← mul_assoc]⟩⟩
  rw [h2]
  constructor
  · intro hu q hq hbq
    let Q : PrimeSpectrum (p.asIdeal.Fiber B) := PrimeSpectrum.preimageEquivFiber A B p ⟨q, hq⟩
    have hq' : (PrimeSpectrum.preimageEquivFiber A B p).symm Q = ⟨q, hq⟩ :=
      Equiv.symm_apply_apply _ _
    have hmem : ((1 : κ) ⊗ₜ[A] b : κ ⊗[A] B) ∈ Q.asIdeal := by
      have : q = Q.comap Algebra.TensorProduct.includeRight.toRingHom := by
        have := congrArg Subtype.val hq'
        simpa using this.symm
      rw [this] at hbq
      exact hbq
    exact Q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)
  · intro hall
    by_contra hnu
    obtain ⟨M, hM, hbM⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hnu)
    let Q : PrimeSpectrum (p.asIdeal.Fiber B) := ⟨M, hM.isPrime⟩
    let q := (PrimeSpectrum.preimageEquivFiber A B p).symm Q
    apply hall q.1 q.2
    change b ∈ (Q.comap Algebra.TensorProduct.includeRight.toRingHom).asIdeal
    exact hbM

end S4

private theorem exists_basicOpen_of_finite {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (F : Set X) (hF : F.Finite) (V : X.Opens) (hFV : F ⊆ (V : Set X)) (hFU : F ⊆ (U : Set X)) :
    ∃ f : Γ(X, U), F ⊆ (X.basicOpen f : Set X) ∧ X.basicOpen f ≤ V := by
  classical
  by_cases hne : F.Nonempty
  swap
  · refine ⟨0, ?_, ?_⟩
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]; exact Set.empty_subset _
    · simp
  obtain ⟨w₀, hw₀⟩ := hne
  set φ := hU.fromSpec with hφ
  let C : Set (PrimeSpectrum Γ(X, U)) := φ.base ⁻¹' ((V : Set X)ᶜ)
  let I : Ideal Γ(X, U) := PrimeSpectrum.vanishingIdeal C
  let P : F → PrimeSpectrum Γ(X, U) := fun w => hU.primeIdealOf ⟨w.1, hFU w.2⟩
  have hPφ : ∀ w : F, φ (P w) = w.1 := fun w => hU.fromSpec_primeIdealOf ⟨w.1, hFU w.2⟩
  have hC : IsClosed C := IsClosed.preimage φ.base.hom.continuous V.isOpen.isClosed_compl
  have hPI : ∀ w : F, ¬ I ≤ (P w).asIdeal := fun w hle => by
    have hmem : P w ∈ PrimeSpectrum.zeroLocus (I : Set Γ(X, U)) := by
      rwa [PrimeSpectrum.mem_zeroLocus]
    have hmem' : P w ∈ C := by
      rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hC.closure_eq] at hmem
      exact hmem
    apply hmem'
    rw [hPφ w]
    exact hFV w.2
  have : Fintype F := hF.fintype
  have havoid : ¬ ((I : Set Γ(X, U)) ⊆ ⋃ w ∈ (↑(Finset.univ : Finset F) : Set F),
      ((fun w : F => (P w).asIdeal) w : Set Γ(X, U))) := by
    rw [Ideal.subset_union_prime (⟨w₀, hw₀⟩ : F) ⟨w₀, hw₀⟩ (fun w _ _ _ => (P w).isPrime)]
    rintro ⟨w, -, hw⟩
    exact hPI w hw
  rw [Set.not_subset] at havoid
  obtain ⟨g, hgI, hg⟩ := havoid
  have hg' : ∀ w : F, g ∉ (P w).asIdeal := fun w h =>
    hg (Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_univ w)) h)
  refine ⟨g, ?_, ?_⟩
  · intro w hw
    have h1 : P ⟨w, hw⟩ ∈ (PrimeSpectrum.basicOpen g : Set _) :=
      (PrimeSpectrum.mem_basicOpen g (P ⟨w, hw⟩)).mpr (hg' ⟨w, hw⟩)
    have h2 : P ⟨w, hw⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen g := by
      rw [hU.fromSpec_preimage_basicOpen]; exact h1
    have h3 : φ (P ⟨w, hw⟩) ∈ X.basicOpen g := h2
    rw [hPφ ⟨w, hw⟩] at h3
    exact h3
  · intro w hw
    have hwU : w ∈ U := X.basicOpen_le g hw
    by_contra hwV
    let p := hU.primeIdealOf ⟨w, hwU⟩
    have hp : φ p = w := hU.fromSpec_primeIdealOf ⟨w, hwU⟩
    have hpC : p ∈ C := by
      change φ.base p ∈ (V : Set X)ᶜ
      rw [Set.mem_compl_iff]; exact fun h => hwV (hp ▸ h)
    have hgp : g ∈ p.asIdeal := (PrimeSpectrum.subset_zeroLocus_vanishingIdeal C hpC) hgI
    have hpg : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen g := by
      change φ p ∈ X.basicOpen g
      rw [hp]; exact hw
    rw [hU.fromSpec_preimage_basicOpen] at hpg
    exact (PrimeSpectrum.mem_basicOpen g p).mp hpg hgp

section core

variable {X R : Scheme.{u}} (s t : R ⟶ X) [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]

private theorem mem_basicOpen_iff_notMem {U : X.Opens} (hU : IsAffineOpen U) (g : Γ(X, U)) {w : X}
    (hw : w ∈ U) : w ∈ X.basicOpen g ↔ g ∉ (hU.primeIdealOf ⟨w, hw⟩).asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen]
  have key : hU.primeIdealOf ⟨w, hw⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen g ↔ w ∈ X.basicOpen g := by
    change hU.fromSpec (hU.primeIdealOf ⟨w, hw⟩) ∈ X.basicOpen g ↔ _
    rw [hU.fromSpec_primeIdealOf]
  rw [← key, hU.fromSpec_preimage_basicOpen]
  rfl

private theorem fromSpec_mem {U : X.Opens} (hU : IsAffineOpen U) (p : PrimeSpectrum Γ(X, U)) :
    hU.fromSpec p ∈ U := by
  rw [← SetLike.mem_coe, ← hU.range_fromSpec]
  exact ⟨p, rfl⟩

private theorem primeIdealOf_fromSpec {U : X.Opens} (hU : IsAffineOpen U)
    (p : PrimeSpectrum Γ(X, U)) :
    hU.primeIdealOf ⟨hU.fromSpec p, fromSpec_mem hU p⟩ = p := by
  apply hU.fromSpec.injective
  rw [hU.fromSpec_primeIdealOf]

private theorem exists_basicOpen_forall {U : X.Opens} (f : Γ(X, U))
    (hD : IsAffineOpen (X.basicOpen f))
    (hVU : s ⁻¹ᵁ X.basicOpen f ≤ t ⁻¹ᵁ U) :
    ∃ g : Γ(X, X.basicOpen f), ∀ w : X, w ∈ X.basicOpen f →
      (w ∈ X.basicOpen g ↔ ∀ r : R, s r = w → t r ∈ X.basicOpen f) := by
  set D := X.basicOpen f with hDdef
  have hV : IsAffineOpen (s ⁻¹ᵁ D) := hD.preimage s
  let inst : Algebra Γ(X, D) Γ(R, s ⁻¹ᵁ D) := (s.app D).hom.toAlgebra
  have : Module.Finite Γ(X, D) Γ(R, s ⁻¹ᵁ D) := IsFinite.finite_app s D hD
  have hflat : (s.app D).hom.Flat := by
    rw [Scheme.Hom.app_eq_appLE]
    exact HasRingHomProperty.appLE (P := @Flat) s inferInstance ⟨D, hD⟩ ⟨_, hV⟩ le_rfl
  have hfp : (s.app D).hom.FinitePresentation := by
    rw [Scheme.Hom.app_eq_appLE]
    exact HasRingHomProperty.appLE (P := @LocallyOfFinitePresentation) s inferInstance ⟨D, hD⟩
      ⟨_, hV⟩ le_rfl
  have : Module.Flat Γ(X, D) Γ(R, s ⁻¹ᵁ D) := hflat
  have : Algebra.FinitePresentation Γ(X, D) Γ(R, s ⁻¹ᵁ D) := hfp
  have : Module.FinitePresentation Γ(X, D) Γ(R, s ⁻¹ᵁ D) :=
    Module.FinitePresentation.of_finite_of_finitePresentation _ _
  have : Module.Projective Γ(X, D) Γ(R, s ⁻¹ᵁ D) := Module.Flat.projective_of_finitePresentation
  obtain ⟨N, hN⟩ := exists_norm Γ(X, D) Γ(R, s ⁻¹ᵁ D)
  let b : Γ(R, s ⁻¹ᵁ D) := R.presheaf.map (homOfLE hVU).op (t.app U f)
  refine ⟨N b, fun w hw => ?_⟩
  rw [mem_basicOpen_iff_notMem hD (N b) hw, hN]
  have hb : ∀ (r : R) (hr : r ∈ s ⁻¹ᵁ D), b ∉ (hV.primeIdealOf ⟨r, hr⟩).asIdeal ↔ t r ∈ D :=
    fun r hr => by
      rw [← mem_basicOpen_iff_notMem hV b hr]
      change r ∈ R.basicOpen (R.presheaf.map (homOfLE hVU).op (t.app U f)) ↔ _
      rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
      change r ∈ (s ⁻¹ᵁ D) ⊓ t ⁻¹ᵁ D ↔ t r ∈ D
      simp only [Opens.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨hr, h⟩⟩
  have hcomap : ∀ (r : R) (hr : r ∈ s ⁻¹ᵁ D),
      (hV.primeIdealOf ⟨r, hr⟩).comap (algebraMap Γ(X, D) Γ(R, s ⁻¹ᵁ D)) =
        hD.primeIdealOf ⟨s r, hr⟩ := fun r hr => by
    have := IsAffineOpen.comap_primeIdealOf_appLE (f := s) D hD (s ⁻¹ᵁ D) hV le_rfl hr
    rw [← Scheme.Hom.app_eq_appLE] at this
    exact this
  constructor
  · intro hall r hsr
    have hr : r ∈ s ⁻¹ᵁ D := by change s r ∈ D; rw [hsr]; exact hw
    refine (hb r hr).mp (hall _ ?_)
    rw [hcomap]
    congr 1
    exact Subtype.ext hsr
  · intro hall 𝔮 h𝔮
    let r : R := hV.fromSpec 𝔮
    have hr : r ∈ s ⁻¹ᵁ D := fromSpec_mem hV 𝔮
    have h𝔮r : hV.primeIdealOf ⟨r, hr⟩ = 𝔮 := primeIdealOf_fromSpec hV 𝔮
    have hsr : s r = w := by
      have h1 := hcomap r hr
      rw [h𝔮r, h𝔮] at h1
      have h2 := congrArg hD.fromSpec h1
      rw [hD.fromSpec_primeIdealOf, hD.fromSpec_primeIdealOf] at h2
      exact h2.symm
    rw [← h𝔮r]
    exact (hb r hr).mpr (hall r hsr)

end core

private theorem main [IsFinite s] [Flat s] [LocallyOfFinitePresentation s] [IsFinite t]
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
    {x : X} {U : X.Opens} (hU : IsAffineOpen U) (hx : ∀ r : R, s r = x → t r ∈ U) :
    ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧ W ≤ U ∧ s ⁻¹ᵁ W = t ⁻¹ᵁ W := by
  have hcls : cls s t x ⊆ (U : Set X) := by
    rintro _ ⟨r, hr, rfl⟩; exact hx r hr
  have hfin : (cls s t x).Finite := by
    have : cls s t x = t.base '' (s.base ⁻¹' {x}) := by
      ext w
      simp only [cls, Set.mem_ofPred_eq, Set.mem_image, Set.mem_preimage,
        Set.mem_singleton_iff]
    rw [this]
    exact (s.finite_preimage_singleton x).image _
  obtain ⟨f, hfcls, hfW'⟩ := exists_basicOpen_of_finite hU (cls s t x) hfin (W' s t U)
    (cls_subset_W' s t U hequiv hcls) hcls
  have hD : IsAffineOpen (X.basicOpen f) := hU.basicOpen f
  have hVU : s ⁻¹ᵁ X.basicOpen f ≤ t ⁻¹ᵁ U :=
    le_trans (Scheme.Hom.preimage_mono s hfW') (preimage_W'_le s t U hequiv)
  obtain ⟨g, hg⟩ := exists_basicOpen_forall s t f hD hVU
  refine ⟨X.basicOpen g, hD.basicOpen g, ?_, ?_, ?_⟩
  · have hxD : x ∈ X.basicOpen f := hfcls (mem_cls_self s t hequiv x)
    rw [hg x hxD]
    intro r hr
    exact hfcls ⟨r, hr, rfl⟩
  · exact le_trans (X.basicOpen_le g) (le_trans (X.basicOpen_le f) le_rfl)
  · have hW : ∀ w : X, w ∈ X.basicOpen g ↔ cls s t w ⊆ (X.basicOpen f : Set X) := fun w => by
      constructor
      · intro hw
        have hwD : w ∈ X.basicOpen f := X.basicOpen_le g hw
        rw [hg w hwD] at hw
        rintro _ ⟨r, hr, rfl⟩
        exact hw r hr
      · intro hsub
        have hwD : w ∈ X.basicOpen f := hsub (mem_cls_self s t hequiv w)
        rw [hg w hwD]
        intro r hr
        exact hsub ⟨r, hr, rfl⟩
    ext r
    change s r ∈ X.basicOpen g ↔ t r ∈ X.basicOpen g
    rw [hW, hW, cls_eq_of_mem s t hequiv (⟨r, rfl, rfl⟩ : t r ∈ cls s t (s r))]

end InvariantAffineOpenAux


-- Of `t` only finiteness is used; its flatness and finite presentation are kept from the
-- source statement.
/-- For a finite, flat, finitely presented equivalence relation `s t : R ⟶ X`, if the
equivalence class of `x` lies in the affine open `U`, then `x` has an affine open
neighborhood `W ≤ U` whose preimages under `s` and `t` agree. -/
@[nolint unusedArguments]
public theorem exists_invariant_isAffineOpen_of_finiteLocallyFree_equivalenceRelation
    {X R : Scheme.{u}} (s t : R ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    [IsFinite t] [Flat t] [LocallyOfFinitePresentation t]
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
    {x : X} {U : X.Opens} (hU : IsAffineOpen U) (hx : ∀ r : R, s r = x → t r ∈ U) :
    ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧ W ≤ U ∧ s ⁻¹ᵁ W = t ⁻¹ᵁ W :=
  InvariantAffineOpenAux.main s t hequiv hU hx

end AlgebraicGeometry.Scheme
