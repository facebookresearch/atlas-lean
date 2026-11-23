/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_exists_section_comp_eq_iff_factors_of_universallyClosed_
of_valuationRing.lean`,
`P2M/Sol/S_AlgebraicGeometry_exists_section_comp_eq_iff_factors_of_universallyClosed_
of_valuationRing.lean`,
`Theorems/Thm_AlgebraicGeometry_dense_setOf_exists_section_of_isAlgClosed.lean`,
`P2M/Sol/S_AlgebraicGeometry_dense_setOf_exists_section_of_isAlgClosed.lean`,
`Theorems/Thm_AlgebraicGeometry_ext_of_forall_comp_eq_of_isAlgClosed.lean`,
`P2M/Sol/S_AlgebraicGeometry_ext_of_forall_comp_eq_of_isAlgClosed.lean`,
`Theorems/Thm_AlgebraicGeometry_exists_comp_eq_of_surjective_of_locallyOfFiniteType_
of_isAlgClosed.lean` and
`P2M/Sol/S_AlgebraicGeometry_exists_comp_eq_of_surjective_of_locallyOfFiniteType_
of_isAlgClosed.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.

The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Sections and equality via rational points

A section over a valuation ring factors through a universally closed open
subscheme exactly when the generic point does; rational points over an
algebraically closed field are dense; and two morphisms over an
algebraically closed field agreeing on all rational points are equal, so a
surjective morphism locally of finite type lifts rational points.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/-- A section over a valuation ring factors through a universally closed
open subscheme exactly when the generic point does. -/
theorem AlgebraicGeometry.exists_section_comp_eq_iff_factors_of_universallyClosed_of_valuationRing
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X Xf X' : Scheme.{u}} (g : X ⟶ Spec (.of R))
    (i : Xf ⟶ X) [IsOpenImmersion i] [UniversallyClosed (i ≫ g)]
    (j : X' ⟶ X)
    (hcover : Set.range i ∪ Set.range j = Set.univ)
    (hempty : IsLocalRing.closedPoint R ∉ Set.range (j ≫ g))
    (x : Spec (.of K) ⟶ X) (hx : x ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    (∃ s : Spec (.of R) ⟶ X, s ≫ g = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s = x) ↔
      ∃ xf : Spec (.of K) ⟶ Xf, xf ≫ i = x := by
  constructor
  · rintro ⟨s, hsg, hsx⟩
    have hgs : g (s (IsLocalRing.closedPoint R)) = IsLocalRing.closedPoint R := by
      have h := Scheme.Hom.comp_apply s g (IsLocalRing.closedPoint R)
      rw [hsg] at h
      exact h.symm
    have hc : s (IsLocalRing.closedPoint R) ∈ Set.range i := by
      have hmem : s (IsLocalRing.closedPoint R) ∈ Set.range i ∪ Set.range j :=
        hcover ▸ Set.mem_univ _
      rcases hmem with h | ⟨y, hy⟩
      · exact h
      · exact absurd ⟨y, by rw [Scheme.Hom.comp_apply, hy, hgs]⟩ hempty
    have hsub : Set.range s ⊆ Set.range i := by
      rintro _ ⟨t, rfl⟩
      exact ((IsLocalRing.specializes_closedPoint t).map s.continuous).mem_open
        (IsOpenImmersion.isOpen_range i) hc
    refine ⟨Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ IsOpenImmersion.lift i s hsub, ?_⟩
    rw [Category.assoc, IsOpenImmersion.lift_fac, hsx]
  · rintro ⟨xf, rfl⟩
    have H : ValuativeCriterion.Existence (i ≫ g) := by
      have h : UniversallyClosed (i ≫ g) := inferInstance
      rw [UniversallyClosed.eq_valuativeCriterion] at h
      exact h.1
    let S : ValuativeCommSq (i ≫ g) :=
      { R := R, K := K, i₁ := xf, i₂ := 𝟙 _, commSq := ⟨by simpa using hx⟩ }
    obtain ⟨l, hl₁, hl₂⟩ := (H S).exists_lift
    dsimp only [S] at hl₁ hl₂
    exact ⟨l ≫ i, by simpa using hl₂, by rw [← Category.assoc, hl₁]⟩

/-- Rational points over an algebraically closed field are dense. -/
theorem AlgebraicGeometry.dense_setOf_exists_section_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] :
    Dense {x : X | ∃ s : Spec (.of k) ⟶ X, s ≫ f = 𝟙 _ ∧
      s (IsLocalRing.closedPoint k) = x} := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hsub : closedPoints X ⊆
      {x : X | ∃ s : Spec (.of k) ⟶ X, s ≫ f = 𝟙 _ ∧
        s (IsLocalRing.closedPoint k) = x} :=
    fun x hx => ⟨pointOfClosedPoint f x hx, pointOfClosedPoint_comp f x hx,
      pointOfClosedPoint_apply f x hx _⟩
  exact Dense.mono hsub (dense_iff_closure_eq.mpr (closure_closedPoints (X := X)))

/-- Two morphisms over an algebraically closed field agreeing on all
rational points are equal. -/
theorem AlgebraicGeometry.ext_of_forall_comp_eq_of_isAlgClosed
    {κ : Type u} [Field κ] [IsAlgClosed κ] {X Y : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of κ)) (fY : Y ⟶ Spec (CommRingCat.of κ))
    [LocallyOfFiniteType fX] [IsReduced X] [IsSeparated fY]
    {f g : X ⟶ Y} (hf : f ≫ fY = fX) (hg : g ≫ fY = fX)
    (h : ∀ x : Spec (CommRingCat.of κ) ⟶ X, x ≫ fX = 𝟙 _ → x ≫ f = x ≫ g) :
    f = g := by
  classical
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace fX
  refine ext_of_fromSpecResidueField_eq f g fY (closedPoints X) ?_ ?_ (hf.trans hg.symm)
  · rw [Dense, ← Set.eq_univ_iff_forall]
    exact closure_closedPoints
  · intro x hx
    have hxcl : IsClosed ({x} : Set X) := hx
    have : LocallyOfFiniteType (X.fromSpecResidueField x) :=
      isClosed_singleton_iff_locallyOfFiniteType.1 hxcl
    have : LocallyOfFiniteType (X.fromSpecResidueField x ≫ fX) := inferInstance
    set φ : CommRingCat.of κ ⟶ CommRingCat.of (X.residueField x) :=
      Spec.preimage (X.fromSpecResidueField x ≫ fX) with hφdef
    have hφ : Spec.map φ = X.fromSpecResidueField x ≫ fX := Spec.map_preimage _
    have hft : RingHom.FiniteType φ.hom := by
      have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
      exact HasRingHomProperty.Spec_iff.mp this
    let _ : Algebra κ (X.residueField x) := φ.hom.toAlgebra
    have : Algebra.FiniteType κ (X.residueField x) := hft
    have : Module.Finite κ (X.residueField x) :=
      finite_of_finite_type_of_isJacobsonRing κ (X.residueField x)
    have : Algebra.IsIntegral κ (X.residueField x) := inferInstance
    have hbij : Function.Bijective (algebraMap κ (X.residueField x)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let e : κ ≃+* X.residueField x := RingEquiv.ofBijective (algebraMap κ (X.residueField x)) hbij
    let ψ : CommRingCat.of (X.residueField x) ⟶ CommRingCat.of κ :=
      CommRingCat.ofHom e.symm.toRingHom
    have hψφ : φ ≫ ψ = 𝟙 _ := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      change e.symm (algebraMap κ (X.residueField x) a) = a
      exact e.symm_apply_apply a
    have : IsIso ψ := by
      refine ⟨⟨φ, ?_, hψφ⟩⟩
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro b
      change algebraMap κ (X.residueField x) (e.symm b) = b
      exact e.apply_symm_apply b
    let x₀ : Spec (CommRingCat.of κ) ⟶ X := Spec.map ψ ≫ X.fromSpecResidueField x
    have hx₀ : x₀ ≫ fX = 𝟙 _ := by
      change (Spec.map ψ ≫ X.fromSpecResidueField x) ≫ fX = 𝟙 _
      rw [Category.assoc, ← hφ, ← Spec.map_comp, hψφ, Spec.map_id]
    have hx₀' := h x₀ hx₀
    change (Spec.map ψ ≫ X.fromSpecResidueField x) ≫ f =
      (Spec.map ψ ≫ X.fromSpecResidueField x) ≫ g at hx₀'
    rw [Category.assoc, Category.assoc] at hx₀'
    exact (cancel_epi (Spec.map ψ)).1 hx₀'

/-- A surjective morphism locally of finite type lifts rational points over
an algebraically closed field. -/
theorem AlgebraicGeometry.exists_comp_eq_of_surjective_of_locallyOfFiniteType_of_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Surjective f] (y : Spec (.of K) ⟶ Y) :
    ∃ x : Spec (.of K) ⟶ X, x ≫ f = y := by
  have hne : Nonempty ↑(pullback f y) := by
    obtain ⟨z, -⟩ := (pullback.snd f y).surjective (IsLocalRing.closedPoint K)
    exact ⟨z⟩
  obtain ⟨-, s, hs, -⟩ :=
    (AlgebraicGeometry.dense_setOf_exists_section_of_isAlgClosed (pullback.snd f y)).nonempty
  exact ⟨s ≫ pullback.fst f y, by rw [Category.assoc, pullback.condition, reassoc_of% hs]⟩
