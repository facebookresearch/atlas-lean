/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Avocado
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.FundamentalLemma
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

/-!
# Generic homotopy-function-complex localization calculus

This file records the genuine semantic inputs missing from a bare simplicial
enrichment: boundary pushout-products and their tensor--Hom lifting law, SM7
mapping-object behavior, and a composition-compatible identification of
derived mapping components with morphisms in the base homotopy category.

From those inputs it proves the two generic comparison theorems needed by a
left Bousfield localization. Neither theorem is a field, and no localized
model structure or raw-carrier instance is installed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w v u

open CategoryTheory Limits MorphismProperty Simplicial
open scoped Simplicial

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
variable [SimplicialCategory C]
variable [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]
variable [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]

/-- Explicit tensor--Hom and SM7 behavior for a simplicially enriched model
category.

The boundary tensor is the pushout-product with a simplicial boundary
inclusion. The lifting equivalence is the corresponding
pushout-product/pullback-Hom adjunction. All fields are independent of a
localizing family. -/
structure SimplicialModelCategoryData where
  /-- The pushout-product of a map with a simplicial boundary inclusion. -/
  boundaryTensor (n : ℕ) {A B : C} (i : A ⟶ B) : Arrow C
  /-- Boundary tensors preserve cofibrations. -/
  boundaryTensor_cofibration (n : ℕ) {A B : C} (i : A ⟶ B)
      (hi : cofibrations C i) :
    cofibrations C (boundaryTensor n i).hom
  /-- The tensor--Hom lifting equivalence at a fibrant target. -/
  boundaryTensor_lifting_iff (n : ℕ) {A B : C} (i : A ⟶ B)
      (Z : C) (hi : cofibrations C i) (hZ : IsFibrant Z) :
    HasLiftingProperty (SSet.boundary n).ι
        (((SimplicialCategory.sHomFunctor C).map i.op).app Z) ↔
      HasLiftingProperty (boundaryTensor n i).hom (terminal.from Z)
  /-- Degree-zero raw precomposition is ordinary precomposition. -/
  rawPrecomp_app_zero {A B : C} (i : A ⟶ B) (Z : C)
      (b : B ⟶ Z) :
    (((SimplicialCategory.sHomFunctor C).map i.op).app Z).app
        (Opposite.op ⦋0⦌) (SimplicialCategory.homEquiv' B Z b) =
      SimplicialCategory.homEquiv' A Z (i ≫ b)
  /-- A weak raw mapping fibration is surjective on vertices. -/
  rawPrecomp_zero_surjective_of_weak {A B : C} (i : A ⟶ B)
      (Z : C) (hi : cofibrations C i) (hZ : IsFibrant Z)
      (hw : SSet.realizationWeakEquivalences
        (((SimplicialCategory.sHomFunctor C).map i.op).app Z)) :
    Function.Surjective
      ((((SimplicialCategory.sHomFunctor C).map i.op).app Z).app
        (Opposite.op ⦋0⦌))
  /-- Boundary lifting recognizes weakness of a raw mapping fibration. -/
  rawPrecomp_weak_of_boundary_lifts {A B : C} (i : A ⟶ B)
      (Z : C) (hi : cofibrations C i) (hZ : IsFibrant Z)
      (hlift : ∀ n, HasLiftingProperty (SSet.boundary n).ι
        (((SimplicialCategory.sHomFunctor C).map i.op).app Z)) :
    SSet.realizationWeakEquivalences
      (((SimplicialCategory.sHomFunctor C).map i.op).app Z)
  /-- Tensoring with a boundary preserves weakness of raw precomposition. -/
  boundaryTensor_rawPrecomp_weak {A B : C} (i : A ⟶ B)
      (Z : C) (hi : cofibrations C i) (hZ : IsFibrant Z)
      (hw : SSet.realizationWeakEquivalences
        (((SimplicialCategory.sHomFunctor C).map i.op).app Z))
      (n : ℕ) :
    SSet.realizationWeakEquivalences
      (((SimplicialCategory.sHomFunctor C).map
        (boundaryTensor n i).hom.op).app Z)
  /-- Realization weak equivalences are bijective on simplicial components. -/
  realizationWeak_bijective_piZero {X Y : SSet.{v}} (f : X ⟶ Y)
      (hf : SSet.realizationWeakEquivalences f) :
    Function.Bijective (SSet.mapπ₀ f)

/-- Generic calculus for the chosen derived mapping object.

The component equivalence targets Mathlib's fibrant-object homotopy category
and is compatible with precomposition. No localizing family occurs in this
structure. -/
structure HomotopyFunctionComplexCalculusData where
  /-- At cofibrant arrows and fibrant targets, raw and chosen derived
  precomposition have the same weakness. -/
  derived_weak_iff_raw {A B : C} (i : A ⟶ B) (Z : C)
      (hi : cofibrations C i) (hZ : IsFibrant Z) :
    SSet.realizationWeakEquivalences
        (derivedMappingPrecomp (C := C) i Z) ↔
      SSet.realizationWeakEquivalences
        (((SimplicialCategory.sHomFunctor C).map i.op).app Z)
  /-- Components of the chosen mapping complex are morphisms in the base
  homotopy category. -/
  piZeroEquiv (X Y : C) :
    SSet.π₀ (((derivedMappingObject (C := C)).obj (.op X)).obj Y) ≃
      (FibrantObject.HoCat.resolution.obj X ⟶
        FibrantObject.HoCat.resolution.obj Y)
  /-- Precomposition on components is composition in the homotopy category. -/
  piZero_precomp {X Y : C} (f : X ⟶ Y) (Z : C)
      (q : SSet.π₀
        (((derivedMappingObject (C := C)).obj (.op Y)).obj Z)) :
    piZeroEquiv X Z
        (SSet.mapπ₀ (derivedMappingPrecomp (C := C) f Z) q) =
      FibrantObject.HoCat.resolution.map f ≫ piZeroEquiv Y Z q
  /-- The base homotopy category detects exactly the base weak
  equivalences. -/
  weakEquivalence_iff_isIso_resolution {X Y : C} (f : X ⟶ Y) :
    weakEquivalences C f ↔ IsIso (FibrantObject.HoCat.resolution.map f)

/-- Terminal localized fibrations are exactly base-fibrant derived-local
objects, assuming genuine tensor--Hom/SM7 and homotopy-function-complex
calculus data. -/
theorem localizedFibrations_terminal_iff
    (sm : SimplicialModelCategoryData (C := C))
    (precomp : HomotopyFunctionComplexPrecompData (C := C))
    (calculus : HomotopyFunctionComplexCalculusData (C := C))
    {I : Type w} (S : I → Arrow C) (X : C) :
    localizedFibrations S (terminal.from X) ↔ isLocalFibrant S X := by
  have baseWeakDerived {A B : C} (f : A ⟶ B)
      (hf : weakEquivalences C f) (Z : C) :
      SSet.realizationWeakEquivalences
        (derivedMappingPrecomp (C := C) f Z) := by
    have hQf : weakEquivalences C
        ((cofibrantReplacement (C := C)).map f) := by
      apply (weakEquivalences C).of_postcomp (W' := weakEquivalences C)
        ((cofibrantReplacement (C := C)).map f)
        ((cofibrantReplacementCounit (C := C)).app B)
        WeakEquivalence.mem
      rw [(cofibrantReplacementCounit (C := C)).naturality]
      exact (weakEquivalences C).comp_mem _ _ WeakEquivalence.mem hf
    have h := precomp.precompWeakOfWeakEquivalence
      ((cofibrantReplacement (C := C)).map f)
      (by infer_instance) (by infer_instance) hQf
      ((fibrantReplacement (C := C)).obj Z) (by infer_instance)
    simpa [derivedMappingPrecomp, derivedMappingObject] using h
  constructor
  · intro hloc
    have hFibProp : fibrations C (terminal.from X) := by
      rw [← rlp_eq_of_wfs (trivialCofibrations C) (fibrations C)]
      intro A B i hi
      exact hloc i
        ⟨hi.1, weakEquivalences_le_localEquivalences
          precomp S i hi.2⟩
    let hFib : IsFibrant X := (fibration_iff _).2 hFibProp
    refine ⟨hFib, ?_⟩
    intro k
    let d := factorizationData (cofibrations C) (trivialFibrations C)
      (S k).hom
    let _ : (localEquivalences S).HasTwoOutOfThreeProperty :=
      localEquivalences_hasTwoOutOfThreeProperty S
    have hsLocal : localEquivalences S (S k).hom := by
      intro Z hZ
      exact hZ.2 k
    have hpLocal : localEquivalences S d.p :=
      weakEquivalences_le_localEquivalences precomp S d.p d.hp.2
    have hiLocal : localEquivalences S d.i := by
      apply (localEquivalences S).of_postcomp d.i d.p hpLocal
      simpa only [d.fac] using hsLocal
    have hiRaw : SSet.realizationWeakEquivalences
        (((SimplicialCategory.sHomFunctor C).map d.i.op).app X) := by
      apply sm.rawPrecomp_weak_of_boundary_lifts d.i X d.hi hFib
      intro n
      apply (sm.boundaryTensor_lifting_iff n d.i X d.hi hFib).2
      apply hloc (sm.boundaryTensor n d.i).hom
      constructor
      · exact sm.boundaryTensor_cofibration n d.i d.hi
      · intro Z hZ
        apply (calculus.derived_weak_iff_raw
          (sm.boundaryTensor n d.i).hom Z
          (sm.boundaryTensor_cofibration n d.i d.hi) hZ.1).2
        apply sm.boundaryTensor_rawPrecomp_weak d.i Z d.hi hZ.1
        exact (calculus.derived_weak_iff_raw d.i Z d.hi hZ.1).1
          (hiLocal Z hZ)
    have hiDerived : SSet.realizationWeakEquivalences
        (derivedMappingPrecomp (C := C) d.i X) :=
      (calculus.derived_weak_iff_raw d.i X d.hi hFib).2 hiRaw
    have hpDerived : SSet.realizationWeakEquivalences
        (derivedMappingPrecomp (C := C) d.p X) :=
      baseWeakDerived d.p d.hp.2 X
    rw [← d.fac, derivedMappingPrecomp_comp]
    exact SSet.realizationWeakEquivalences.comp_mem _ _
      hpDerived hiDerived
  · intro hX A B i hi
    have hraw : SSet.realizationWeakEquivalences
        (((SimplicialCategory.sHomFunctor C).map i.op).app X) :=
      (calculus.derived_weak_iff_raw i X hi.1 hX.1).1
        (hi.2 X hX)
    have hsurj := sm.rawPrecomp_zero_surjective_of_weak
      i X hi.1 hX.1 hraw
    refine ⟨?_⟩
    intro a b sq
    let a₀ := SimplicialCategory.homEquiv' A X a
    obtain ⟨b₀, hb₀⟩ := hsurj a₀
    let l : B ⟶ X := (SimplicialCategory.homEquiv' B X).symm b₀
    apply CommSq.HasLift.mk'
    refine { l := l, fac_left := ?_, fac_right := ?_ }
    · apply (SimplicialCategory.homEquiv' A X).injective
      rw [← sm.rawPrecomp_app_zero i X l]
      change _ = a₀
      have hl : SimplicialCategory.homEquiv' B X l = b₀ := by
        dsimp only [l]
        exact (SimplicialCategory.homEquiv' B X).apply_symm_apply b₀
      rw [hl]
      exact hb₀
    · apply terminalIsTerminal.hom_ext

/-- Between derived-local fibrant objects, local equivalences are exactly
the base weak equivalences. Both homotopy-category inverse triangles are
deduced from pi-zero bijectivity. -/
theorem localEquivalences_weakEquivalence_iff_of_local
    (sm : SimplicialModelCategoryData (C := C))
    (precomp : HomotopyFunctionComplexPrecompData (C := C))
    (calculus : HomotopyFunctionComplexCalculusData (C := C))
    {I : Type w} (S : I → Arrow C) {X Y : C} (f : X ⟶ Y)
    (hX : isLocalFibrant S X) (hY : isLocalFibrant S Y) :
    localEquivalences S f ↔ weakEquivalences C f := by
  constructor
  · intro hf
    let F := FibrantObject.HoCat.resolution (C := C)
    let eXX := calculus.piZeroEquiv X X
    let eYX := calculus.piZeroEquiv Y X
    let eXY := calculus.piZeroEquiv X Y
    let eYY := calculus.piZeroEquiv Y Y
    have hπX : Function.Bijective
        (SSet.mapπ₀ (derivedMappingPrecomp (C := C) f X)) :=
      sm.realizationWeak_bijective_piZero _ (hf X hX)
    have hπY : Function.Bijective
        (SSet.mapπ₀ (derivedMappingPrecomp (C := C) f Y)) :=
      sm.realizationWeak_bijective_piZero _ (hf Y hY)
    obtain ⟨qg, hqg⟩ := hπX.2 (eXX.symm (𝟙 (F.obj X)))
    let g : F.obj Y ⟶ F.obj X := eYX qg
    have hfg : F.map f ≫ g = 𝟙 (F.obj X) := by
      calc
        F.map f ≫ g = eXX
            (SSet.mapπ₀ (derivedMappingPrecomp (C := C) f X) qg) :=
          (calculus.piZero_precomp f X qg).symm
        _ = eXX (eXX.symm (𝟙 (F.obj X))) := by rw [hqg]
        _ = 𝟙 (F.obj X) := eXX.apply_symm_apply _
    let qgf := eYY.symm (g ≫ F.map f)
    let qid := eYY.symm (𝟙 (F.obj Y))
    have hq : qgf = qid := by
      apply hπY.1
      apply eXY.injective
      rw [calculus.piZero_precomp f Y qgf,
        calculus.piZero_precomp f Y qid]
      dsimp only [qgf, qid]
      rw [eYY.apply_symm_apply, eYY.apply_symm_apply]
      rw [← Category.assoc, hfg, Category.id_comp, Category.comp_id]
    have hgf : g ≫ F.map f = 𝟙 (F.obj Y) := by
      have h := congrArg eYY hq
      simpa only [qgf, qid, eYY.apply_symm_apply] using h
    let _ : IsIso (F.map f) := ⟨⟨g, hfg, hgf⟩⟩
    exact (calculus.weakEquivalence_iff_isIso_resolution f).2 inferInstance
  · intro hf
    exact weakEquivalences_le_localEquivalences precomp S f hf

end HomotopicalAlgebra
