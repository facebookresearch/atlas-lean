/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedMapping.Basic
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalence

/-!
# Homotopy-function-complex data

This file records the homotopical properties of the chosen derived mapping object
`sHom (Q X) (R Y)`. The data is explicit: it installs no global packet or model-category instance.
Raw source invariance and two-variable invariance are split into nested
proposition-valued packets; the larger presentation-and-detection packet
extends them.

An alternative functorial presentation is qualified by a natural span whose components are
realization weak equivalences. This is the functor-level comparison needed for presentation
independence; no equality between replacement choices is asserted.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w v u

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
variable [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]
variable [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]

/-- The minimal source-variable weak-invariance input for raw simplicial mapping objects. -/
structure HomotopyFunctionComplexPrecompData where
  /-- A weak map between cofibrant sources induces a weak precomposition map into a fibrant
  target. -/
  precompWeakOfWeakEquivalence {X Y : C} (f : X ⟶ Y)
      (hX : IsCofibrant X) (hY : IsCofibrant Y) (hf : weakEquivalences C f)
      (Z : C) (hZ : IsFibrant Z) :
    SSet.realizationWeakEquivalences
      (((SimplicialCategory.sHomFunctor C).map f.op).app Z)

/-- The two-variable weak-invariance input for raw simplicial mapping objects. -/
structure HomotopyFunctionComplexInvarianceData extends
    HomotopyFunctionComplexPrecompData (C := C) where
  /-- A weak map between fibrant targets induces a weak postcomposition map out of a cofibrant
  source. -/
  postcompWeakOfWeakEquivalence (X : C) (hX : IsCofibrant X)
      {Y Z : C} (g : Y ⟶ Z) (hY : IsFibrant Y) (hZ : IsFibrant Z)
      (hg : weakEquivalences C g) :
    SSet.realizationWeakEquivalences
      (((SimplicialCategory.sHomFunctor C).obj (.op X)).map g)

/-- Explicit presentation and detection data for the chosen derived simplicial mapping object.

The natural comparison span qualifies one alternative functorial presentation.
The final field is the separate weak-equivalence detector into all fibrant targets. -/
structure HomotopyFunctionComplexData extends
    HomotopyFunctionComplexInvarianceData (C := C) where
  /-- An explicitly qualified alternative functorial mapping-object presentation. -/
  alternativeMappingObject : Cᵒᵖ ⥤ C ⥤ SSet.{v}
  /-- A common comparison presentation for the canonical and alternative presentations. -/
  comparisonMappingObject : Cᵒᵖ ⥤ C ⥤ SSet.{v}
  /-- The natural comparison leg to the canonical chosen derived mapping object. -/
  comparisonToDerived :
    comparisonMappingObject ⟶ derivedMappingObject (C := C)
  /-- The natural comparison leg to the explicitly qualified alternative. -/
  comparisonToAlternative :
    comparisonMappingObject ⟶ alternativeMappingObject
  /-- Every component of the canonical comparison leg is a realization weak equivalence. -/
  comparisonToDerived_weak (X : Cᵒᵖ) (Y : C) :
    SSet.realizationWeakEquivalences ((comparisonToDerived.app X).app Y)
  /-- Every component of the alternative comparison leg is a realization weak equivalence. -/
  comparisonToAlternative_weak (X : Cᵒᵖ) (Y : C) :
    SSet.realizationWeakEquivalences ((comparisonToAlternative.app X).app Y)
  /-- The chosen derived mapping object detects base weak equivalences by precomposition into all
  fibrant targets. This is detection data, not a consequence of presentation independence. -/
  weakEquivalence_iff_derivedMappingPrecomp {X Y : C} (f : X ⟶ Y) :
    weakEquivalences C f ↔ ∀ (Z : C), IsFibrant Z →
      SSet.realizationWeakEquivalences (derivedMappingPrecomp (C := C) f Z)

private noncomputable def cofibrantReplacementComparison
    (data : HomotopyFunctionComplexData (C := C)) :
    data.comparisonMappingObject ⟶ derivedMappingObject (C := C) :=
  data.comparisonToDerived

private noncomputable def fibrantReplacementComparison
    (data : HomotopyFunctionComplexData (C := C)) :
    data.comparisonMappingObject ⟶ data.alternativeMappingObject :=
  data.comparisonToAlternative

private theorem derivedMappingObjectReplacementZigzag
    (data : HomotopyFunctionComplexData (C := C)) (X : Cᵒᵖ) (Y : C) :
    SSet.realizationWeakEquivalences
        (((cofibrantReplacementComparison data).app X).app Y) ∧
      SSet.realizationWeakEquivalences
        (((fibrantReplacementComparison data).app X).app Y) := by
  exact ⟨data.comparisonToDerived_weak X Y,
    data.comparisonToAlternative_weak X Y⟩

/-- Precomposition is a realization weak equivalence in the chosen derived
mapping object exactly when it is one in the qualified alternative
presentation. -/
theorem derivedMappingPrecomp_weak_iff_alternative
    (data : HomotopyFunctionComplexData (C := C)) {X Y : C}
    (f : X ⟶ Y) (Z : C) :
    SSet.realizationWeakEquivalences (derivedMappingPrecomp (C := C) f Z) ↔
      SSet.realizationWeakEquivalences
        ((data.alternativeMappingObject.map f.op).app Z) := by
  let F := data.comparisonMappingObject
  let G := derivedMappingObject (C := C)
  let H := data.alternativeMappingObject
  let η : F ⟶ G := cofibrantReplacementComparison data
  let θ : F ⟶ H := fibrantReplacementComparison data
  have hηY : SSet.realizationWeakEquivalences ((η.app (.op Y)).app Z) := by
    exact (derivedMappingObjectReplacementZigzag data (.op Y) Z).1
  have hηX : SSet.realizationWeakEquivalences ((η.app (.op X)).app Z) := by
    exact (derivedMappingObjectReplacementZigzag data (.op X) Z).1
  have hθY : SSet.realizationWeakEquivalences ((θ.app (.op Y)).app Z) := by
    exact (derivedMappingObjectReplacementZigzag data (.op Y) Z).2
  have hθX : SSet.realizationWeakEquivalences ((θ.app (.op X)).app Z) := by
    exact (derivedMappingObjectReplacementZigzag data (.op X) Z).2
  have hηNaturality :
      (F.map f.op).app Z ≫ (η.app (.op X)).app Z =
        (η.app (.op Y)).app Z ≫ (G.map f.op).app Z := by
    exact congr_fun (congr_arg NatTrans.app (η.naturality f.op)) Z
  have hθNaturality :
      (F.map f.op).app Z ≫ (θ.app (.op X)).app Z =
        (θ.app (.op Y)).app Z ≫ (H.map f.op).app Z := by
    exact congr_fun (congr_arg NatTrans.app (θ.naturality f.op)) Z
  have hη :
      SSet.realizationWeakEquivalences ((F.map f.op).app Z) ↔
        SSet.realizationWeakEquivalences ((G.map f.op).app Z) := by
    constructor
    · intro hF
      apply SSet.realizationWeakEquivalences.of_precomp
        ((η.app (.op Y)).app Z) ((G.map f.op).app Z) hηY
      rw [← hηNaturality]
      exact SSet.realizationWeakEquivalences.comp_mem _ _ hF hηX
    · intro hG
      apply SSet.realizationWeakEquivalences.of_postcomp
        ((F.map f.op).app Z) ((η.app (.op X)).app Z) hηX
      rw [hηNaturality]
      exact SSet.realizationWeakEquivalences.comp_mem _ _ hηY hG
  have hθ :
      SSet.realizationWeakEquivalences ((F.map f.op).app Z) ↔
        SSet.realizationWeakEquivalences ((H.map f.op).app Z) := by
    constructor
    · intro hF
      apply SSet.realizationWeakEquivalences.of_precomp
        ((θ.app (.op Y)).app Z) ((H.map f.op).app Z) hθY
      rw [← hθNaturality]
      exact SSet.realizationWeakEquivalences.comp_mem _ _ hF hθX
    · intro hH
      apply SSet.realizationWeakEquivalences.of_postcomp
        ((F.map f.op).app Z) ((θ.app (.op X)).app Z) hθX
      rw [hθNaturality]
      exact SSet.realizationWeakEquivalences.comp_mem _ _ hθY hH
  simpa [G, derivedMappingPrecomp] using hη.symm.trans hθ

/-- Postcomposition is a realization weak equivalence in the chosen derived
mapping object exactly when it is one in the qualified alternative
presentation. -/
theorem derivedMappingPostcomp_weak_iff_alternative
    (data : HomotopyFunctionComplexData (C := C)) (X : C) {Y Z : C}
    (g : Y ⟶ Z) :
    SSet.realizationWeakEquivalences (derivedMappingPostcomp (C := C) X g) ↔
      SSet.realizationWeakEquivalences
        ((data.alternativeMappingObject.obj (.op X)).map g) := by
  let F := data.comparisonMappingObject
  let G := derivedMappingObject (C := C)
  let H := data.alternativeMappingObject
  let η : F ⟶ G := cofibrantReplacementComparison data
  let θ : F ⟶ H := fibrantReplacementComparison data
  have hηY : SSet.realizationWeakEquivalences ((η.app (.op X)).app Y) := by
    exact (derivedMappingObjectReplacementZigzag data (.op X) Y).1
  have hηZ : SSet.realizationWeakEquivalences ((η.app (.op X)).app Z) := by
    exact (derivedMappingObjectReplacementZigzag data (.op X) Z).1
  have hθY : SSet.realizationWeakEquivalences ((θ.app (.op X)).app Y) := by
    exact (derivedMappingObjectReplacementZigzag data (.op X) Y).2
  have hθZ : SSet.realizationWeakEquivalences ((θ.app (.op X)).app Z) := by
    exact (derivedMappingObjectReplacementZigzag data (.op X) Z).2
  have hηNaturality :
      (F.obj (.op X)).map g ≫ (η.app (.op X)).app Z =
        (η.app (.op X)).app Y ≫ (G.obj (.op X)).map g := by
    exact (η.app (.op X)).naturality g
  have hθNaturality :
      (F.obj (.op X)).map g ≫ (θ.app (.op X)).app Z =
        (θ.app (.op X)).app Y ≫ (H.obj (.op X)).map g := by
    exact (θ.app (.op X)).naturality g
  have hη :
      SSet.realizationWeakEquivalences ((F.obj (.op X)).map g) ↔
        SSet.realizationWeakEquivalences ((G.obj (.op X)).map g) := by
    constructor
    · intro hF
      apply SSet.realizationWeakEquivalences.of_precomp
        ((η.app (.op X)).app Y) ((G.obj (.op X)).map g) hηY
      rw [← hηNaturality]
      exact SSet.realizationWeakEquivalences.comp_mem _ _ hF hηZ
    · intro hG
      apply SSet.realizationWeakEquivalences.of_postcomp
        ((F.obj (.op X)).map g) ((η.app (.op X)).app Z) hηZ
      rw [hηNaturality]
      exact SSet.realizationWeakEquivalences.comp_mem _ _ hηY hG
  have hθ :
      SSet.realizationWeakEquivalences ((F.obj (.op X)).map g) ↔
        SSet.realizationWeakEquivalences ((H.obj (.op X)).map g) := by
    constructor
    · intro hF
      apply SSet.realizationWeakEquivalences.of_precomp
        ((θ.app (.op X)).app Y) ((H.obj (.op X)).map g) hθY
      rw [← hθNaturality]
      exact SSet.realizationWeakEquivalences.comp_mem _ _ hF hθZ
    · intro hH
      apply SSet.realizationWeakEquivalences.of_postcomp
        ((F.obj (.op X)).map g) ((θ.app (.op X)).app Z) hθZ
      rw [hθNaturality]
      exact SSet.realizationWeakEquivalences.comp_mem _ _ hθY hH
  simpa [G, derivedMappingPostcomp] using hη.symm.trans hθ

/-- The local-equivalence predicate computed with the qualified alternative
mapping presentation agrees with the chosen derived mapping object. -/
theorem localEquivalences_replacement_independent
    (data : HomotopyFunctionComplexData (C := C)) {I : Type w}
    (S : I → Arrow C) {X Y : C} (f : X ⟶ Y) :
    (∀ Z, (IsFibrant Z ∧ ∀ i,
        SSet.realizationWeakEquivalences
          ((data.alternativeMappingObject.map (S i).hom.op).app Z)) →
      SSet.realizationWeakEquivalences
        ((data.alternativeMappingObject.map f.op).app Z)) ↔
      (∀ Z, (IsFibrant Z ∧ ∀ i,
          SSet.realizationWeakEquivalences
            (derivedMappingPrecomp (C := C) (S i).hom Z)) →
        SSet.realizationWeakEquivalences
          (derivedMappingPrecomp (C := C) f Z)) := by
  constructor
  · intro h Z hZ
    apply (derivedMappingPrecomp_weak_iff_alternative data f Z).mpr
    apply h Z
    exact ⟨hZ.1, fun i ↦
      (derivedMappingPrecomp_weak_iff_alternative data (S i).hom Z).mp
        (hZ.2 i)⟩
  · intro h Z hZ
    apply (derivedMappingPrecomp_weak_iff_alternative data f Z).mp
    apply h Z
    exact ⟨hZ.1, fun i ↦
      (derivedMappingPrecomp_weak_iff_alternative data (S i).hom Z).mpr
        (hZ.2 i)⟩

end HomotopicalAlgebra
