/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: Tsutomu Okano <toskua@meta.com>
-/

-- Author: Tsutomu Okano <toskua@meta.com>

module

public import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.Basic
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenFibrantCriterion

/-!
# Quillen adjunctions between selected left Bousfield localizations

The existing localized carriers retain a full original adjunction, with
both functors, all maps, the unit, the counit and the hom equivalence.
For an original level Quillen adjunction, the localized adjunction is
Quillen exactly when its original right functor sends every target
local-fibrant object to a source local-fibrant object.

The proof uses the original cofibration classes and the existing agreement
of base and localized fibrations between local-fibrant objects, followed
by the fibrant-object criterion for Quillen adjunctions. The localization
families, base models and selected localization data remain explicit.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe wS wT vC vD uC uD

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.LeftLocalized

variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [SimplicialCategory C]
  [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]
  [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]
  {D : Type uD} [Category.{vD} D] [ModelCategory D] [SimplicialCategory D]
  [HasFunctorialFactorization (cofibrations D) (trivialFibrations D)]
  [HasFunctorialFactorization (trivialCofibrations D) (fibrations D)]
  {I : Type wS} {J : Type wT} {S : I → Arrow C} {T : J → Arrow D}
  (LC : LeftBousfieldLocalizationData S) (LD : LeftBousfieldLocalizationData T)

/-- The original left functor on the existing selected localized carriers. -/
def leftFunctor (F : C ⥤ D) : LeftLocalized LC ⥤ LeftLocalized LD :=
  (toBase LC ⋙ F) ⋙ ofBase LD

/-- The original right functor on the existing selected localized carriers. -/
def rightFunctor (R : D ⥤ C) : LeftLocalized LD ⥤ LeftLocalized LC :=
  (toBase LD ⋙ R) ⋙ ofBase LC

@[simp]
theorem leftFunctor_obj_toBase (F : C ⥤ D) (X : LeftLocalized LC) :
    (toBase LD).obj ((leftFunctor LC LD F).obj X) = F.obj X.1 := rfl

@[simp]
theorem rightFunctor_obj_toBase (R : D ⥤ C) (Y : LeftLocalized LD) :
    (toBase LC).obj ((rightFunctor LC LD R).obj Y) = R.obj Y.1 := rfl

/-- Every original left-functor map is retained after forgetting the localization tag. -/
@[simp]
theorem leftFunctor_map_toBase (F : C ⥤ D) {X Y : LeftLocalized LC} (f : X ⟶ Y) :
    (toBase LD).map ((leftFunctor LC LD F).map f) = F.map ((toBase LC).map f) := rfl

/-- Every original right-functor map is retained after forgetting the localization tag. -/
@[simp]
theorem rightFunctor_map_toBase (R : D ⥤ C) {X Y : LeftLocalized LD} (f : X ⟶ Y) :
    (toBase LC).map ((rightFunctor LC LD R).map f) = R.map ((toBase LD).map f) := rfl

/-- The whole original left functor is retained, including every source and target map. -/
theorem leftFunctor_comp_toBase (F : C ⥤ D) :
    leftFunctor LC LD F ⋙ toBase LD = toBase LC ⋙ F := rfl

/-- The whole original right functor is retained, including every source and target map. -/
theorem rightFunctor_comp_toBase (R : D ⥤ C) :
    rightFunctor LC LD R ⋙ toBase LC = toBase LD ⋙ R := rfl

theorem ofBase_comp_leftFunctor (F : C ⥤ D) :
    ofBase LC ⋙ leftFunctor LC LD F = F ⋙ ofBase LD := rfl

theorem ofBase_comp_rightFunctor (R : D ⥤ C) :
    ofBase LD ⋙ rightFunctor LC LD R = R ⋙ ofBase LC := rfl

/-- In particular, any actual original free or index map has its same localized image. -/
theorem ofBase_leftFunctor_map (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    (leftFunctor LC LD F).map ((ofBase LC).map f) = (ofBase LD).map (F.map f) := rfl

theorem ofBase_rightFunctor_map (R : D ⥤ C) {X Y : D} (f : X ⟶ Y) :
    (rightFunctor LC LD R).map ((ofBase LD).map f) = (ofBase LC).map (R.map f) := rfl

variable {F : C ⥤ D} {R : D ⥤ C}

/-- The full original adjunction, with its original unit and counit components. -/
def adjunction (adj : F ⊣ R) : leftFunctor LC LD F ⊣ rightFunctor LC LD R where
  unit :=
    { app := fun X => InducedCategory.homMk (adj.unit.app X.1)
      naturality := by
        intro X Y f
        apply InducedCategory.hom_ext
        exact adj.unit.naturality f.hom }
  counit :=
    { app := fun Y => InducedCategory.homMk (adj.counit.app Y.1)
      naturality := by
        intro X Y f
        apply InducedCategory.hom_ext
        exact adj.counit.naturality f.hom }
  left_triangle_components X := by
    apply InducedCategory.hom_ext
    exact adj.left_triangle_components X.1
  right_triangle_components Y := by
    apply InducedCategory.hom_ext
    exact adj.right_triangle_components Y.1

/-- The entire localized unit component projects to the original level unit. -/
@[simp]
theorem adjunction_unit_toBase (adj : F ⊣ R) (X : LeftLocalized LC) :
    (toBase LC).map ((adjunction LC LD adj).unit.app X) = adj.unit.app X.1 := rfl

/-- The entire localized counit component projects to the original level counit. -/
@[simp]
theorem adjunction_counit_toBase (adj : F ⊣ R) (Y : LeftLocalized LD) :
    (toBase LD).map ((adjunction LC LD adj).counit.app Y) = adj.counit.app Y.1 := rfl

/-- Both directions of the full hom equivalence retain the original adjunction functions. -/
theorem adjunction_homEquiv_toBase (adj : F ⊣ R) (X : LeftLocalized LC)
    (Y : LeftLocalized LD) (f : (leftFunctor LC LD F).obj X ⟶ Y) :
    (toBase LC).map ((adjunction LC LD adj).homEquiv X Y f) =
      adj.homEquiv X.1 Y.1 ((toBase LD).map f) := rfl

theorem adjunction_homEquiv_symm_toBase (adj : F ⊣ R) (X : LeftLocalized LC)
    (Y : LeftLocalized LD) (g : X ⟶ (rightFunctor LC LD R).obj Y) :
    (toBase LD).map (((adjunction LC LD adj).homEquiv X Y).symm g) =
      (adj.homEquiv X.1 Y.1).symm ((toBase LC).map g) := rfl

section Quillen

variable (adj : F ⊣ R) [baseQuillen : Adjunction.IsQuillenAdjunction adj]

include baseQuillen LC LD

/-- Original cofibrations are preserved on the actual selected localized carriers. -/
theorem leftFunctor_preservesCofibrations : PreservesCofibrations (leftFunctor LC LD F) := by
  intro X Y f hf
  change cofibrations C f.hom at hf
  change cofibrations D (F.map f.hom)
  exact baseQuillen.preservesCofibrations f.hom hf

/-- Right preservation of local-fibrant objects gives preservation of all fibrations
between fibrant objects in the selected localizations. -/
theorem rightFunctor_preservesFibrationsBetweenFibrantObjects
    (hR : ∀ Z : D, isLocalFibrant T Z → isLocalFibrant S (R.obj Z)) :
    PreservesFibrationsBetweenFibrantObjects (rightFunctor LC LD R) := by
  intro X Y p hp
  have hX : isLocalFibrant T X.1 := (fibrant_iff LD X).1 hp.2.1
  have hY : isLocalFibrant T Y.1 := (fibrant_iff LD Y).1 hp.2.2
  have hpBase : fibrations D ((toBase LD).map p) :=
    (fibration_iff_of_local LD p hX hY).1 hp.1
  have hpImage : fibrations C (R.map ((toBase LD).map p)) :=
    Adjunction.IsQuillenAdjunction.preservesFibrations (adj := adj) p.hom hpBase
  exact (fibration_iff_of_local LC ((rightFunctor LC LD R).map p)
    (hR X.1 hX) (hR Y.1 hY)).2 hpImage

/-- The full local-object condition constructs the localized Quillen adjunction. -/
theorem isQuillenAdjunction_of_preservesLocalFibrant
    (hR : ∀ Z : D, isLocalFibrant T Z → isLocalFibrant S (R.obj Z)) :
    Adjunction.IsQuillenAdjunction (adjunction LC LD adj) :=
  Adjunction.IsQuillenAdjunction.mkOfPreservesCofibrationsAndFibrationsBetweenFibrantObjects
    (leftFunctor_preservesCofibrations LC LD adj)
    (rightFunctor_preservesFibrationsBetweenFibrantObjects LC LD adj hR)

/-- Exact descent criterion on every actual local-fibrant object of the full target family. -/
theorem isQuillenAdjunction_iff_preservesLocalFibrant :
    Adjunction.IsQuillenAdjunction (adjunction LC LD adj) ↔
      ∀ Z : D, isLocalFibrant T Z → isLocalFibrant S (R.obj Z) := by
  constructor
  · intro h Z hZ
    let _ : Adjunction.IsQuillenAdjunction (adjunction LC LD adj) := h
    have hZ' : IsFibrant ((ofBase LD).obj Z) := (fibrant_iff LD _).2 hZ
    have hImage : IsFibrant ((rightFunctor LC LD R).obj ((ofBase LD).obj Z)) :=
      Adjunction.IsQuillenAdjunction.preservesFibrantObjects
        (adj := adjunction LC LD adj) hZ'
    exact (fibrant_iff LC _).1 hImage
  · exact isQuillenAdjunction_of_preservesLocalFibrant LC LD adj

/-- The constructed left adjoint preserves every actual localized trivial cofibration. -/
theorem leftFunctor_preservesTrivialCofibrations
    (hR : ∀ Z : D, isLocalFibrant T Z → isLocalFibrant S (R.obj Z)) :
    PreservesTrivialCofibrations (leftFunctor LC LD F) :=
  (isQuillenAdjunction_of_preservesLocalFibrant LC LD adj hR).preservesTrivialCofibrations

/-- The constructed right adjoint preserves arbitrary actual localized fibrations. -/
theorem rightFunctor_preservesFibrations
    (hR : ∀ Z : D, isLocalFibrant T Z → isLocalFibrant S (R.obj Z)) :
    PreservesFibrations (rightFunctor LC LD R) := by
  let _ : Adjunction.IsQuillenAdjunction (adjunction LC LD adj) :=
    isQuillenAdjunction_of_preservesLocalFibrant LC LD adj hR
  exact Adjunction.IsQuillenAdjunction.preservesFibrations (adj := adjunction LC LD adj)

/-- The constructed right adjoint preserves every actual localized trivial fibration. -/
theorem rightFunctor_preservesTrivialFibrations
    (hR : ∀ Z : D, isLocalFibrant T Z → isLocalFibrant S (R.obj Z)) :
    PreservesTrivialFibrations (rightFunctor LC LD R) := by
  let _ : Adjunction.IsQuillenAdjunction (adjunction LC LD adj) :=
    isQuillenAdjunction_of_preservesLocalFibrant LC LD adj hR
  exact Adjunction.IsQuillenAdjunction.preservesTrivialFibrations (adj := adjunction LC LD adj)

/-- Local equivalences between original cofibrant objects have the actual local-equivalent
left-functor image. Both original localization families and maps are retained. -/
theorem map_localEquivalence_of_cofibrant
    (hR : ∀ Z : D, isLocalFibrant T Z → isLocalFibrant S (R.obj Z))
    {X Y : C} (f : X ⟶ Y) (hf : localEquivalences S f)
    (hX : IsCofibrant X) (hY : IsCofibrant Y) :
    localEquivalences T (F.map f) := by
  let _ : Adjunction.IsQuillenAdjunction (adjunction LC LD adj) :=
    isQuillenAdjunction_of_preservesLocalFibrant LC LD adj hR
  let _ : Adjunction.IsQuillenAdjunction (equivalence LC).toAdjunction := ofBase_isLeftQuillen LC
  let _ : IsCofibrant ((ofBase LC).obj X) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
      (adj := (equivalence LC).toAdjunction) hX
  let _ : IsCofibrant ((ofBase LC).obj Y) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
      (adj := (equivalence LC).toAdjunction) hY
  let _ : WeakEquivalence ((ofBase LC).map f) := (weakEquivalence_iff _).2 hf
  exact (weakEquivalence_iff _).1
    (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
      (adj := adjunction LC LD adj) ((ofBase LC).map f))

/-- Each original selected localizing map with cofibrant endpoints has its actual
local-equivalent image under the original left functor. -/
theorem image_localizingMap_of_cofibrant
    (hR : ∀ Z : D, isLocalFibrant T Z → isLocalFibrant S (R.obj Z)) (i : I)
    (hX : IsCofibrant (S i).left) (hY : IsCofibrant (S i).right) :
    localEquivalences T (F.map (S i).hom) :=
  map_localEquivalence_of_cofibrant LC LD adj hR (S i).hom (LC.localizingMaps i) hX hY

end Quillen

end HomotopicalAlgebra.LeftLocalized
