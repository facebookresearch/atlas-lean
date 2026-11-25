/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.SourceKanExtensions

set_option autoImplicit false
noncomputable section

universe w w' uD vD uE vE uC vC

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits HomotopicalAlgebra

namespace FunctorProjectiveSourceKanTests

variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  (sD : EssentialIndexData.{w} D C) (sE : EssentialIndexData.{w} E C) (u : D ⥤ E)

include d sD sE

/-- The original adjunct uses the actual source unit and original restricted target map. -/
theorem originalAdjunctComponent (F : D ⥤ C) (G : E ⥤ C)
    (f : (FunctorProjective.SourceKanExtensions.FromData.lan d sD sE u).obj F ⟶ G) (a : D) :
    ((FunctorProjective.SourceKanExtensions.FromData.adjunction d sD sE u).homEquiv F G f).app a =
      ((FunctorProjective.SourceKanExtensions.FromData.adjunction d sD sE u).unit.app F).app a ≫
        f.app (u.obj a) := by
  rw [Adjunction.homEquiv_unit]
  rfl

variable {κ' : Cardinal.{w'}} [Fact κ'.IsRegular] [OrderBot κ'.ord.ToType]
  (dE : CofibrantGenerationData C κ') (tE : EssentialIndexData.{w'} E C)

/-- The original native Lan preserves cofibrations for independent source-model choices. -/
theorem originalCofibrationMap {F G : D ⥤ C} (f : F ⟶ G) :
    letI : ModelCategory (D ⥤ C) := FunctorProjective.SourceConstruction.FromData.modelCategory d sD
    letI : ModelCategory (E ⥤ C) := FunctorProjective.SourceConstruction.FromData.modelCategory dE tE
    cofibrations (D ⥤ C) f → cofibrations (E ⥤ C)
      ((FunctorProjective.SourceKanExtensions.FromData.lan d sD sE u).map f) := by
  let : ModelCategory (D ⥤ C) := FunctorProjective.SourceConstruction.FromData.modelCategory d sD
  let : ModelCategory (E ⥤ C) := FunctorProjective.SourceConstruction.FromData.modelCategory dE tE
  let adj := FunctorProjective.SourceKanExtensions.FromData.adjunction d sD sE u
  let h : adj.IsQuillenAdjunction :=
    FunctorProjective.SourceKanExtensions.FromData.isQuillen d sD sE u dE tE
  exact h.preservesCofibrations f

/-- Trivial cofibration preservation retains the whole original image arrow. -/
theorem originalTrivialCofibrationMap {F G : D ⥤ C} (f : F ⟶ G) :
    letI : ModelCategory (D ⥤ C) := FunctorProjective.SourceConstruction.FromData.modelCategory d sD
    letI : ModelCategory (E ⥤ C) := FunctorProjective.SourceConstruction.FromData.modelCategory dE tE
    trivialCofibrations (D ⥤ C) f → trivialCofibrations (E ⥤ C)
      ((FunctorProjective.SourceKanExtensions.FromData.lan d sD sE u).map f) := by
  let : ModelCategory (D ⥤ C) := FunctorProjective.SourceConstruction.FromData.modelCategory d sD
  let : ModelCategory (E ⥤ C) := FunctorProjective.SourceConstruction.FromData.modelCategory dE tE
  let adj := FunctorProjective.SourceKanExtensions.FromData.adjunction d sD sE u
  let h : adj.IsQuillenAdjunction :=
    FunctorProjective.SourceKanExtensions.FromData.isQuillen d sD sE u dE tE
  exact h.preservesTrivialCofibrations f

section ConventionalSources

omit d sD sE

variable [IsCombinatorialModelCategory.{w} C]
  [EssentiallySmall.{w} D] [EssentiallySmall.{w} E]

/-- Conventional sources construct both inverse native adjunct functions without a target
Lan-existence premise or an incoming model on the functor category. -/
theorem publicSourceAdjunctInverse (F : D ⥤ C) (G : E ⥤ C)
    (f : (FunctorProjective.SourceKanExtensions.lan (C := C) u).obj F ⟶ G) :
    (((FunctorProjective.SourceKanExtensions.adjunction (C := C) u).homEquiv F G).symm
      ((FunctorProjective.SourceKanExtensions.adjunction (C := C) u).homEquiv F G f)) = f :=
  ((FunctorProjective.SourceKanExtensions.adjunction (C := C) u).homEquiv F G).symm_apply_apply f

/-- The public unit retains full naturality on the original source index maps. -/
theorem publicSourceUnitComponent (F : D ⥤ C) {a b : D} (f : a ⟶ b) :
    F.map f ≫ ((FunctorProjective.SourceKanExtensions.adjunction (C := C) u).unit.app F).app b =
      ((FunctorProjective.SourceKanExtensions.adjunction (C := C) u).unit.app F).app a ≫
        (u ⋙ (FunctorProjective.SourceKanExtensions.lan (C := C) u).obj F).map f :=
  ((FunctorProjective.SourceKanExtensions.adjunction (C := C) u).unit.app F).naturality f

end ConventionalSources

end FunctorProjectiveSourceKanTests
