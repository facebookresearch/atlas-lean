/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.Restriction
import MathlibExtTest.AlgebraicTopology.ModelCategory.FunctorProjectiveDataTests
import MathlibExtTest.CategoryTheory.MorphismProperty.FunctorCategory.RestrictionTests

/-!# Original projective restriction at independent actual data and cardinals -/
set_option autoImplicit false
noncomputable section
universe uD vD uE vE uS vS uM vM wD wE wS
open CategoryTheory Functor HomotopicalAlgebra

namespace MathlibExtTest.FunctorProjectiveRestriction

variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  {M : Type uM} [Category.{vM} M] [ModelCategory M]

section ExistingModels

variable [ModelCategory (D ⥤ M)] [ModelCategory (E ⥤ M)]

example (hWD : weakEquivalences (D ⥤ M) = (weakEquivalences M).functorCategory D)
    (hWE : weakEquivalences (E ⥤ M) = (weakEquivalences M).functorCategory E) (u : D ⥤ E) :
    weakEquivalences (E ⥤ M) ≤
      (weakEquivalences (D ⥤ M)).inverseImage ((whiskeringLeft D E M).obj u) :=
  FunctorProjective.Restriction.preserves_weakEquivalences_of_eqs hWD hWE u

example (hFD : fibrations (D ⥤ M) = (fibrations M).functorCategory D)
    (hFE : fibrations (E ⥤ M) = (fibrations M).functorCategory E)
    (hTD : trivialFibrations (D ⥤ M) = (trivialFibrations M).functorCategory D)
    (hTE : trivialFibrations (E ⥤ M) = (trivialFibrations M).functorCategory E) (u : D ⥤ E) :
    PreservesFibrations ((whiskeringLeft D E M).obj u) ∧
      PreservesTrivialFibrations ((whiskeringLeft D E M).obj u) :=
  FunctorProjective.Restriction.preserves_right_classes_of_eqs hFD hFE hTD hTE u

end ExistingModels

section FixedData

variable {κD : Cardinal.{wD}} [Fact κD.IsRegular] [OrderBot κD.ord.ToType]
  {κE : Cardinal.{wE}} [Fact κE.IsRegular] [OrderBot κE.ord.ToType]
  [Small.{wD} D] [LocallySmall.{wD} D] [Small.{wE} E] [LocallySmall.{wE} E]
  (dD : CofibrantGenerationData M κD) (dE : CofibrantGenerationData M κE) (u : D ⥤ E)

example :
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    (weakEquivalences (E ⥤ M) ≤
      (weakEquivalences (D ⥤ M)).inverseImage ((whiskeringLeft D E M).obj u)) ∧
      PreservesFibrations ((whiskeringLeft D E M).obj u) ∧
        PreservesTrivialFibrations ((whiskeringLeft D E M).obj u) :=
  FunctorProjective.Restriction.preserves_classes dD dE u

example {X Y : E ⥤ M} (f : X ⟶ Y) :
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    weakEquivalences (E ⥤ M) f →
      weakEquivalences (D ⥤ M) (((whiskeringLeft D E M).obj u).map f) := by
  let _ : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
  let _ : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
  exact (FunctorProjective.Restriction.preserves_classes dD dE u).1 f

example {X Y : E ⥤ M} (f : X ⟶ Y) :
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    fibrations (E ⥤ M) f →
      fibrations (D ⥤ M) (((whiskeringLeft D E M).obj u).map f) := by
  let _ : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
  let _ : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
  exact (FunctorProjective.Restriction.preserves_classes dD dE u).2.1 f

example {X Y : E ⥤ M} (f : X ⟶ Y) :
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    trivialFibrations (E ⥤ M) f →
      trivialFibrations (D ⥤ M) (((whiskeringLeft D E M).obj u).map f) := by
  let _ : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
  let _ : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
  exact (FunctorProjective.Restriction.preserves_classes dD dE u).2.2 f

example {X Y : E ⥤ M} (f : X ⟶ Y) :
    (fun (d : D) => (((whiskeringLeft D E M).obj u).map f).app d) =
      fun (d : D) => f.app (u.obj d) := rfl

example (u₀ : Discrete PEmpty.{1} ⥤ E) :
    letI : ModelCategory (Discrete PEmpty.{1} ⥤ M) :=
      FunctorProjective.modelCategory.{wD} (J := Discrete PEmpty.{1}) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    PreservesFibrations ((whiskeringLeft (Discrete PEmpty.{1}) E M).obj u₀) := by
  let _ : ModelCategory (Discrete PEmpty.{1} ⥤ M) :=
    FunctorProjective.modelCategory.{wD} (J := Discrete PEmpty.{1}) dD
  let _ : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
  exact (FunctorProjective.Restriction.preserves_classes dD dE u₀).2.1

example (u₀ : Discrete ℕ ⥤ E) :
    letI : ModelCategory (Discrete ℕ ⥤ M) :=
      FunctorProjective.modelCategory.{wD} (J := Discrete ℕ) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    PreservesTrivialFibrations ((whiskeringLeft (Discrete ℕ) E M).obj u₀) := by
  let _ : ModelCategory (Discrete ℕ ⥤ M) :=
    FunctorProjective.modelCategory.{wD} (J := Discrete ℕ) dD
  let _ : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
  exact (FunctorProjective.Restriction.preserves_classes dD dE u₀).2.2

example (u₀ : SingleObj (Multiplicative ℕ) ⥤ E) :
    letI : ModelCategory (SingleObj (Multiplicative ℕ) ⥤ M) :=
      FunctorProjective.modelCategory.{wD} (J := SingleObj (Multiplicative ℕ)) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    PreservesFibrations ((whiskeringLeft (SingleObj (Multiplicative ℕ)) E M).obj u₀) := by
  let _ : ModelCategory (SingleObj (Multiplicative ℕ) ⥤ M) :=
    FunctorProjective.modelCategory.{wD} (J := SingleObj (Multiplicative ℕ)) dD
  let _ : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
  exact (FunctorProjective.Restriction.preserves_classes dD dE u₀).2.1

section Composition

variable {S : Type uS} [Category.{vS} S]
  {κS : Cardinal.{wS}} [Fact κS.IsRegular] [OrderBot κS.ord.ToType]
  [Small.{wS} S] [LocallySmall.{wS} S] (dS : CofibrantGenerationData M κS) (v : E ⥤ S)

example {X Y : S ⥤ M} (f : X ⟶ Y) :
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory.{wS} (J := S) dS
    weakEquivalences (S ⥤ M) f → weakEquivalences (D ⥤ M)
      (((whiskeringLeft D E M).obj u).map (((whiskeringLeft E S M).obj v).map f)) := by
  let _ : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
  let _ : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
  let _ : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory.{wS} (J := S) dS
  intro hf
  exact (FunctorProjective.Restriction.preserves_classes dD dE u).1 _
    ((FunctorProjective.Restriction.preserves_classes dE dS v).1 f hf)

end Composition

section Raised

local instance : Category.{vD} (ULift.{uD + 1} D) := uliftCategory D
local instance : Category.{max (vD + 1) vD} (ULiftHom.{vD + 1} (ULift.{uD + 1} D)) :=
  @ULiftHom.category (ULift.{uD + 1} D) (inferInstance : Category.{vD} (ULift.{uD + 1} D))
local instance : Small.{wD} (ULiftHom.{vD + 1} (ULift.{uD + 1} D)) :=
  small_map (ULiftHom.objEquiv.symm.trans Equiv.ulift)
local instance : LocallySmall.{wD} (ULiftHom.{vD + 1} (ULift.{uD + 1} D)) where
  hom_small x y := by
    let _ : Small.{wD} (x.objDown.down ⟶ y.objDown.down) := LocallySmall.hom_small _ _
    exact small_map Equiv.ulift
local instance : Category.{vE} (ULift.{uE + 1} E) := uliftCategory E
local instance : Category.{max (vE + 1) vE} (ULiftHom.{vE + 1} (ULift.{uE + 1} E)) :=
  @ULiftHom.category (ULift.{uE + 1} E) (inferInstance : Category.{vE} (ULift.{uE + 1} E))
local instance : Small.{wE} (ULiftHom.{vE + 1} (ULift.{uE + 1} E)) :=
  small_map (ULiftHom.objEquiv.symm.trans Equiv.ulift)
local instance : LocallySmall.{wE} (ULiftHom.{vE + 1} (ULift.{uE + 1} E)) where
  hom_small x y := by
    let _ : Small.{wE} (x.objDown.down ⟶ y.objDown.down) := LocallySmall.hom_small _ _
    exact small_map Equiv.ulift

example (u₀ : ULiftHom.{vD + 1} (ULift.{uD + 1} D) ⥤ ULiftHom.{vE + 1} (ULift.{uE + 1} E)) :
    letI : ModelCategory (ULiftHom.{vD + 1} (ULift.{uD + 1} D) ⥤ M) :=
      FunctorProjective.modelCategory.{wD} (J := ULiftHom.{vD + 1} (ULift.{uD + 1} D)) dD
    letI : ModelCategory (ULiftHom.{vE + 1} (ULift.{uE + 1} E) ⥤ M) :=
      FunctorProjective.modelCategory.{wE} (J := ULiftHom.{vE + 1} (ULift.{uE + 1} E)) dE
    PreservesFibrations ((whiskeringLeft _ _ M).obj u₀) := by
  let _ : ModelCategory (ULiftHom.{vD + 1} (ULift.{uD + 1} D) ⥤ M) :=
    FunctorProjective.modelCategory.{wD} (J := ULiftHom.{vD + 1} (ULift.{uD + 1} D)) dD
  let _ : ModelCategory (ULiftHom.{vE + 1} (ULift.{uE + 1} E) ⥤ M) :=
    FunctorProjective.modelCategory.{wE} (J := ULiftHom.{vE + 1} (ULift.{uE + 1} E)) dE
  exact (FunctorProjective.Restriction.preserves_classes dD dE u₀).2.1

end Raised
end FixedData
end MathlibExtTest.FunctorProjectiveRestriction
