/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.DerivedAmbientComputation
public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedTensorConstructions

/-!
# The original three-variable source of the derived module associator

Both source brackets retain the actual base and module Q functors. The
original outer Q counits give whole natural contractions, proved invertible
by the earned ambient Brown laws. The actual linear module associator then
gives the complete source natural isomorphism in both coefficients and the
original module variable.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v wA wC

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MorphismProperty Functor
open scoped CategoryTheory.MonObj MonoidalCategory

namespace HomotopicalAlgebra.ModuleTransfer.DerivedAmbientAction

variable {C : Type u} [Category.{v} C] [ModelCategory C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C]
  {A : C} [MonObj A] {I J : MorphismProperty C}
  {κA : Cardinal.{wA}} [Fact κA.IsRegular] [OrderBot κA.ord.ToType]
  (tA : RightTransfer.OriginalRankModelTransfer (Mod.free A) (Mod.forget (D := C) A) I J κA)
  {κC : Cardinal.{wC}} [Fact κC.IsRegular] [OrderBot κC.ord.ToType]
  (dC : CofibrantGenerationData C κC)

open CategoryTheory.HomogeneousLocalization
open CategoryTheory.HomogeneousLocalization.AmbientTensorHom

local notation "qA" => tA.replacements
local notation "qC" => GeneratedFunctorialReplacements.fromGeneration dC
local notation "M" => Mod C A
local notation "WA" => moduleWeak tA
local notation "HA" => MorphismProperty.Localization WA
local notation "πA" => MorphismProperty.Q WA

/-- The actual outer coefficient is left unreplaced while the original module Q is retained. -/
def leftOuter : C ⥤ M ⥤ M := by
  letI : ModelCategory M := tA.model
  exact leftBifunctor A ⋙ (whiskeringLeft M M M).obj (qA).Q

/-- The actual original coefficient Q is retained while the outer module is left unreplaced. -/
def rightOuter : C ⥤ M ⥤ M := (qC).Q ⋙ leftBifunctor A

/-- The original coefficient Q counit gives the whole outer left contraction. -/
def leftOuterContraction : replaced tA dC ⟶ leftOuter tA := by
  letI : ModelCategory M := tA.model
  exact whiskerRight (whiskerRight (qC).q (leftBifunctor A))
    ((whiskeringLeft M M M).obj (qA).Q) ≫
      (isoWhiskerRight (leftBifunctor A).leftUnitor ((whiskeringLeft M M M).obj (qA).Q)).hom

/-- The original module Q counit gives the whole outer right contraction. -/
def rightOuterContraction : replaced tA dC ⟶ rightOuter (A := A) dC := by
  letI : ModelCategory M := tA.model
  exact whiskerLeft ((qC).Q ⋙ leftBifunctor A) ((whiskeringLeft M M M).map (qA).q) ≫
    ((qC).Q ⋙ leftBifunctor A).rightUnitor.hom

/-- The complete left source bracket uses the actual chosen base QQ tensor and original module Q. -/
def rawLeftBracket : C ⥤ C ⥤ M ⥤ HA :=
  (postcompose₃.obj πA).obj
    (bifunctorComp₁₂ (DerivedTensorConstructions.replacedTensor (qC)) (replaced tA dC))

/-- The complete right source bracket uses the two original actual module action replacements. -/
def rawRightBracket : C ⥤ C ⥤ M ⥤ HA :=
  (postcompose₃.obj πA).obj (bifunctorComp₂₃ (replaced tA dC) (replaced tA dC))

/-- The ordinary left tensor word retains the same actual two coefficient and one module Q objects. -/
def actualLeftBracket : C ⥤ C ⥤ M ⥤ HA :=
  (postcompose₃.obj πA).obj
    (bifunctorComp₁₂ (DerivedTensorConstructions.replacedTensor (qC)) (leftOuter tA))

/-- The ordinary right tensor word retains those same original three Q objects. -/
def actualRightBracket : C ⥤ C ⥤ M ⥤ HA :=
  (postcompose₃.obj πA).obj
    (bifunctorComp₂₃ (rightOuter (A := A) dC) (replaced tA dC))

/-- The complete outer coefficient contraction is natural in all three original source variables. -/
def leftBracketContraction : rawLeftBracket tA dC ⟶ actualLeftBracket tA dC :=
  (postcompose₃.obj πA).map
    ((bifunctorComp₁₂Functor.obj (DerivedTensorConstructions.replacedTensor (qC))).map
      (leftOuterContraction tA dC))

/-- The complete outer module contraction is natural in all three original source variables. -/
def rightBracketContraction : rawRightBracket tA dC ⟶ actualRightBracket tA dC :=
  (postcompose₃.obj πA).map
    ((bifunctorComp₂₃Functor.map (rightOuterContraction tA dC)).app (replaced tA dC))

omit [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The left contraction is exactly the original coefficient Q counit tensored with the module Q object. -/
theorem leftBracketContraction_app (U V : C) (N : M) :
    letI : ModelCategory M := tA.model
    (((leftBracketContraction tA dC).app U).app V).app N =
      (πA).map ((AmbientBrown.coefficientFunctor ((qA).Q.obj N)).map
        ((qC).q.app ((qC).Q.obj U ⊗ (qC).Q.obj V))) := by
  let : ModelCategory M := tA.model
  dsimp [leftBracketContraction, leftOuterContraction, replaced,
    DerivedTensorConstructions.replacedTensor]
  simp
  rfl

omit [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The right contraction is exactly the original module Q counit under the original coefficient Q. -/
theorem rightBracketContraction_app (U V : C) (N : M) :
    letI : ModelCategory M := tA.model
    (((rightBracketContraction tA dC).app U).app V).app N =
      (πA).map ((Mod.AmbientTensor.functor A ((qC).Q.obj U)).map
        ((qA).q.app (Mod.AmbientTensor.tensorModule A ((qC).Q.obj V) ((qA).Q.obj N)))) := by
  let : ModelCategory M := tA.model
  dsimp [rightBracketContraction, rightOuterContraction, replaced]
  simp
  rfl

/-- Actual coefficient Brown preservation proves invertibility of the whole original left contraction. -/
theorem leftBracketContraction_isIso (U V : C) (N : M) :
    IsIso ((((leftBracketContraction tA dC).app U).app V).app N) := by
  let : ModelCategory M := tA.model
  rw [leftBracketContraction_app]
  let : IsCofibrant ((qC).Q.obj U) := (qC).q_cofibrant U
  let : IsCofibrant ((qC).Q.obj V) := (qC).q_cofibrant V
  let pp := IsClosedSymmetricMonoidalModelCategory.pushoutProductAxiom (C := C)
  let : IsCofibrant ((qC).Q.obj U ⊗ (qC).Q.obj V) := pp.isCofibrant_tensorObj _ _
  let : IsCofibrant ((𝟭 C).obj ((qC).Q.obj U ⊗ (qC).Q.obj V)) :=
    (inferInstance : IsCofibrant ((qC).Q.obj U ⊗ (qC).Q.obj V))
  let : IsCofibrant ((qC).Q.obj ((qC).Q.obj U ⊗ (qC).Q.obj V)) := (qC).q_cofibrant _
  let : IsCofibrant ((qA).Q.obj N) := (qA).q_cofibrant N
  have h := AmbientBrown.coefficient_weak_of_cofibrant tA.weak_eq tA.fibrations_eq
    ((qA).Q.obj N) ((qC).q.app ((qC).Q.obj U ⊗ (qC).Q.obj V)) ((qC).q_trivialFibration _).2
  exact Localization.inverts πA WA _ h

/-- Actual module Brown preservation proves invertibility of the whole original right contraction. -/
theorem rightBracketContraction_isIso (U V : C) (N : M) :
    IsIso ((((rightBracketContraction tA dC).app U).app V).app N) := by
  let : ModelCategory M := tA.model
  rw [rightBracketContraction_app]
  let : IsCofibrant ((qC).Q.obj U) := (qC).q_cofibrant U
  let : IsCofibrant ((qC).Q.obj V) := (qC).q_cofibrant V
  let : IsCofibrant ((qA).Q.obj N) := (qA).q_cofibrant N
  let : IsCofibrant (Mod.AmbientTensor.tensorModule A ((qC).Q.obj V) ((qA).Q.obj N)) :=
    tensorModule_isCofibrant tA _ _ (inferInstance : IsCofibrant ((qA).Q.obj N))
  let : IsCofibrant ((𝟭 M).obj (Mod.AmbientTensor.tensorModule A ((qC).Q.obj V) ((qA).Q.obj N))) :=
    (inferInstance : IsCofibrant (Mod.AmbientTensor.tensorModule A ((qC).Q.obj V) ((qA).Q.obj N)))
  let : IsCofibrant ((qA).Q.obj (Mod.AmbientTensor.tensorModule A ((qC).Q.obj V) ((qA).Q.obj N))) :=
    (qA).q_cofibrant _
  have h := AmbientBrown.module_weak_of_cofibrant tA.weak_eq tA.fibrations_eq
    ((qC).Q.obj U) ((qA).q.app (Mod.AmbientTensor.tensorModule A ((qC).Q.obj V) ((qA).Q.obj N)))
    ((qA).q_trivialFibration _).2
  exact Localization.inverts πA WA _ h

/-- The whole original left contraction is a natural isomorphism with the actual component inverses. -/
def leftBracketContractionIso : rawLeftBracket tA dC ≅ actualLeftBracket tA dC := by
  let : ∀ U V N, IsIso ((((leftBracketContraction tA dC).app U).app V).app N) :=
    leftBracketContraction_isIso tA dC
  let : ∀ U V, IsIso (((leftBracketContraction tA dC).app U).app V) :=
    fun U V => NatIso.isIso_of_isIso_app _
  let : ∀ U, IsIso ((leftBracketContraction tA dC).app U) := fun U => NatIso.isIso_of_isIso_app _
  let : IsIso (leftBracketContraction tA dC) := NatIso.isIso_of_isIso_app _
  exact asIso (leftBracketContraction tA dC)

/-- The whole original right contraction is a natural isomorphism with the actual component inverses. -/
def rightBracketContractionIso : rawRightBracket tA dC ≅ actualRightBracket tA dC := by
  let : ∀ U V N, IsIso ((((rightBracketContraction tA dC).app U).app V).app N) :=
    rightBracketContraction_isIso tA dC
  let : ∀ U V, IsIso (((rightBracketContraction tA dC).app U).app V) :=
    fun U V => NatIso.isIso_of_isIso_app _
  let : ∀ U, IsIso ((rightBracketContraction tA dC).app U) := fun U => NatIso.isIso_of_isIso_app _
  let : IsIso (rightBracketContraction tA dC) := NatIso.isIso_of_isIso_app _
  exact asIso (rightBracketContraction tA dC)

/-- The original whole linear module associator is evaluated on the same three actual Q functors. -/
def actualBracketAssociator : actualLeftBracket tA dC ≅ actualRightBracket tA dC := by
  letI : ModelCategory M := tA.model
  exact (postcompose₃.obj πA).mapIso
    (((((whiskeringLeft₃ M).obj (qC).Q).obj (qC).Q).obj (qA).Q).mapIso
      (AmbientActionPointSet.sourceAssociator (A := A)))

/-- Both original outer Q contractions and the original module associator give the whole source Iso. -/
def rawBracketAssociator : rawLeftBracket tA dC ≅ rawRightBracket tA dC :=
  leftBracketContractionIso tA dC ≪≫ actualBracketAssociator tA dC ≪≫
    (rightBracketContractionIso tA dC).symm

end HomotopicalAlgebra.ModuleTransfer.DerivedAmbientAction
