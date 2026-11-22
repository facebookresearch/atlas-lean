/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Whiskering
public import MathlibExt.CategoryTheory.Action.Arrow
public import MathlibExt.CategoryTheory.Monoidal.EquivariantProfileCells
public import MathlibExt.CategoryTheory.Operad.Tensor.EnvelopingAttachmentFiltration

/-!
# The original operadic profile cells as coefficient orbit cells

The actual coefficient of every original colored operad profile is retained
as an arbitrary equivariant tensor coefficient. The whole original balanced
pushout-product arrow is identified with its supported coefficient orbit.
Both original quotient projections, every original caller cofan, and its
boundary and top maps are preserved by these comparisons.

These maps compare the actual enveloping attachment cells; they do not require
cofibrant operad coefficients or supply a filtration as an extra hypothesis.
-/

@[expose] public section

open CategoryTheory.OperadicOrbitCells.ProfileGeometry

section CoefficientActionFunctor

/-!
## Functorial coefficient tensors of complete Arrow actions
-/


set_option autoImplicit false

noncomputable section

universe uj vj ug u v

namespace CategoryTheory.OperadicOrbitCells

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalCategory
open ProfileGeometry

variable {C : Type u} [Category.{v} C]


variable {G : Type ug} [Group G]



variable [MonoidalCategory C]

/-- Tensoring an arbitrary original coefficient is functorial on entire equivariant arrows. -/
def coefficientArrowActionFunctor (Y : Action C G) :
    Action (Arrow C) G ⥤ Action (Arrow C) G :=
  actionArrowFunctor ⋙ (tensorLeft Y).mapArrow ⋙ arrowActionFunctor

/-- The whole functor object retains the actual diagonal coefficient/input action. -/
theorem coefficientArrowActionFunctor_obj (Y : Action C G) (A : Action (Arrow C) G) :
    (coefficientArrowActionFunctor Y).obj A = coefficientArrowAction Y A := rfl

/-- The original complete action iso is preserved by the actual coefficient tensor functor. -/
def coefficientArrowActionIso (Y : Action C G) {A B : Action (Arrow C) G} (e : A ≅ B) :
    coefficientArrowAction Y A ≅ coefficientArrowAction Y B :=
  (coefficientArrowActionFunctor Y).mapIso e

variable [HasColimitsOfShape (SingleObj G) C]


/-- The actual diagonal coefficient action has precisely the original coefficient orbit arrow. -/
theorem arrowActionOrbitFunctor_coefficient (Y : Action C G) (A : Action (Arrow C) G) :
    arrowActionOrbitFunctor.obj (coefficientArrowAction Y A) =
      coefficientOrbitArrow Y (Action.actionUnderlyingHom A) := rfl

end CategoryTheory.OperadicOrbitCells

end
end CoefficientActionFunctor

section OrbitCofans

/-!
## Both actual quotient projections under a full action-arrow morphism
-/


set_option autoImplicit false

noncomputable section

universe ug u v

namespace CategoryTheory.OperadicOrbitCells

open CategoryTheory Limits MonoidalCategory ProfileGeometry

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {G : Type ug} [Group G] [HasColimitsOfShape (SingleObj G) C]

/-- The actual original whole action arrow has its original group transformation. -/
def bareActionTransformation (A : Action (Arrow C) G) :
    (Action.functorCategoryEquivalence C G).functor.obj (Action.leftActionFunctor.obj A) ⟶
      (Action.functorCategoryEquivalence C G).functor.obj (Action.rightActionFunctor.obj A) :=
  (Action.functorCategoryEquivalence C G).functor.map (Action.actionUnderlyingHom A)

/-- The two actual original orbit projections form its whole original Arrow cocone. -/
def bareActionOrbitCocone (A : Action (Arrow C) G) :
    Cocone (naturalArrowFunctor (bareActionTransformation A)) :=
  naturalArrowCocone (bareActionTransformation A)

/-- The original full Arrow universal property follows from the two
actual orbit universal properties. -/
def bareActionOrbitIsColimit (A : Action (Arrow C) G) :
    IsColimit (bareActionOrbitCocone A) :=
  naturalArrowIsColimit (bareActionTransformation A)

omit [MonoidalCategory C] in
/-- The actual whole original quotient cofan is natural in every original action-arrow morphism. -/
theorem bareActionOrbitCocone_naturality {A B : Action (Arrow C) G} (f : A ⟶ B) :
    (bareActionOrbitCocone A).ι.app (SingleObj.star G) ≫ arrowActionOrbitFunctor.map f =
      f.hom ≫ (bareActionOrbitCocone B).ι.app (SingleObj.star G) := by
  apply Arrow.hom_ext
  · exact ι_colimMap
      ((Action.functorCategoryEquivalence C G).functor.map (Action.leftActionFunctor.map f))
      (SingleObj.star G)
  · exact ι_colimMap
      ((Action.functorCategoryEquivalence C G).functor.map (Action.rightActionFunctor.map f))
      (SingleObj.star G)

end CategoryTheory.OperadicOrbitCells

end
end OrbitCofans

section CoefficientTensor

/-!
## The original A5 operad coefficient as an arbitrary equivariant tensor coefficient
-/


set_option autoImplicit false

noncomputable section

universe uc u v

namespace CategoryTheory.OperadicOrbitCells.A5Comparison

open CategoryTheory Limits MonoidalCategory Operad
open scoped MonoidalCategory
open Operad.Tensor.InitialAttachment

attribute [local instance] FintypeCat.fintype

variable {W : Type uc}

/-- Every original input-set vertex has exactly the original full coefficient profile. -/
theorem originalInputProfile_obj (P : ColoredProfile W) (S : ProfileInputSets P) :
    (markedProfileFunctor P.outputColor).obj ((originalInputCube P).obj S) = P := rfl

/-- An original face inclusion acts as the identity on the original full coefficient profile. -/
theorem originalInputProfile_face (P : ColoredProfile W)
    {S T : ProfileInputSets P} (f : S ⟶ T) :
    (markedProfileFunctor P.outputColor).map ((originalInputCube P).map f) = 𝟙 P := by
  apply ColoredProfile.Hom.ext
  rfl

/-- Every original input permutation acts on the original coefficient by that same profile map. -/
theorem originalInputProfile_aut (P : ColoredProfile W) (g : Aut P)
    (S : ProfileInputSets P) :
    (markedProfileFunctor P.outputColor).map (profileAutInputVertexIso P g S).hom =
      g.asIso.hom := by
  apply ColoredProfile.Hom.ext
  rfl

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- Use the finite tensor constructed from the original symmetric monoidal structure. -/
local instance binaryProfileFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C

/-- The original full operad profile has its actual original arbitrary coefficient action. -/
def operadCoefficientAction (E : ColoredOperadObj W C) (P : ColoredProfile W) :
    Action C (Aut P) :=
  Action.mk (E.toCollection.obj P) (Aut.toEnd.comp (Functor.mapAut P E.toCollection))

/-- The coefficient action retains the same original E profile map, not a cofibrant replacement. -/
theorem operadCoefficientAction_map (E : ColoredOperadObj W C) (P : ColoredProfile W)
    (g : Aut P) :
    ((operadCoefficientAction E P).ρ g).asHom = E.toCollection.map g.asIso.hom := rfl

/-- The original A5 coefficient-free input diagram retains its original marked carrier. -/
def originalInputTensorDiagram {X Xprime : W → C} (x : X ⟶ Xprime) : MarkedInputs W ⥤ C :=
  FiniteFamily.map (markedInputCarrier x) ⋙ FiniteTensor.tensor

/-- The promoted generic input diagram retains the exact original object and every original map. -/
theorem originalInputTensorDiagram_eq {X Xprime : W → C} (x : X ⟶ Xprime) :
    originalInputTensorDiagram x = CategoryTheory.OperadicOrbitCells.inputTensorDiagram x := rfl

/-- All original E coefficient and input morphisms tensor through the same whole source diagram. -/
def markedBinaryTensorIso (E : ColoredOperadObj W C) {X Xprime : W → C}
    (x : X ⟶ Xprime) (d : W) :
    markedTensorDiagram E x d ≅
      (markedProfileFunctor d ⋙ E.toCollection) ⊗ originalInputTensorDiagram x :=
  NatIso.ofComponents
    (fun M => coefficientBinaryTensorIso
      ((markedProfileFunctor d ⋙ E.toCollection).obj M)
      ((FiniteFamily.map (markedInputCarrier x)).obj M))
    (fun f => coefficientBinaryTensorIso_naturality
      ((markedProfileFunctor d ⋙ E.toCollection).map f)
      ((FiniteFamily.map (markedInputCarrier x)).map f))

/-- At an original profile vertex the coefficient is the actual E(P) object. -/
def coefficientVertexIso (E : ColoredOperadObj W C) {X Xprime : W → C}
    (x : X ⟶ Xprime) (P : ColoredProfile W) (S : ProfileInputSets P) :
    (markedTensorDiagram E x P.outputColor).obj ((originalInputCube P).obj S) ≅
      E.toCollection.obj P ⊗ (originalInputTensorDiagram x).obj ((originalInputCube P).obj S) :=
  (markedBinaryTensorIso E x P.outputColor).app ((originalInputCube P).obj S)

/-- Every original input-set face keeps its original E(P) coefficient and its original x map. -/
theorem coefficientVertexIso_face (E : ColoredOperadObj W C) {X Xprime : W → C}
    (x : X ⟶ Xprime) (P : ColoredProfile W) {S T : ProfileInputSets P} (f : S ⟶ T) :
    (markedTensorDiagram E x P.outputColor).map ((originalInputCube P).map f) ≫
        (coefficientVertexIso E x P T).hom =
      (coefficientVertexIso E x P S).hom ≫
        (E.toCollection.obj P ◁
          (originalInputTensorDiagram x).map ((originalInputCube P).map f)) := by
  have h := (markedBinaryTensorIso E x P.outputColor).hom.naturality
    ((originalInputCube P).map f)
  have hc : E.toCollection.map
      ((markedProfileFunctor P.outputColor).map ((originalInputCube P).map f)) =
      𝟙 (E.toCollection.obj P) :=
    (congrArg E.toCollection.map (originalInputProfile_face P f)).trans
      (E.toCollection.map_id P)
  let l := (originalInputTensorDiagram x).map ((originalInputCube P).map f)
  have h' : (markedTensorDiagram E x P.outputColor).map ((originalInputCube P).map f) ≫
      (coefficientVertexIso E x P T).hom =
      (coefficientVertexIso E x P S).hom ≫
        (E.toCollection.map
          ((markedProfileFunctor P.outputColor).map ((originalInputCube P).map f)) ⊗ₘ l) := h
  exact h'.trans (congrArg ((coefficientVertexIso E x P S).hom ≫ ·)
    ((congrArg (fun c => c ⊗ₘ l) hc).trans (id_tensorHom _ l)))

end CategoryTheory.OperadicOrbitCells.A5Comparison

end
end CoefficientTensor

section BoundaryComparison

/-!
## Actual original A5 coefficient boundary and top tensor comparisons
-/


set_option autoImplicit false

noncomputable section

universe uc u v us

namespace CategoryTheory.OperadicOrbitCells.A5Comparison.CanonicalBoundary

open CategoryTheory Limits MonoidalCategory Operad
open scoped MonoidalCategory
open Operad.Tensor.InitialAttachment

attribute [local instance] FintypeCat.fintype

variable {W : Type uc} {C : Type u} [Category.{v} C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [HasColimitsOfSize.{us, us} C]

/-- Use the original symmetric tensor structure for the original coefficient boundary. -/
local instance boundaryFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance boundarySmallestColimits : HasColimitsOfSize.{0, 0} C where
  has_colimits_of_shape J := HasColimitsOfShape.of_essentiallySmall C J

/-- The actual original coefficient-weighted cube is the original binary coefficient tensor. -/
def coefficientInputCubeIso (E : ColoredOperadObj W C) {X Xprime : W → C}
    (x : X ⟶ Xprime) (P : ColoredProfile W) :
    geometryInputTensorCube (markedTensorDiagram E x P.outputColor) P ≅
      geometryInputTensorCube (originalInputTensorDiagram x) P ⋙
        tensorLeft (E.toCollection.obj P) :=
  NatIso.ofComponents (coefficientVertexIso E x P)
    (fun f => coefficientVertexIso_face E x P f)

/-- The same source cube comparison retains precisely every original proper face. -/
def coefficientPuncturedCubeIso (E : ColoredOperadObj W C) {X Xprime : W → C}
    (x : X ⟶ Xprime) (P : ColoredProfile W) :
    geometryPuncturedTensor (markedTensorDiagram E x P.outputColor) P ≅
      geometryPuncturedTensor (originalInputTensorDiagram x) P ⋙
        tensorLeft (E.toCollection.obj P) :=
  Functor.isoWhiskerLeft (originalPuncturedInclusion P) (coefficientInputCubeIso E x P)

/-- The actual mapped original proper-face cocone keeps the original binary coefficient tensor. -/
def coefficientBoundaryCocone (E : ColoredOperadObj W C) {X Xprime : W → C}
    (x : X ⟶ Xprime) (P : ColoredProfile W) :
    Cocone (geometryPuncturedTensor (markedTensorDiagram E x P.outputColor) P) :=
  (Cocone.precompose (coefficientPuncturedCubeIso E x P).hom).obj
    ((tensorLeft (E.toCollection.obj P)).mapCocone
      (colimit.cocone (geometryPuncturedTensor (originalInputTensorDiagram x) P)))

/-- Closedness proves preservation of this actual original proper-face colimit. -/
def coefficientBoundaryIsColimit (E : ColoredOperadObj W C) {X Xprime : W → C}
    (x : X ⟶ Xprime) (P : ColoredProfile W) :
    IsColimit (coefficientBoundaryCocone E x P) :=
  (IsColimit.precomposeHomEquiv (coefficientPuncturedCubeIso E x P)
    ((tensorLeft (E.toCollection.obj P)).mapCocone
      (colimit.cocone (geometryPuncturedTensor (originalInputTensorDiagram x) P)))).symm
    (isColimitOfPreserves (tensorLeft (E.toCollection.obj P)) (colimit.isColimit _))

/-- The actual original E coefficient boundary is the tensor of its
original plain input boundary. -/
def coefficientBoundaryIso (E : ColoredOperadObj W C) {X Xprime : W → C}
    (x : X ⟶ Xprime) (P : ColoredProfile W) :
    geometryInputBoundary (markedTensorDiagram E x P.outputColor) P ≅
      E.toCollection.obj P ⊗ geometryInputBoundary (originalInputTensorDiagram x) P :=
  (colimit.isColimit _).coconePointUniqueUpToIso (coefficientBoundaryIsColimit E x P)

/-- Every actual original proper-face coefficient map survives the boundary tensor comparison. -/
@[reassoc]
theorem coefficientBoundaryIso_face (E : ColoredOperadObj W C) {X Xprime : W → C}
    (x : X ⟶ Xprime) (P : ColoredProfile W) (S : ProfilePuncturedInputSets P) :
    colimit.ι (geometryPuncturedTensor (markedTensorDiagram E x P.outputColor) P) S ≫
        (coefficientBoundaryIso E x P).hom =
      (coefficientVertexIso E x P S.1).hom ≫
        (E.toCollection.obj P ◁
          colimit.ι (geometryPuncturedTensor (originalInputTensorDiagram x) P) S) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
    (coefficientBoundaryIsColimit E x P) S

/-- The actual original coefficient boundary and top maps form the full original Arrow square. -/
theorem coefficientBoundaryTop_square (E : ColoredOperadObj W C) {X Xprime : W → C}
    (x : X ⟶ Xprime) (P : ColoredProfile W) :
    (coefficientBoundaryIso E x P).hom ≫
        (E.toCollection.obj P ◁ geometryBoundaryToTop (originalInputTensorDiagram x) P) =
      geometryBoundaryToTop (markedTensorDiagram E x P.outputColor) P ≫
        (coefficientVertexIso E x P Finset.univ).hom := by
  let De := markedTensorDiagram E x P.outputColor
  let D := originalInputTensorDiagram x
  let Y := E.toCollection.obj P
  let F := tensorLeft Y
  apply colimit.hom_ext
  intro S
  have hL : colimit.ι (geometryPuncturedTensor De P) S ≫
      ((coefficientBoundaryIso E x P).hom ≫ F.map (geometryBoundaryToTop D P)) =
      (coefficientVertexIso E x P S.1).hom ≫
        F.map ((geometryInputTensorCube D P).map (homOfLE (Finset.subset_univ S.1))) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ F.map (geometryBoundaryToTop D P))
        (coefficientBoundaryIso_face E x P S)).trans
        ((Category.assoc _ _ _).trans
          (congrArg ((coefficientVertexIso E x P S.1).hom ≫ ·)
            ((F.map_comp _ _).symm.trans
              (congrArg F.map (geometryBoundaryToTop_face D P S))))))
  have hR : colimit.ι (geometryPuncturedTensor De P) S ≫
      (geometryBoundaryToTop De P ≫ (coefficientVertexIso E x P Finset.univ).hom) =
      (coefficientVertexIso E x P S.1).hom ≫
        F.map ((geometryInputTensorCube D P).map (homOfLE (Finset.subset_univ S.1))) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (coefficientVertexIso E x P Finset.univ).hom)
        (geometryBoundaryToTop_face De P S)).trans
        (coefficientVertexIso_face E x P (homOfLE (Finset.subset_univ S.1))))
  exact hL.trans hR.symm

/-- The full original A5 input/coefficient arrow has its actual binary coefficient Arrow iso. -/
def coefficientRawArrowIso (E : ColoredOperadObj W C) {X Xprime : W → C}
    (x : X ⟶ Xprime) (P : ColoredProfile W) :
    Arrow.mk (geometryBoundaryToTop (markedTensorDiagram E x P.outputColor) P) ≅
      (tensorLeft (E.toCollection.obj P)).mapArrow.obj
        (Arrow.mk (geometryBoundaryToTop (originalInputTensorDiagram x) P)) :=
  Arrow.isoMk (coefficientBoundaryIso E x P)
    (coefficientVertexIso E x P Finset.univ) (coefficientBoundaryTop_square E x P)

end CategoryTheory.OperadicOrbitCells.A5Comparison.CanonicalBoundary

end
end BoundaryComparison

section EquivariantComparison

/-!
## The actual A5 coefficient tensor comparison preserves both original group actions
-/


set_option autoImplicit false

noncomputable section

universe uc u v us

namespace CategoryTheory.OperadicOrbitCells.A5Comparison.CanonicalEquivariance

open CategoryTheory.OperadicOrbitCells.A5Comparison.CanonicalBoundary

open CategoryTheory Limits MonoidalCategory Operad
open scoped MonoidalCategory
open Operad.Tensor.InitialAttachment

attribute [local instance] FintypeCat.fintype

variable {W : Type uc} {C : Type u} [Category.{v} C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [HasColimitsOfSize.{us, us} C]

/-- Use the original symmetric tensor structure for both original coefficient actions. -/
local instance equivariantFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance equivariantSmallestColimits : HasColimitsOfSize.{0, 0} C where
  has_colimits_of_shape J := HasColimitsOfShape.of_essentiallySmall C J

omit [MonoidalClosed C] [HasColimitsOfSize.{us, us} C] in
/-- The original coefficient and original input permutations remain
diagonal on every original face. -/
theorem coefficientVertexIso_aut (E : ColoredOperadObj W C) {X Xprime : W → C}
    (x : X ⟶ Xprime) (P : ColoredProfile W) (g : Aut P) (S : ProfileInputSets P) :
    (markedTensorDiagram E x P.outputColor).map (profileAutInputVertexIso P g S).hom ≫
        (coefficientVertexIso E x P (profileAutSubset P g S)).hom =
      (coefficientVertexIso E x P S).hom ≫
        (((operadCoefficientAction E P).ρ g).asHom ⊗ₘ
          (originalInputTensorDiagram x).map (profileAutInputVertexIso P g S).hom) := by
  have h := (markedBinaryTensorIso E x P.outputColor).hom.naturality
    (profileAutInputVertexIso P g S).hom
  have hc := congrArg E.toCollection.map (originalInputProfile_aut P g S)
  let l := (originalInputTensorDiagram x).map (profileAutInputVertexIso P g S).hom
  have h' : (markedTensorDiagram E x P.outputColor).map (profileAutInputVertexIso P g S).hom ≫
      (coefficientVertexIso E x P (profileAutSubset P g S)).hom =
      (coefficientVertexIso E x P S).hom ≫
        (E.toCollection.map
          ((markedProfileFunctor P.outputColor).map (profileAutInputVertexIso P g S).hom) ⊗ₘ l) := h
  exact h'.trans (congrArg ((coefficientVertexIso E x P S).hom ≫ ·)
    (congrArg (fun c => c ⊗ₘ l) hc))

omit [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
    [HasColimitsOfSize.{us, us} C] in
/-- The actual full-input group map is the same original E coefficient profile map. -/
theorem originalInputProfile_topAut (P : ColoredProfile W) (g : Aut P) :
    (markedProfileFunctor P.outputColor).map (originalInputTopHom P g).asIso.hom =
      g.asIso.hom := by
  apply ColoredProfile.Hom.ext
  rfl

omit [SymmetricCategory C] [MonoidalClosed C] [HasColimitsOfSize.{us, us} C] in
private theorem tensor_whisker_comp {Y A B T : C} (y : Y ⟶ Y) (f : A ⟶ B) (j : B ⟶ T) :
    (y ⊗ₘ f) ≫ (Y ◁ j) = y ⊗ₘ (f ≫ j) := by
  rw [← id_tensorHom Y j, tensorHom_comp_tensorHom, Category.comp_id]

omit [SymmetricCategory C] [MonoidalClosed C] [HasColimitsOfSize.{us, us} C] in
private theorem whisker_tensor_comp {Y A B T : C} (j : A ⟶ B) (y : Y ⟶ Y) (f : B ⟶ T) :
    (Y ◁ j) ≫ (y ⊗ₘ f) = y ⊗ₘ (j ≫ f) := by
  rw [← id_tensorHom Y j, tensorHom_comp_tensorHom, Category.id_comp]

/-- The actual boundary coefficient comparison preserves the original diagonal group action. -/
theorem coefficientBoundaryIso_aut (E : ColoredOperadObj W C) {X Xprime : W → C}
    (x : X ⟶ Xprime) (P : ColoredProfile W) (g : Aut P) :
    geometryAutMap (markedTensorDiagram E x P.outputColor) P g ≫
        (coefficientBoundaryIso E x P).hom =
      (coefficientBoundaryIso E x P).hom ≫
        (((operadCoefficientAction E P).ρ g).asHom ⊗ₘ
          geometryAutMap (originalInputTensorDiagram x) P g) := by
  let De := markedTensorDiagram E x P.outputColor
  let D := originalInputTensorDiagram x
  let Y := E.toCollection.obj P
  let y := ((operadCoefficientAction E P).ρ g).asHom
  apply colimit.hom_ext
  intro S
  let Sg := (profileAutPunctured P g).obj S
  let j := colimit.ι (geometryPuncturedTensor D P) S
  let jg := colimit.ι (geometryPuncturedTensor D P) Sg
  let v := (profileAutInputVertexIso P g S.1).hom
  have hL : colimit.ι (geometryPuncturedTensor De P) S ≫
      (geometryAutMap De P g ≫ (coefficientBoundaryIso E x P).hom) =
      (coefficientVertexIso E x P S.1).hom ≫ (y ⊗ₘ (D.map v ≫ jg)) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (coefficientBoundaryIso E x P).hom) (geometryAutMap_face De P g S)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (De.map v ≫ ·) (coefficientBoundaryIso_face E x P Sg)).trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (· ≫ (Y ◁ jg)) (coefficientVertexIso_aut E x P g S.1)).trans
                ((Category.assoc _ _ _).trans
                  (congrArg ((coefficientVertexIso E x P S.1).hom ≫ ·)
                    (tensor_whisker_comp y (D.map v) jg))))))))
  have hR : colimit.ι (geometryPuncturedTensor De P) S ≫
      ((coefficientBoundaryIso E x P).hom ≫ (y ⊗ₘ geometryAutMap D P g)) =
      (coefficientVertexIso E x P S.1).hom ≫ (y ⊗ₘ (j ≫ geometryAutMap D P g)) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (y ⊗ₘ geometryAutMap D P g)) (coefficientBoundaryIso_face E x P S)).trans
        ((Category.assoc _ _ _).trans
          (congrArg ((coefficientVertexIso E x P S.1).hom ≫ ·)
            (whisker_tensor_comp j y (geometryAutMap D P g)))))
  exact hL.trans ((congrArg ((coefficientVertexIso E x P S.1).hom ≫ ·)
    (congrArg (fun a => y ⊗ₘ a) (geometryAutMap_face D P g S).symm)).trans hR.symm)

omit [MonoidalClosed C] [HasColimitsOfSize.{us, us} C] in
/-- The actual top coefficient comparison preserves the same original diagonal group action. -/
theorem coefficientTopIso_aut (E : ColoredOperadObj W C) {X Xprime : W → C}
    (x : X ⟶ Xprime) (P : ColoredProfile W) (g : Aut P) :
    (geometryInputTopRepresentation (markedTensorDiagram E x P.outputColor) P g).asHom ≫
        (coefficientVertexIso E x P Finset.univ).hom =
      (coefficientVertexIso E x P Finset.univ).hom ≫
        (((operadCoefficientAction E P).ρ g).asHom ⊗ₘ
          (geometryInputTopRepresentation (originalInputTensorDiagram x) P g).asHom) := by
  have h := (markedBinaryTensorIso E x P.outputColor).hom.naturality
    (originalInputTopHom P g).asIso.hom
  have hc := congrArg E.toCollection.map (originalInputProfile_topAut P g)
  let l := (originalInputTensorDiagram x).map (originalInputTopHom P g).asIso.hom
  have h' : (markedTensorDiagram E x P.outputColor).map (originalInputTopHom P g).asIso.hom ≫
      (coefficientVertexIso E x P Finset.univ).hom =
      (coefficientVertexIso E x P Finset.univ).hom ≫
        (E.toCollection.map ((markedProfileFunctor P.outputColor).map
          (originalInputTopHom P g).asIso.hom) ⊗ₘ l) := h
  exact h'.trans (congrArg ((coefficientVertexIso E x P Finset.univ).hom ≫ ·)
    (congrArg (fun c => c ⊗ₘ l) hc))

/-- The original full A5 coefficient/input action has the actual arbitrary-coefficient Arrow iso. -/
def operadCoefficientRawActionIso (E : ColoredOperadObj W C) {X Xprime : W → C}
    (x : X ⟶ Xprime) (P : ColoredProfile W) :
    rawGeometryArrowAction (markedTensorDiagram E x P.outputColor) P ≅
      coefficientArrowAction (operadCoefficientAction E P)
        (rawGeometryArrowAction (originalInputTensorDiagram x) P) :=
  Action.mkIso (coefficientRawArrowIso E x P) (by
    intro g
    apply Arrow.hom_ext
    · exact coefficientBoundaryIso_aut E x P g
    · exact coefficientTopIso_aut E x P g)

end CategoryTheory.OperadicOrbitCells.A5Comparison.CanonicalEquivariance

end
end EquivariantComparison

section OrbitComparison

/-!
## The actual A5 operad coefficient orbit and every original caller cofan
-/


set_option autoImplicit false

noncomputable section

universe uc u v us

namespace CategoryTheory.OperadicOrbitCells.A5Comparison.CanonicalOrbit

open CategoryTheory.OperadicOrbitCells.A5Comparison.CanonicalEquivariance

open CategoryTheory Limits MonoidalCategory Operad
open Operad.Tensor.InitialAttachment Operad.Tensor.InitialAttachment.ProfileCells

attribute [local instance] FintypeCat.fintype

variable {W : Type uc} {C : Type u} [Category.{v} C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [HasColimitsOfSize.{us, us} C]

/-- Use the original symmetric tensor structure for the actual coefficient orbit comparison. -/
local instance orbitComparisonFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance orbitComparisonSmallestColimits : HasColimitsOfSize.{0, 0} C where
  has_colimits_of_shape J := HasColimitsOfShape.of_essentiallySmall C J
local instance orbitComparisonAutColimits (P : ColoredProfile W) :
    HasColimitsOfShape (SingleObj (Aut P)) C :=
  HasColimitsOfShape.of_essentiallySmall C _

/-- The full original operad coefficient action is the arbitrary-coefficient actual PP action. -/
def operadCoefficientPPActionIso (E : ColoredOperadObj W C) {X Xprime : W → C}
    (x : X ⟶ Xprime) (P : ColoredProfile W) :
    rawGeometryArrowAction (markedTensorDiagram E x P.outputColor) P ≅
      coefficientArrowAction (operadCoefficientAction E P) (profilePushoutProductAction x P) := by
  have ep : rawGeometryArrowAction (originalInputTensorDiagram x) P ≅
      profilePushoutProductAction x P :=
    Action.transportArrowActionIso (rawProfileArrowAction x P) (inputPushoutProductIso x P)
  exact operadCoefficientRawActionIso E x P ≪≫
    coefficientArrowActionIso (operadCoefficientAction E P) ep

/-- The actual original A5 profile quotient is the actual arbitrary-coefficient PP orbit Arrow. -/
def operadCoefficientOrbitIso (E : ColoredOperadObj W C) {X Xprime : W → C}
    (x : X ⟶ Xprime) (P : ColoredProfile W) :
    balancedProfileArrow E x P ≅
      profileIteratedOrbitArrow x P (operadCoefficientAction E P) :=
  arrowActionOrbitFunctor.mapIso (operadCoefficientPPActionIso E x P)

/-- Both original quotient projections retain the entire actual coefficient PP action map. -/
theorem operadCoefficientOrbitIso_cofan (E : ColoredOperadObj W C) {X Xprime : W → C}
    (x : X ⟶ Xprime) (P : ColoredProfile W) :
    (bareActionOrbitCocone (rawGeometryArrowAction (markedTensorDiagram E x P.outputColor) P)).ι.app
        (SingleObj.star (Aut P)) ≫ (operadCoefficientOrbitIso E x P).hom =
      (operadCoefficientPPActionIso E x P).hom.hom ≫
        (profileIteratedOrbitCocone x P (operadCoefficientAction E P)).ι.app
          (SingleObj.star (Aut P)) :=
  bareActionOrbitCocone_naturality (operadCoefficientPPActionIso E x P).hom

section Caller

variable [Small.{us} W]

/-- The original caller receives the actual arbitrary-coefficient PP orbit through the same map. -/
def operadCoefficientCallerCofan (E : ColoredOperadObj W C) {X Xprime : W → C}
    (x : X ⟶ Xprime) (P : ColoredProfile W) :
    profileIteratedOrbitArrow x P (operadCoefficientAction E P) ⟶
      degreeBalancedArrow E x P.outputColor (inputCount P) :=
  (operadCoefficientOrbitIso E x P).inv ≫ callerProfileCellCofan E x P

/-- The complete source and target caller cofans are retained through the full Arrow iso. -/
theorem operadCoefficientCallerCofan_fac (E : ColoredOperadObj W C) {X Xprime : W → C}
    (x : X ⟶ Xprime) (P : ColoredProfile W) :
    (operadCoefficientOrbitIso E x P).hom ≫ operadCoefficientCallerCofan E x P =
      callerProfileCellCofan E x P :=
  (operadCoefficientOrbitIso E x P).hom_inv_id_assoc _

end Caller

end CategoryTheory.OperadicOrbitCells.A5Comparison.CanonicalOrbit

end
end OrbitComparison

section SupportedCells

/-!
## Every original positive A5 cell is an actual arbitrary-coefficient supported orbit cell
-/


set_option autoImplicit false

noncomputable section

universe uc u v us

namespace CategoryTheory.OperadicOrbitCells.A5Comparison.CanonicalSupported

open CategoryTheory.OperadicOrbitCells.A5Comparison.CanonicalOrbit

open CategoryTheory Limits MonoidalCategory Operad
open Operad.Tensor.InitialAttachment Operad.Tensor.InitialAttachment.ProfileCells

attribute [local instance] FintypeCat.fintype

variable {W : Type uc} {C : Type u} [Category.{v} C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [HasColimitsOfSize.{us, us} C]

/-- Use the original symmetric tensor structure for every actual supported operad cell. -/
local instance supportedCellsFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance supportedCellsSmallestColimits : HasColimitsOfSize.{0, 0} C where
  has_colimits_of_shape J := HasColimitsOfShape.of_essentiallySmall C J
local instance supportedCellsAutColimits (P : ColoredProfile W) :
    HasColimitsOfShape (SingleObj (Aut P)) C :=
  HasColimitsOfShape.of_essentiallySmall C _

/-- The entire original positive operad orbit Arrow is a literal supported coefficient orbit. -/
def operadProfileFamilyOrbitIso (E : ColoredOperadObj W C) {X Xprime : W → C}
    (x : X ⟶ Xprime) (P : ColoredProfile W) (hP : 0 < inputCount P) :
    balancedProfileArrow E x P ≅
      familyOrbitArrow (profilePositiveOrbitFamily x P hP (operadCoefficientAction E P)) :=
  operadCoefficientOrbitIso E x P ≪≫
    profileFamilyOrbitIso x P hP (operadCoefficientAction E P)

/-- Every actual original positive operad cell belongs to the conventional global orbit class. -/
theorem operadProfileArrow_mem_isoClosure (Q : MorphismProperty C)
    (E : ColoredOperadObj W C) {X Xprime : W → C} (x : X ⟶ Xprime)
    (P : ColoredProfile W) (hP : 0 < inputCount P)
    (hx : ∀ i : P.inputs, Q (x (P.inputColor i))) :
    (orbitGenerators Q).isoClosure (balancedProfileArrow E x P).hom :=
  ((orbitGenerators Q).isoClosure.arrow_iso_iff (operadCoefficientOrbitIso E x P)).2
    (profileIteratedOrbitArrow_mem_isoClosure Q x P hP (operadCoefficientAction E P) hx)

section Caller

variable [Small.{us} W]

local instance supportedCellsDegreeColimits (n : ℕ) :
    HasColimitsOfShape (DegreeMarkedInputs W n) C :=
  HasColimitsOfShape.of_essentiallySmall C _
local instance supportedCellsPuncturedColimits (n : ℕ) :
    HasColimitsOfShape (PuncturedMarkedInputs W n) C :=
  HasColimitsOfShape.of_essentiallySmall C _

/-- The literal supported orbit cell has the actual original caller degree cofan. -/
def operadFamilyCallerCofan (E : ColoredOperadObj W C) {X Xprime : W → C}
    (x : X ⟶ Xprime) (P : ColoredProfile W) (hP : 0 < inputCount P) :
    familyOrbitArrow (profilePositiveOrbitFamily x P hP (operadCoefficientAction E P)) ⟶
      degreeBalancedArrow E x P.outputColor (inputCount P) :=
  (operadProfileFamilyOrbitIso E x P hP).inv ≫ callerProfileCellCofan E x P

/-- Both original caller cofans retain the original full Arrow through the supported-cell iso. -/
theorem operadFamilyCallerCofan_fac (E : ColoredOperadObj W C) {X Xprime : W → C}
    (x : X ⟶ Xprime) (P : ColoredProfile W) (hP : 0 < inputCount P) :
    (operadProfileFamilyOrbitIso E x P hP).hom ≫ operadFamilyCallerCofan E x P hP =
      callerProfileCellCofan E x P :=
  (operadProfileFamilyOrbitIso E x P hP).hom_inv_id_assoc _

/-- Each original proper face keeps its actual original tensor map and original quotient leg. -/
theorem operadFamilyCallerCofan_boundary_face (E : ColoredOperadObj W C) {X Xprime : W → C}
    (x : X ⟶ Xprime) (P : ColoredProfile W) (hP : 0 < inputCount P)
    (S : FullProfilePunctured P) :
    (fullProfileBoundaryCocone (markedTensorDiagram E x P.outputColor) P).ι.app S ≫
        ((operadProfileFamilyOrbitIso E x P hP).hom.left ≫
          (operadFamilyCallerCofan E x P hP).left) =
      (markedTensorDiagram E x P.outputColor).map
          (profileInverseVertex (callerRepresentativeIso P) S.1) ≫
        colimit.ι (puncturedMarkedTensorDiagram E x P.outputColor (inputCount P))
          (representativePuncturedVertex (callerClass P) (callerBoundarySubset P S)) := by
  have hf := congrArg Arrow.Hom.left (operadFamilyCallerCofan_fac E x P hP)
  exact (congrArg ((fullProfileBoundaryCocone (markedTensorDiagram E x P.outputColor) P).ι.app
    S ≫ ·) hf).trans (callerProfileCellCofan_boundary_face E x P S)

/-- Every full vertex keeps its original top tensor map and original degree quotient leg. -/
theorem operadFamilyCallerCofan_top_face (E : ColoredOperadObj W C) {X Xprime : W → C}
    (x : X ⟶ Xprime) (P : ColoredProfile W) (hP : 0 < inputCount P) (S : FullProfileCube P) :
    (fullProfileTopCocone (markedTensorDiagram E x P.outputColor) P).ι.app S ≫
        ((operadProfileFamilyOrbitIso E x P hP).hom.right ≫
          (operadFamilyCallerCofan E x P hP).right) =
      (markedTensorDiagram E x P.outputColor).map
          (profileInverseVertex (callerRepresentativeIso P) S) ≫
        (degreeToTop E x P.outputColor (inputCount P)).app
          (representativeVertex (callerClass P) (callerVertexSubset P S)) ≫
        colimit.ι (degreeTopTensorDiagram E x P.outputColor (inputCount P))
          (representativeVertex (callerClass P) (callerVertexSubset P S)) := by
  have hf := congrArg Arrow.Hom.right (operadFamilyCallerCofan_fac E x P hP)
  exact (congrArg ((fullProfileTopCocone (markedTensorDiagram E x P.outputColor) P).ι.app
    S ≫ ·) hf).trans (callerProfileCellCofan_top_face E x P S)

end Caller

end CategoryTheory.OperadicOrbitCells.A5Comparison.CanonicalSupported

end
end SupportedCells
