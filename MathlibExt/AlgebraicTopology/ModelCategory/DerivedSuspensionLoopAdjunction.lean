/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.PointedFramingAction
import MathlibExt.AlgebraicTopology.ModelCategory.FiniteResolutionTensor
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import MathlibExt.Topology.Category.PointedCGWH.SphereOne
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Adjunction.Unique
import MathlibExt.AlgebraicTopology.ModelCategory.CompatibleCotensorFraming
import MathlibExt.AlgebraicTopology.ModelCategory.DerivedAdjunctionCoherence
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHSimplicialEnrichment
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHSingularModel

/-!
# Ordinary suspension and loops from the actual pointed circle

The circle is the genuine quotient of the actual standard one-simplex by its
entire boundary. Its pointed framing tensor and cotensor produce ordinary
suspension and loops in every pointed model category. The full adjunction uses
all original replacement and frame comparison maps.
-/

set_option autoImplicit false
noncomputable section
universe uC vC
open CategoryTheory Limits MorphismProperty
open scoped Simplicial SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.DerivedSuspensionLoopAdjunction

open PointedFramingAction

/-- The actual boundary inclusion of the original standard one-simplex. -/
abbrev circleBoundary : (SSet.boundary.{vC} 1 : SSet.{vC}) ⟶ SSet.stdSimplex.obj ⦋1⦌ :=
  (SSet.boundary.{vC} 1).ι

/-- The actual pointed circle, collapsing the whole original one-simplex boundary to its original point. -/
abbrev circle : PointedSSet.{vC} := SSet.pointedCircle.{vC}

/-- The entire original standard-simplex quotient map. -/
def circleQuotient : SSet.stdSimplex.obj ⦋1⦌ ⟶ circle.{vC}.right :=
  (SSet.boundary.{vC} 1).toQuotient

/-- The whole original boundary becomes the same actual pointed basepoint. -/
@[reassoc (attr := simp)]
theorem circle_boundary :
    circleBoundary.{vC} ≫ circleQuotient =
      SSet.stdSimplex.isTerminalObj₀.from (SSet.boundary.{vC} 1 : SSet.{vC}) ≫ circle.hom :=
        (SSet.boundary.{vC} 1).quotient_isPushout.w

/-- The actual original circle is cofibrant in the created pointed Kan--Quillen model. -/
theorem circle_isCofibrant : IsCofibrant circle.{vC} := pointedSSet_isCofibrant _

variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, vC} C] [HasColimitsOfSize.{0, vC} C]
  (d : GeneratedFunctorialReplacements.Data (C := C))

/-- Ordinary suspension is tensoring with the actual circle through the original framing on Ho(C). -/
def suspension : (weakEquivalences C).Localization ⥤ (weakEquivalences C).Localization :=
  tensorHo d circle

/-- Ordinary loops are cotensoring with that same actual circle through the original framing on Ho(C). -/
def loops : (weakEquivalences C).Localization ⥤ (weakEquivalences C).Localization :=
  cotensorHo d circle

/-- The full ordinary suspension--loop adjunction is constructed from the actual original pointed framing. -/
def adjunction : suspension d ⊣ loops d := ordinaryAdjunction d circle

/-- The entire original suspension object is the actual circle cofiber tensor of its complete left frame. -/
theorem suspension_obj (X : C) :
    (suspension d).obj ((weakEquivalences C).Q.obj X) =
      (weakEquivalences C).Q.obj (pointedTensor ((leftFrame d).obj X) circle) := rfl

/-- The entire original loop object is the actual circle fiber cotensor of its complete right frame. -/
theorem loops_obj (Y : C) :
    (loops d).obj ((weakEquivalences C).Q.obj Y) =
      (weakEquivalences C).Q.obj (pointedCotensor ((rightFrame d).obj Y) circle) := rfl

/-- Every original suspension map retains the same actual left-frame morphism and circle quotient map. -/
theorem suspension_map {X Y : C} (f : X ⟶ Y) :
    (suspension d).map ((weakEquivalences C).Q.map f) =
      (weakEquivalences C).Q.map (pointedTensorMap ((leftFrame d).map f) (𝟙 circle)) :=
  tensorHo_map d circle f

/-- Every original loop map retains the same actual right-frame morphism and circle fiber map. -/
theorem loops_map {X Y : C} (f : X ⟶ Y) :
    (loops d).map ((weakEquivalences C).Q.map f) =
      (weakEquivalences C).Q.map (pointedCotensorMap ((rightFrame d).map f) (𝟙 circle)) :=
  cotensorHo_map d circle f

/-- The actual ordinary adjunction unit, on every original Ho object. -/
def unit : 𝟭 (weakEquivalences C).Localization ⟶ suspension d ⋙ loops d := (adjunction d).unit

/-- The actual ordinary adjunction counit, on every original Ho object. -/
def counit : loops d ⋙ suspension d ⟶ 𝟭 (weakEquivalences C).Localization := (adjunction d).counit

/-- Every original suspension object retains the full actual first triangle. -/
theorem suspension_triangle (X : (weakEquivalences C).Localization) :
    (suspension d).map ((unit d).app X) ≫ (counit d).app ((suspension d).obj X) = 𝟙 _ :=
  (adjunction d).left_triangle_components X

/-- Every original loop object retains the full actual second triangle. -/
theorem loops_triangle (Y : (weakEquivalences C).Localization) :
    (unit d).app ((loops d).obj Y) ≫ (loops d).map ((counit d).app Y) = 𝟙 _ :=
  (adjunction d).right_triangle_components Y

/-- The whole ordinary Hom function retains the same original framing comparison word. -/
theorem homEquiv_original (X Y : C)
    (f : (suspension d).obj ((weakEquivalences C).Q.obj X) ⟶ (weakEquivalences C).Q.obj Y) :
    (adjunction d).homEquiv ((weakEquivalences C).Q.obj X) ((weakEquivalences C).Q.obj Y) f =
      framedHomEquiv d X circle Y f := by
  exact PointedFramingAction.ordinaryAdjunction_homEquiv d circle _ _ f

end HomotopicalAlgebra.DerivedSuspensionLoopAdjunction

namespace HomotopicalAlgebra.DerivedSuspensionLoopAdjunction

open PointedFramingAction

/-- Both original one-simplex faces become the actual same circle basepoint. -/
@[reassoc (attr := simp)]
theorem circle_face (i : Fin 2) :
    SSet.stdSimplex.δ i ≫ circleQuotient.{vC} =
      SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj ⦋0⦌ : SSet.{vC}) ≫ circle.hom := by
  rw [← SSet.boundary.ι_ι i, Category.assoc, circle_boundary]
  rw [← Category.assoc]
  exact congrArg (fun f => f ≫ circle.hom) (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

/-- Every caller one-simplex with both original faces at the point gives the actual circle quotient map. -/
def circleHomOfBoundary (Z : PointedSSet.{vC}) (f : SSet.stdSimplex.obj ⦋1⦌ ⟶ Z.right)
    (hf : ∀ i : Fin 2, SSet.stdSimplex.δ i ≫ f =
      SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj ⦋0⦌ : SSet.{vC}) ≫ Z.hom) :
    circle ⟶ Z :=
  Under.homMk (pushout.desc f Z.hom (by
    apply SSet.boundary.hom_ext
    intro i
    rw [SSet.boundary.ι_ι_assoc]
    have h : SSet.boundary.ι i ≫ SSet.stdSimplex.isTerminalObj₀.from (SSet.boundary.{vC} 1) =
        SSet.stdSimplex.isTerminalObj₀.from (Δ[0] : SSet.{vC}) :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [← Category.assoc, h]
    exact hf i)) (pushout.inr_desc _ _ _)

/-- The original entire one-simplex is recovered by the quotient universal property. -/
@[reassoc (attr := simp)]
theorem circleHomOfBoundary_quotient (Z : PointedSSet.{vC}) (f : SSet.stdSimplex.obj ⦋1⦌ ⟶ Z.right)
    (hf : ∀ i : Fin 2, SSet.stdSimplex.δ i ≫ f =
      SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj ⦋0⦌ : SSet.{vC}) ≫ Z.hom) :
    circleQuotient ≫ (circleHomOfBoundary Z f hf).right = f := pushout.inl_desc _ _ _

section FrameCircleGeometry

attribute [local implicit_reducible] ResolutionHomComplex.obj

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C]
/-- The same original zero object supplies the coefficient zero maps. -/
local instance coefficientZeroMorphisms1 : HasZeroMorphisms C := HasZeroObject.zeroMorphismsOfZeroObject
open scoped ZeroObject

omit [HasZeroObject C] in
/-- Every actual left Hom coface is the original cosimplicial coefficient map. -/
theorem leftHom_stdCoface (A : CosimplicialObject C) (Y : C) (i : Fin 2)
    (f : SSet.stdSimplex.obj ⦋1⦌ ⟶ ResolutionHomComplex.left A Y) :
    SSet.yonedaEquiv (SSet.stdSimplex.δ i ≫ f) = A.δ i ≫ SSet.yonedaEquiv f := by
  have h := uliftYonedaEquiv_naturality f (SimplexCategory.δ i).op
  exact h.symm.trans (ResolutionHomComplex.left_map_apply A Y _ _)

omit [HasZeroObject C] in
/-- Every actual right Hom face is the original simplicial coefficient map. -/
theorem rightHom_stdFace (X : C) (B : SimplicialObject C) (i : Fin 2)
    (f : SSet.stdSimplex.obj ⦋1⦌ ⟶ ResolutionHomComplex.right X B) :
    SSet.yonedaEquiv (SSet.stdSimplex.δ i ≫ f) = SSet.yonedaEquiv f ≫ B.δ i := by
  have h := uliftYonedaEquiv_naturality f (SimplexCategory.δ i).op
  exact h.symm.trans (ResolutionHomComplex.right_map_apply X B _ _)

section Cylinder

variable [HasFiniteColimits C]

/-- The full original two-end map of the actual cosimplicial frame cylinder. -/
def cylinderBoundary (A : CosimplicialObject C) : A.obj ⦋0⦌ ⨿ A.obj ⦋0⦌ ⟶ A.obj ⦋1⦌ :=
  coprod.desc (A.δ (0 : Fin 2)) (A.δ (1 : Fin 2))

/-- The actual full cylinder-end cofiber, with its same original zero map. -/
abbrev cylinderCofiber (A : CosimplicialObject C) : C :=
  pushout (cylinderBoundary A) (0 : A.obj ⦋0⦌ ⨿ A.obj ⦋0⦌ ⟶ (0 : C))

/-- The original entire cylinder quotient map. -/
def cylinderQuotient (A : CosimplicialObject C) : A.obj ⦋1⦌ ⟶ cylinderCofiber A := pushout.inl _ _

/-- The full original two-end boundary is killed by the actual cylinder quotient. -/
@[reassoc (attr := simp)]
theorem cylinderBoundary_quotient (A : CosimplicialObject C) :
    cylinderBoundary A ≫ cylinderQuotient A = 0 := pushout.condition.trans zero_comp

/-- Both original cylinder ends are killed by that same entire quotient. -/
@[reassoc (attr := simp)]
theorem cylinderEnd_quotient (A : CosimplicialObject C) (i : Fin 2) :
    A.δ i ≫ cylinderQuotient A = 0 := by
  fin_cases i
  · change A.δ (0 : Fin 2) ≫ cylinderQuotient A = 0
    have h := congrArg (fun f => coprod.inl (X := A.obj ⦋0⦌) (Y := A.obj ⦋0⦌) ≫ f)
      (cylinderBoundary_quotient A)
    simpa only [cylinderBoundary, coprod.inl_desc_assoc, comp_zero] using h
  · change A.δ (1 : Fin 2) ≫ cylinderQuotient A = 0
    have h := congrArg (fun f => coprod.inr (X := A.obj ⦋0⦌) (Y := A.obj ⦋0⦌) ≫ f)
      (cylinderBoundary_quotient A)
    simpa only [cylinderBoundary, coprod.inr_desc_assoc, comp_zero] using h

/-- The original cylinder cofiber map gives a full pointed map out of the actual circle. -/
def cylinderHomForward (A : CosimplicialObject C) (Y : C) (f : cylinderCofiber A ⟶ Y) :
    circle.{vC} ⟶ pointedLeftHom A Y :=
  circleHomOfBoundary _ ((SSet.yonedaEquiv (X := ResolutionHomComplex.left A Y)).symm (cylinderQuotient A ≫ f)) (by
    intro i
    apply SSet.yonedaEquiv.injective
    rw [leftHom_stdCoface, Equiv.apply_symm_apply, ← Category.assoc, cylinderEnd_quotient, zero_comp]
    rfl)

/-- The entire original cylinder quotient is read back in the original one-simplex coordinate. -/
@[reassoc (attr := simp)]
theorem cylinderHomForward_quotient (A : CosimplicialObject C) (Y : C) (f : cylinderCofiber A ⟶ Y) :
    circleQuotient ≫ (cylinderHomForward A Y f).right =
      (SSet.yonedaEquiv (X := ResolutionHomComplex.left A Y)).symm (cylinderQuotient A ≫ f) :=
        circleHomOfBoundary_quotient _ _ _

omit [HasFiniteColimits C] in
/-- A full pointed circle map has zero original cylinder endpoints in its original coefficient coordinate. -/
theorem cylinderHomBackward_end (A : CosimplicialObject C) (Y : C)
    (g : circle.{vC} ⟶ pointedLeftHom A Y) (i : Fin 2) :
    A.δ i ≫ SSet.yonedaEquiv (X := ResolutionHomComplex.left A Y) (circleQuotient ≫ g.right) = 0 := by
  rw [← leftHom_stdCoface, ← Category.assoc, circle_face, Category.assoc, CategoryTheory.Under.w]
  rfl

/-- The full actual cylinder cofiber desc supplied by the entire original pointed circle map. -/
def cylinderHomBackward (A : CosimplicialObject C) (Y : C)
    (g : circle.{vC} ⟶ pointedLeftHom A Y) : cylinderCofiber A ⟶ Y :=
  pushout.desc (f := cylinderBoundary A)
    (g := (0 : A.obj ⦋0⦌ ⨿ A.obj ⦋0⦌ ⟶ (0 : C)))
    (SSet.yonedaEquiv (X := ResolutionHomComplex.left A Y) (circleQuotient ≫ g.right)) (0 : (0 : C) ⟶ Y) (by
      apply coprod.hom_ext
      · simp only [cylinderBoundary, coprod.inl_desc_assoc, comp_zero]
        exact cylinderHomBackward_end A Y g (0 : Fin 2)
      · simp only [cylinderBoundary, coprod.inr_desc_assoc, comp_zero]
        exact cylinderHomBackward_end A Y g (1 : Fin 2))

/-- The actual cylinder quotient reads back the entire original coefficient one-simplex. -/
@[reassoc (attr := simp)]
theorem cylinderHomBackward_quotient (A : CosimplicialObject C) (Y : C)
    (g : circle.{vC} ⟶ pointedLeftHom A Y) :
    cylinderQuotient A ≫ cylinderHomBackward A Y g =
      SSet.yonedaEquiv (X := ResolutionHomComplex.left A Y) (circleQuotient ≫ g.right) := pushout.inl_desc _ _ _

/-- The full actual cylinder cofiber and pointed circle Hom have the same original universal property. -/
def cylinderHomEquiv (A : CosimplicialObject C) (Y : C) :
    (cylinderCofiber A ⟶ Y) ≃ (circle.{vC} ⟶ pointedLeftHom A Y) where
  toFun := cylinderHomForward A Y
  invFun := cylinderHomBackward A Y
  left_inv f := by
    apply pushout.hom_ext
    · change cylinderQuotient A ≫ cylinderHomBackward A Y (cylinderHomForward A Y f) =
        cylinderQuotient A ≫ f
      rw [cylinderHomBackward_quotient, cylinderHomForward_quotient, Equiv.apply_symm_apply]
    · exact HasZeroObject.zeroIsInitial.hom_ext _ _
  right_inv g := by
    apply Under.UnderMorphism.ext
    apply pushout.hom_ext
    · change circleQuotient ≫ (cylinderHomForward A Y (cylinderHomBackward A Y g)).right =
        circleQuotient ≫ g.right
      rw [cylinderHomForward_quotient]
      exact (congrArg (SSet.yonedaEquiv (X := ResolutionHomComplex.left A Y)).symm
        (cylinderHomBackward_quotient A Y g)).trans
          ((SSet.yonedaEquiv (X := ResolutionHomComplex.left A Y)).symm_apply_apply _)
    · change circle.hom ≫ (cylinderHomForward A Y (cylinderHomBackward A Y g)).right = circle.hom ≫ g.right
      rw [CategoryTheory.Under.w, CategoryTheory.Under.w]

end Cylinder

end FrameCircleGeometry

end HomotopicalAlgebra.DerivedSuspensionLoopAdjunction

namespace HomotopicalAlgebra.DerivedSuspensionLoopAdjunction

open PointedFramingAction

section PathCircleGeometry

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C] [HasFiniteLimits C]
/-- The same original zero object supplies the coefficient zero maps. -/
local instance coefficientZeroMorphisms2 : HasZeroMorphisms C := HasZeroObject.zeroMorphismsOfZeroObject
attribute [local implicit_reducible] ResolutionHomComplex.obj
open scoped ZeroObject

/-- The full original two-end projection of the actual simplicial frame path. -/
def pathBoundary (B : SimplicialObject C) : B.obj (Opposite.op ⦋1⦌) ⟶
    B.obj (Opposite.op ⦋0⦌) ⨯ B.obj (Opposite.op ⦋0⦌) :=
  prod.lift (B.δ (0 : Fin 2)) (B.δ (1 : Fin 2))

/-- The actual full path-end fiber with its same original zero map. -/
abbrev pathFiber (B : SimplicialObject C) : C :=
  pullback (pathBoundary B) (0 : (0 : C) ⟶ B.obj (Opposite.op ⦋0⦌) ⨯ B.obj (Opposite.op ⦋0⦌))

/-- The original entire path fiber projection. -/
def pathProjection (B : SimplicialObject C) : pathFiber B ⟶ B.obj (Opposite.op ⦋1⦌) := pullback.fst _ _

/-- The original complete two-end path projection is zero on the actual fiber. -/
@[reassoc (attr := simp)]
theorem pathProjection_boundary (B : SimplicialObject C) :
    pathProjection B ≫ pathBoundary B = 0 := pullback.condition.trans comp_zero

/-- Both original path ends are zero on that same entire fiber projection. -/
@[reassoc (attr := simp)]
theorem pathProjection_end (B : SimplicialObject C) (i : Fin 2) : pathProjection B ≫ B.δ i = 0 := by
  fin_cases i
  · change pathProjection B ≫ B.δ (0 : Fin 2) = 0
    have h := congrArg (fun f => f ≫ prod.fst (X := B.obj (Opposite.op ⦋0⦌))
      (Y := B.obj (Opposite.op ⦋0⦌))) (pathProjection_boundary B)
    simpa only [Category.assoc, pathBoundary, prod.lift_fst, zero_comp] using h
  · change pathProjection B ≫ B.δ (1 : Fin 2) = 0
    have h := congrArg (fun f => f ≫ prod.snd (X := B.obj (Opposite.op ⦋0⦌))
      (Y := B.obj (Opposite.op ⦋0⦌))) (pathProjection_boundary B)
    simpa only [Category.assoc, pathBoundary, prod.lift_snd, zero_comp] using h

/-- The original path fiber map gives its entire pointed circle Hom map. -/
def pathHomForward (X : C) (B : SimplicialObject C) (f : X ⟶ pathFiber B) :
    circle.{vC} ⟶ pointedRightHom X B :=
  circleHomOfBoundary _ ((SSet.yonedaEquiv (X := ResolutionHomComplex.right X B)).symm
    (f ≫ pathProjection B)) (by
      intro i
      apply SSet.yonedaEquiv.injective
      rw [rightHom_stdFace, Equiv.apply_symm_apply, Category.assoc, pathProjection_end, comp_zero]
      rfl)

/-- The full original path coordinate is read back through the actual circle quotient. -/
@[reassoc (attr := simp)]
theorem pathHomForward_quotient (X : C) (B : SimplicialObject C) (f : X ⟶ pathFiber B) :
    circleQuotient ≫ (pathHomForward X B f).right =
      (SSet.yonedaEquiv (X := ResolutionHomComplex.right X B)).symm (f ≫ pathProjection B) :=
  circleHomOfBoundary_quotient _ _ _

omit [HasFiniteLimits C] in
/-- Every full original pointed circle map has zero original path endpoints. -/
theorem pathHomBackward_end (X : C) (B : SimplicialObject C)
    (g : circle.{vC} ⟶ pointedRightHom X B) (i : Fin 2) :
    SSet.yonedaEquiv (X := ResolutionHomComplex.right X B) (circleQuotient ≫ g.right) ≫ B.δ i = 0 := by
  rw [← rightHom_stdFace, ← Category.assoc, circle_face, Category.assoc, CategoryTheory.Under.w]
  rfl

/-- The whole actual path fiber lift supplied by the original pointed circle map. -/
def pathHomBackward (X : C) (B : SimplicialObject C)
    (g : circle.{vC} ⟶ pointedRightHom X B) : X ⟶ pathFiber B :=
  pullback.lift (f := pathBoundary B)
    (g := (0 : (0 : C) ⟶ B.obj (Opposite.op ⦋0⦌) ⨯ B.obj (Opposite.op ⦋0⦌)))
    (SSet.yonedaEquiv (X := ResolutionHomComplex.right X B) (circleQuotient ≫ g.right)) (0 : X ⟶ (0 : C))
    (by
      apply prod.hom_ext
      · simp only [Category.assoc, pathBoundary, prod.lift_fst, zero_comp]
        exact pathHomBackward_end X B g (0 : Fin 2)
      · simp only [Category.assoc, pathBoundary, prod.lift_snd, zero_comp]
        exact pathHomBackward_end X B g (1 : Fin 2))

/-- The actual path fiber projection reads back the entire original one-simplex coordinate. -/
@[reassoc (attr := simp)]
theorem pathHomBackward_projection (X : C) (B : SimplicialObject C)
    (g : circle.{vC} ⟶ pointedRightHom X B) :
    pathHomBackward X B g ≫ pathProjection B =
      SSet.yonedaEquiv (X := ResolutionHomComplex.right X B) (circleQuotient ≫ g.right) :=
  pullback.lift_fst _ _ _

/-- The original full path fiber and pointed circle Hom have the same complete universal property. -/
def pathHomEquiv (X : C) (B : SimplicialObject C) :
    (X ⟶ pathFiber B) ≃ (circle.{vC} ⟶ pointedRightHom X B) where
  toFun := pathHomForward X B
  invFun := pathHomBackward X B
  left_inv f := by
    apply pullback.hom_ext
    · change pathHomBackward X B (pathHomForward X B f) ≫ pathProjection B = f ≫ pathProjection B
      rw [pathHomBackward_projection, pathHomForward_quotient, Equiv.apply_symm_apply]
    · exact HasZeroObject.zeroIsTerminal.hom_ext _ _
  right_inv g := by
    apply Under.UnderMorphism.ext
    apply pushout.hom_ext
    · change circleQuotient ≫ (pathHomForward X B (pathHomBackward X B g)).right = circleQuotient ≫ g.right
      rw [pathHomForward_quotient]
      exact (congrArg (SSet.yonedaEquiv (X := ResolutionHomComplex.right X B)).symm
        (pathHomBackward_projection X B g)).trans
          ((SSet.yonedaEquiv (X := ResolutionHomComplex.right X B)).symm_apply_apply _)
    · change circle.hom ≫ (pathHomForward X B (pathHomBackward X B g)).right = circle.hom ≫ g.right
      rw [CategoryTheory.Under.w, CategoryTheory.Under.w]

end PathCircleGeometry

end HomotopicalAlgebra.DerivedSuspensionLoopAdjunction

namespace HomotopicalAlgebra.DerivedSuspensionLoopAdjunction

open PointedFramingAction

section CylinderTensorComparison

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C]
  [HasFiniteColimits C] [HasColimitsOfSize.{0, vC} C]
attribute [local implicit_reducible] ResolutionHomComplex.obj

omit [HasColimitsOfSize.{0, vC} C] in
/-- The complete actual cylinder Hom equivalence preserves every original target map. -/
theorem cylinderHomEquiv_target (A : CosimplicialObject C) {Y Y' : C} (p : Y ⟶ Y')
    (f : cylinderCofiber A ⟶ Y) :
    cylinderHomEquiv A Y' (f ≫ p) = cylinderHomEquiv A Y f ≫ (pointedLeftHomFunctor A).map p := by
  apply Under.UnderMorphism.ext
  apply pushout.hom_ext
  · change circleQuotient ≫ (cylinderHomForward A Y' (f ≫ p)).right =
      circleQuotient ≫ ((cylinderHomForward A Y f).right ≫
        ResolutionHomComplex.postcomp A ((SimplicialObject.const C).map p))
    rw [← Category.assoc, cylinderHomForward_quotient, cylinderHomForward_quotient]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    change cylinderQuotient A ≫ (f ≫ p) = (cylinderQuotient A ≫ f) ≫ p
    exact (Category.assoc _ _ _).symm
  · change circle.hom ≫ (cylinderHomForward A Y' (f ≫ p)).right =
      circle.hom ≫ (cylinderHomEquiv A Y f ≫ (pointedLeftHomFunctor A).map p).right
    rw [CategoryTheory.Under.w, CategoryTheory.Under.w]

/-- The full natural Hom equivalence compares the actual circle tensor and original cylinder-end cofiber. -/
def cylinderTensorHomEquiv (A : CosimplicialObject C) (Y : C) :
    (pointedTensor A circle.{vC} ⟶ Y) ≃ (cylinderCofiber A ⟶ Y) :=
  (pointedTensorHomEquiv A circle Y).trans (cylinderHomEquiv A Y).symm

/-- Every original target map is retained by the full circle/cylinder Hom comparison. -/
theorem cylinderTensorHomEquiv_target (A : CosimplicialObject C) {Y Y' : C} (p : Y ⟶ Y')
    (f : pointedTensor A circle.{vC} ⟶ Y) :
    cylinderTensorHomEquiv A Y' (f ≫ p) = cylinderTensorHomEquiv A Y f ≫ p := by
  apply (cylinderHomEquiv A Y').injective
  change cylinderHomEquiv A Y' ((cylinderHomEquiv A Y').symm
      (pointedTensorHomEquiv A circle Y' (f ≫ p))) =
    cylinderHomEquiv A Y' ((cylinderHomEquiv A Y).symm (pointedTensorHomEquiv A circle Y f) ≫ p)
  rw [Equiv.apply_symm_apply, cylinderHomEquiv_target, Equiv.apply_symm_apply, pointedTensorHomEquiv_target]

/-- The actual circle tensor is the same complete original cylinder-end cofiber. -/
def cylinderTensorIso (A : CosimplicialObject C) : pointedTensor A circle.{vC} ≅ cylinderCofiber A := by
  let U := pointedTensor A circle.{vC}
  let V := cylinderCofiber A
  let e (Y : C) := cylinderTensorHomEquiv A Y
  let f : U ⟶ V := (e V).symm (𝟙 V)
  let g : V ⟶ U := e U (𝟙 U)
  refine ⟨f, g, ?_, ?_⟩
  · apply (e U).injective
    have hn := cylinderTensorHomEquiv_target A g f
    change e U (f ≫ g) = e V f ≫ g at hn
    rw [hn]
    dsimp only [f]
    rw [Equiv.apply_symm_apply, Category.id_comp]
  · have hn := cylinderTensorHomEquiv_target A f (𝟙 U)
    change e V (𝟙 U ≫ f) = g ≫ f at hn
    rw [Category.id_comp] at hn
    rw [← hn]
    dsimp only [f]
    exact (e V).apply_symm_apply _

/-- The entire forward circle/cylinder comparison is the actual original cofiber desc word. -/
theorem cylinderTensorIso_hom (A : CosimplicialObject C) :
    (cylinderTensorIso A).hom = (pointedTensorHomEquiv A circle (cylinderCofiber A)).symm
      (cylinderHomEquiv A (cylinderCofiber A) (𝟙 _)) := rfl

/-- The entire inverse comparison is the actual original cylinder desc word. -/
theorem cylinderTensorIso_inv (A : CosimplicialObject C) :
    (cylinderTensorIso A).inv = (cylinderHomEquiv A (pointedTensor A circle)).symm
      (pointedTensorHomEquiv A circle (pointedTensor A circle) (𝟙 _)) := rfl

end CylinderTensorComparison

section PathCotensorComparison

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C]
  [HasFiniteLimits C] [HasLimitsOfSize.{0, vC} C]
attribute [local implicit_reducible] ResolutionHomComplex.obj

omit [HasLimitsOfSize.{0, vC} C] in
/-- The complete original path Hom equivalence preserves every actual source map. -/
theorem pathHomEquiv_source {X X' : C} (p : X ⟶ X') (B : SimplicialObject C)
    (f : X' ⟶ pathFiber B) :
    pathHomEquiv X B (p ≫ f) = pathHomEquiv X' B f ≫
      pointedHomPrecomp ((CosimplicialObject.const C).map p) B := by
  apply Under.UnderMorphism.ext
  apply pushout.hom_ext
  · change circleQuotient ≫ (pathHomForward X B (p ≫ f)).right =
      circleQuotient ≫ ((pathHomForward X' B f).right ≫
        ResolutionHomComplex.precomp ((CosimplicialObject.const C).map p) B)
    rw [← Category.assoc, pathHomForward_quotient, pathHomForward_quotient]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    change (p ≫ f) ≫ pathProjection B = p ≫ (f ≫ pathProjection B)
    exact Category.assoc _ _ _
  · change circle.hom ≫ (pathHomForward X B (p ≫ f)).right =
      circle.hom ≫ (pathHomEquiv X' B f ≫ pointedHomPrecomp ((CosimplicialObject.const C).map p) B).right
    rw [CategoryTheory.Under.w, CategoryTheory.Under.w]

/-- The whole original pointed circle cotensor and actual path fiber have the same natural Hom. -/
def pathCotensorHomEquiv (X : C) (B : SimplicialObject C) :
    (X ⟶ pointedCotensor B circle.{vC}) ≃ (X ⟶ pathFiber B) :=
  (pointedCotensorHomEquiv X circle B).trans (pathHomEquiv X B).symm

/-- Every actual original source map is retained by the full circle/path Hom comparison. -/
theorem pathCotensorHomEquiv_source {X X' : C} (p : X ⟶ X') (B : SimplicialObject C)
    (f : X' ⟶ pointedCotensor B circle.{vC}) :
    pathCotensorHomEquiv X B (p ≫ f) = p ≫ pathCotensorHomEquiv X' B f := by
  apply (pathHomEquiv X B).injective
  change pathHomEquiv X B ((pathHomEquiv X B).symm (pointedCotensorHomEquiv X circle B (p ≫ f))) =
    pathHomEquiv X B (p ≫ (pathHomEquiv X' B).symm (pointedCotensorHomEquiv X' circle B f))
  rw [Equiv.apply_symm_apply, pathHomEquiv_source, Equiv.apply_symm_apply, pointedCotensorHomEquiv_source]

/-- The actual pointed circle cotensor is the same full original path-end fiber. -/
def pathCotensorIso (B : SimplicialObject C) : pointedCotensor B circle.{vC} ≅ pathFiber B := by
  let U := pointedCotensor B circle.{vC}
  let V := pathFiber B
  let e (X : C) := pathCotensorHomEquiv X B
  let f : U ⟶ V := e U (𝟙 U)
  let g : V ⟶ U := (e V).symm (𝟙 V)
  refine ⟨f, g, ?_, ?_⟩
  · apply (e U).injective
    have hn := pathCotensorHomEquiv_source f B g
    change e U (f ≫ g) = f ≫ e V g at hn
    rw [hn]
    dsimp only [g]
    rw [Equiv.apply_symm_apply, Category.comp_id]
  · have hn := pathCotensorHomEquiv_source g B (𝟙 U)
    change e V (g ≫ 𝟙 U) = g ≫ f at hn
    rw [Category.comp_id] at hn
    rw [← hn]
    dsimp only [g]
    exact (e V).apply_symm_apply _

/-- The entire forward circle/path comparison is the actual original fiber lift word. -/
theorem pathCotensorIso_hom (B : SimplicialObject C) :
    (pathCotensorIso B).hom = (pathHomEquiv (pointedCotensor B circle) B).symm
      (pointedCotensorHomEquiv (pointedCotensor B circle) circle B (𝟙 _)) := rfl

/-- The entire inverse circle/path comparison is the same original full fiber lift word. -/
theorem pathCotensorIso_inv (B : SimplicialObject C) :
    (pathCotensorIso B).inv = (pointedCotensorHomEquiv (pathFiber B) circle B).symm
      (pathHomEquiv (pathFiber B) B (𝟙 _)) := rfl

end PathCotensorComparison

end HomotopicalAlgebra.DerivedSuspensionLoopAdjunction

namespace HomotopicalAlgebra.DerivedSuspensionLoopAdjunction

open PointedFramingAction

section CylinderMaps

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C] [HasFiniteColimits C]
/-- The same original zero object supplies the coefficient zero maps. -/
local instance coefficientZeroMorphisms3 : HasZeroMorphisms C := HasZeroObject.zeroMorphismsOfZeroObject
attribute [local implicit_reducible] ResolutionHomComplex.obj
open scoped ZeroObject

omit [HasZeroObject C] in
/-- Every full frame map retains both original cylinder endpoints. -/
theorem cylinderBoundary_naturality {A A' : CosimplicialObject C} (a : A ⟶ A') :
    cylinderBoundary A ≫ a.app ⦋1⦌ =
      coprod.map (a.app ⦋0⦌) (a.app ⦋0⦌) ≫ cylinderBoundary A' := by
  apply coprod.hom_ext
  · simp only [cylinderBoundary, coprod.inl_desc_assoc, coprod.inl_map_assoc, coprod.inl_desc]
    exact a.naturality (SimplexCategory.δ (0 : Fin 2))
  · simp only [cylinderBoundary, coprod.inr_desc_assoc, coprod.inr_map_assoc, coprod.inr_desc]
    exact a.naturality (SimplexCategory.δ (1 : Fin 2))

/-- The actual whole cylinder-end cofiber map of the original frame morphism. -/
def cylinderMap {A A' : CosimplicialObject C} (a : A ⟶ A') : cylinderCofiber A ⟶ cylinderCofiber A' :=
  pushout.map (cylinderBoundary A) (0 : A.obj ⦋0⦌ ⨿ A.obj ⦋0⦌ ⟶ (0 : C))
    (cylinderBoundary A') (0 : A'.obj ⦋0⦌ ⨿ A'.obj ⦋0⦌ ⟶ (0 : C))
    (a.app ⦋1⦌) (𝟙 (0 : C)) (coprod.map (a.app ⦋0⦌) (a.app ⦋0⦌))
    (cylinderBoundary_naturality a) (by simp)

/-- The entire original cylinder quotient square keeps its original degree-one map. -/
@[reassoc (attr := simp)]
theorem cylinderMap_quotient {A A' : CosimplicialObject C} (a : A ⟶ A') :
    cylinderQuotient A ≫ cylinderMap a = a.app ⦋1⦌ ≫ cylinderQuotient A' := pushout.inl_desc _ _ _

/-- The complete cylinder Hom function is natural in every original frame morphism. -/
theorem cylinderHomEquiv_frame {A A' : CosimplicialObject C} (a : A ⟶ A') (Y : C)
    (f : cylinderCofiber A' ⟶ Y) :
    cylinderHomEquiv A Y (cylinderMap a ≫ f) =
      cylinderHomEquiv A' Y f ≫ pointedHomPrecomp a ((SimplicialObject.const C).obj Y) := by
  apply Under.UnderMorphism.ext
  apply pushout.hom_ext
  · change circleQuotient ≫ (cylinderHomForward A Y (cylinderMap a ≫ f)).right =
      circleQuotient ≫ ((cylinderHomForward A' Y f).right ≫
        ResolutionHomComplex.precomp a ((SimplicialObject.const C).obj Y))
    rw [← Category.assoc, cylinderHomForward_quotient, cylinderHomForward_quotient]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    change cylinderQuotient A ≫ (cylinderMap a ≫ f) = a.app ⦋1⦌ ≫ (cylinderQuotient A' ≫ f)
    rw [← Category.assoc, cylinderMap_quotient, Category.assoc]
  · change circle.hom ≫ (cylinderHomForward A Y (cylinderMap a ≫ f)).right =
      circle.hom ≫ (cylinderHomEquiv A' Y f ≫ pointedHomPrecomp a ((SimplicialObject.const C).obj Y)).right
    rw [CategoryTheory.Under.w, CategoryTheory.Under.w]

variable [HasColimitsOfSize.{0, vC} C]

/-- The full circle/cylinder isomorphism keeps every original frame map in its entire forward square. -/
theorem cylinderTensorIso_naturality {A A' : CosimplicialObject C} (a : A ⟶ A') :
    pointedTensorMap a (𝟙 circle.{vC}) ≫ (cylinderTensorIso A').hom =
      (cylinderTensorIso A).hom ≫ cylinderMap a := by
  apply (pointedTensorHomEquiv A circle (cylinderCofiber A')).injective
  have h₁ := pointedTensorHomEquiv_source a circle (cylinderCofiber A') (cylinderTensorIso A').hom
  rw [cylinderTensorIso_hom, Equiv.apply_symm_apply] at h₁
  have h₂ := pointedTensorHomEquiv_target A circle (cylinderMap a) (cylinderTensorIso A).hom
  rw [cylinderTensorIso_hom, Equiv.apply_symm_apply] at h₂
  have h₃ := cylinderHomEquiv_frame a (cylinderCofiber A') (𝟙 _)
  rw [Category.comp_id] at h₃
  have h₄ := cylinderHomEquiv_target A (cylinderMap a) (𝟙 _)
  rw [Category.id_comp] at h₄
  exact h₁.trans (h₃.symm.trans (h₄.trans h₂.symm))

end CylinderMaps

section PathMaps

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C] [HasFiniteLimits C]
/-- The same original zero object supplies the coefficient zero maps. -/
local instance coefficientZeroMorphisms4 : HasZeroMorphisms C := HasZeroObject.zeroMorphismsOfZeroObject
attribute [local implicit_reducible] ResolutionHomComplex.obj
open scoped ZeroObject

omit [HasZeroObject C] in
/-- Every full frame map retains both original path endpoint projections. -/
theorem pathBoundary_naturality {B B' : SimplicialObject C} (b : B ⟶ B') :
    pathBoundary B ≫ prod.map (b.app (Opposite.op ⦋0⦌)) (b.app (Opposite.op ⦋0⦌)) =
      b.app (Opposite.op ⦋1⦌) ≫ pathBoundary B' := by
  apply prod.hom_ext
  · simp only [Category.assoc, pathBoundary, prod.map_fst, prod.lift_fst, prod.lift_fst_assoc]
    exact b.naturality (SimplexCategory.δ (0 : Fin 2)).op
  · simp only [Category.assoc, pathBoundary, prod.map_snd, prod.lift_snd, prod.lift_snd_assoc]
    exact b.naturality (SimplexCategory.δ (1 : Fin 2)).op

/-- The actual full path-end fiber map of every original simplicial frame morphism. -/
def pathMap {B B' : SimplicialObject C} (b : B ⟶ B') : pathFiber B ⟶ pathFiber B' :=
  pullback.map (pathBoundary B) (0 : (0 : C) ⟶ B.obj (Opposite.op ⦋0⦌) ⨯ B.obj (Opposite.op ⦋0⦌))
    (pathBoundary B') (0 : (0 : C) ⟶ B'.obj (Opposite.op ⦋0⦌) ⨯ B'.obj (Opposite.op ⦋0⦌))
    (b.app (Opposite.op ⦋1⦌)) (𝟙 (0 : C))
    (prod.map (b.app (Opposite.op ⦋0⦌)) (b.app (Opposite.op ⦋0⦌)))
    (pathBoundary_naturality b) (by simp)

/-- The entire original path fiber projection square keeps its original degree-one map. -/
@[reassoc (attr := simp)]
theorem pathMap_projection {B B' : SimplicialObject C} (b : B ⟶ B') :
    pathMap b ≫ pathProjection B' = pathProjection B ≫ b.app (Opposite.op ⦋1⦌) := pullback.lift_fst _ _ _

/-- The full original path Hom function is natural in every actual frame morphism. -/
theorem pathHomEquiv_frame (X : C) {B B' : SimplicialObject C} (b : B ⟶ B') (f : X ⟶ pathFiber B) :
    pathHomEquiv X B' (f ≫ pathMap b) = pathHomEquiv X B f ≫
      pointedHomPostcomp ((CosimplicialObject.const C).obj X) b := by
  apply Under.UnderMorphism.ext
  apply pushout.hom_ext
  · change circleQuotient ≫ (pathHomForward X B' (f ≫ pathMap b)).right =
      circleQuotient ≫ ((pathHomForward X B f).right ≫
        ResolutionHomComplex.postcomp ((CosimplicialObject.const C).obj X) b)
    rw [← Category.assoc, pathHomForward_quotient, pathHomForward_quotient]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    change (f ≫ pathMap b) ≫ pathProjection B' = (f ≫ pathProjection B) ≫ b.app (Opposite.op ⦋1⦌)
    rw [Category.assoc, pathMap_projection, ← Category.assoc]
  · change circle.hom ≫ (pathHomForward X B' (f ≫ pathMap b)).right =
      circle.hom ≫ (pathHomEquiv X B f ≫ pointedHomPostcomp ((CosimplicialObject.const C).obj X) b).right
    rw [CategoryTheory.Under.w, CategoryTheory.Under.w]

variable [HasLimitsOfSize.{0, vC} C]

/-- The full circle/path isomorphism keeps every original frame map in its entire forward square. -/
theorem pathCotensorIso_naturality {B B' : SimplicialObject C} (b : B ⟶ B') :
    (pathCotensorIso B).hom ≫ pathMap b =
      pointedCotensorMap b (𝟙 circle.{vC}) ≫ (pathCotensorIso B').hom := by
  apply (pathHomEquiv (pointedCotensor B circle) B').injective
  have h₁ := pathHomEquiv_frame (pointedCotensor B circle) b (pathCotensorIso B).hom
  rw [pathCotensorIso_hom, Equiv.apply_symm_apply] at h₁
  have h₂ := pathHomEquiv_source (pointedCotensorMap b (𝟙 circle)) B' (pathCotensorIso B').hom
  rw [pathCotensorIso_hom, Equiv.apply_symm_apply] at h₂
  have h₃ := pointedCotensorHomEquiv_target (pointedCotensor B circle) circle b (𝟙 _)
  rw [Category.id_comp] at h₃
  have h₄ := pointedCotensorHomEquiv_source (pointedCotensorMap b (𝟙 circle)) circle B' (𝟙 _)
  rw [Category.comp_id] at h₄
  exact h₁.trans (h₃.symm.trans (h₄.trans h₂.symm))

end PathMaps

end HomotopicalAlgebra.DerivedSuspensionLoopAdjunction

namespace HomotopicalAlgebra.DerivedSuspensionLoopAdjunction

open PointedFramingAction

section OriginalEndpoints

attribute [local implicit_reducible] PointedFramingAction.leftCylinder PointedFramingAction.rightPath

variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [HasZeroObject C]
  (d : GeneratedFunctorialReplacements.Data (C := C))
/-- The same original zero object supplies the coefficient zero maps. -/
local instance coefficientZeroMorphisms5 : HasZeroMorphisms C := HasZeroObject.zeroMorphismsOfZeroObject
open scoped ZeroObject

/-- The full original two-end inclusion of the actual good cylinder on the same original Q object. -/
def originalCylinderBoundary (X : C) : d.Q.obj X ⨿ d.Q.obj X ⟶ (leftCylinder d X).I :=
  coprod.desc (leftCylinder d X).i₀ (leftCylinder d X).i₁

/-- The original ordinary cylinder cofiber, with its full actual Q endpoints and zero map. -/
abbrev originalCylinderCofiber (X : C) : C :=
  pushout (originalCylinderBoundary d X) (0 : d.Q.obj X ⨿ d.Q.obj X ⟶ (0 : C))

/-- The full original cylinder cofiber quotient map. -/
def originalCylinderQuotient (X : C) : (leftCylinder d X).I ⟶ originalCylinderCofiber d X := pushout.inl _ _

omit [HasZeroObject C] in
/-- The original Q-identification retains the whole original two-end cylinder boundary. -/
theorem originalCylinderBoundary_frame (X : C) :
    originalCylinderBoundary d X =
      coprod.map ((leftZeroIso d).inv.app X) ((leftZeroIso d).inv.app X) ≫
        cylinderBoundary ((leftFrame d).obj X) := by
  exact (coprod.map_desc _ _ _ _).symm

/-- The actual original Q cylinder cofiber is the same complete frame-degree-zero cofiber. -/
def originalCylinderIso (X : C) : originalCylinderCofiber d X ≅ cylinderCofiber ((leftFrame d).obj X) := by
  let a := pushout.map (originalCylinderBoundary d X) (0 : d.Q.obj X ⨿ d.Q.obj X ⟶ (0 : C))
    (cylinderBoundary ((leftFrame d).obj X))
    (0 : ((leftFrame d).obj X).obj ⦋0⦌ ⨿ ((leftFrame d).obj X).obj ⦋0⦌ ⟶ (0 : C))
    (eqToIso (leftCylinder_I d X)).hom (𝟙 (0 : C))
    (coprod.map ((leftZeroIso d).inv.app X) ((leftZeroIso d).inv.app X))
    (by exact (Category.comp_id _).trans (originalCylinderBoundary_frame d X)) (by simp)
  let : IsIso (coprod.map ((leftZeroIso d).inv.app X) ((leftZeroIso d).inv.app X)) := by
    change IsIso (coprod.mapIso ((leftZeroIso d).app X).symm ((leftZeroIso d).app X).symm).hom
    infer_instance
  let _ : IsIso a := by
    dsimp only [a]
    exact pushout.map_isIso _ _ _ _ _ _ _ _ _
  exact asIso a

/-- The whole original Q-cylinder quotient leg is retained in the point-set comparison. -/
@[reassoc (attr := simp)]
theorem originalCylinderIso_quotient (X : C) :
    originalCylinderQuotient d X ≫ (originalCylinderIso d X).hom =
      (eqToIso (leftCylinder_I d X)).hom ≫ cylinderQuotient ((leftFrame d).obj X) := by
  exact pushout.inl_desc _ _ _

/-- The full original two-end projection of the actual path object on the same original R object. -/
def originalPathBoundary (Y : C) : (rightPath d Y).P ⟶ d.R.obj Y ⨯ d.R.obj Y :=
  prod.lift (rightPath d Y).p₀ (rightPath d Y).p₁

/-- The original ordinary path fiber, with its full actual R endpoints and zero map. -/
abbrev originalPathFiber (Y : C) : C :=
  pullback (originalPathBoundary d Y) (0 : (0 : C) ⟶ d.R.obj Y ⨯ d.R.obj Y)

/-- The whole original R-path fiber projection. -/
def originalPathProjection (Y : C) : originalPathFiber d Y ⟶ (rightPath d Y).P := pullback.fst _ _

omit [HasZeroObject C] in
/-- The original R-identification retains the full original two-end path projection. -/
theorem originalPathBoundary_frame (Y : C) :
    originalPathBoundary d Y = pathBoundary ((rightFrame d).obj Y) ≫
      prod.map ((rightZeroIso d).inv.app Y) ((rightZeroIso d).inv.app Y) :=
  (prod.lift_map _ _ _ _).symm

/-- The actual full original R-path fiber is the same complete frame-degree-zero path fiber. -/
def originalPathIso (Y : C) : pathFiber ((rightFrame d).obj Y) ≅ originalPathFiber d Y := by
  let a := pullback.map (pathBoundary ((rightFrame d).obj Y))
    (0 : (0 : C) ⟶ ((rightFrame d).obj Y).obj (Opposite.op ⦋0⦌) ⨯
      ((rightFrame d).obj Y).obj (Opposite.op ⦋0⦌))
    (originalPathBoundary d Y) (0 : (0 : C) ⟶ d.R.obj Y ⨯ d.R.obj Y)
    (eqToIso (rightPath_P d Y)).inv (𝟙 (0 : C))
    (prod.map ((rightZeroIso d).inv.app Y) ((rightZeroIso d).inv.app Y))
    (by exact (originalPathBoundary_frame d Y).symm.trans (Category.id_comp _).symm) (by simp)
  let : IsIso (prod.map ((rightZeroIso d).inv.app Y) ((rightZeroIso d).inv.app Y)) := by
    change IsIso (prod.mapIso ((rightZeroIso d).app Y).symm ((rightZeroIso d).app Y).symm).hom
    infer_instance
  let _ : IsIso a := by
    dsimp only [a]
    exact pullback.map_isIso _ _ _ _ _ _ _ _ _
  exact asIso a

/-- The full original R-path fiber projection is retained in its point-set comparison. -/
@[reassoc (attr := simp)]
theorem originalPathIso_projection (Y : C) :
    (originalPathIso d Y).hom ≫ originalPathProjection d Y =
      pathProjection ((rightFrame d).obj Y) ≫ (eqToIso (rightPath_P d Y)).inv := by
  exact pullback.lift_fst _ _ _

variable [HasLimitsOfSize.{0, vC} C] [HasColimitsOfSize.{0, vC} C]

/-- Ordinary suspension retains the full original good-cylinder cofiber comparison. -/
def suspensionCylinderIso (X : C) :
    (suspension d).obj ((weakEquivalences C).Q.obj X) ≅
      (weakEquivalences C).Q.obj (originalCylinderCofiber d X) :=
  (weakEquivalences C).Q.mapIso
    (cylinderTensorIso ((leftFrame d).obj X) ≪≫ (originalCylinderIso d X).symm)

/-- Ordinary loops retain the full original good-path fiber comparison. -/
def loopsPathIso (Y : C) :
    (loops d).obj ((weakEquivalences C).Q.obj Y) ≅
      (weakEquivalences C).Q.obj (originalPathFiber d Y) :=
  (weakEquivalences C).Q.mapIso
    (pathCotensorIso ((rightFrame d).obj Y) ≪≫ originalPathIso d Y)

/-- The complete suspension comparison keeps both original cylinder cofiber maps. -/
theorem suspensionCylinderIso_hom (X : C) :
    (suspensionCylinderIso d X).hom = (weakEquivalences C).Q.map
      ((cylinderTensorIso ((leftFrame d).obj X)).hom ≫ (originalCylinderIso d X).inv) := rfl

/-- The complete loop comparison keeps both original path fiber maps. -/
theorem loopsPathIso_hom (Y : C) :
    (loopsPathIso d Y).hom = (weakEquivalences C).Q.map
      ((pathCotensorIso ((rightFrame d).obj Y)).hom ≫ (originalPathIso d Y).hom) := rfl

end OriginalEndpoints

end HomotopicalAlgebra.DerivedSuspensionLoopAdjunction

namespace HomotopicalAlgebra.DerivedSuspensionLoopAdjunction.Compatible

set_option backward.defeqAttrib.useBackward true
open Opposite
open PointedFramingAction (PointedSSet)
open scoped ZeroObject

variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [SimplicialCategory C]
  [HasZeroObject C] (a : CompatibleSimplicialMapping.Action C)
/-- The same original zero object supplies the coefficient zero maps. -/
local instance coefficientZeroMorphisms6 : HasZeroMorphisms C := HasZeroObject.zeroMorphismsOfZeroObject

/-- The actual pointed tensor collapses exactly the image of the supplied basepoint. -/
abbrev tensorObj (X : C) (K : PointedSSet.{vC}) : C :=
  pushout ((a.tensor.obj X).map K.hom)
    (0 : (a.tensor.obj X).obj (Δ[0] : SSet.{vC}) ⟶ (0 : C))

/-- The entire original unpointed tensor maps into its actual pointed quotient. -/
def tensorQuotient (X : C) (K : PointedSSet.{vC}) :
    (a.tensor.obj X).obj K.right ⟶ tensorObj a X K := pushout.inl _ _

/-- The actual pointed cotensor is the fiber over zero of the supplied basepoint restriction. -/
abbrev cotensorObj (Y : C) (K : PointedSSet.{vC}) : C :=
  pullback ((a.cotensor.map K.hom.op).app Y)
    (0 : (0 : C) ⟶ (a.cotensor.obj (op (Δ[0] : SSet.{vC}))).obj Y)

/-- The full actual pointed cotensor projects into the original unpointed cotensor. -/
def cotensorProjection (Y : C) (K : PointedSSet.{vC}) :
    cotensorObj a Y K ⟶ (a.cotensor.obj (op K.right)).obj Y := pullback.fst _ _

@[reassoc (attr := simp)]
theorem tensor_basepoint (X : C) (K : PointedSSet.{vC}) :
    (a.tensor.obj X).map K.hom ≫ tensorQuotient a X K = 0 :=
  pushout.condition.trans zero_comp

@[reassoc (attr := simp)]
theorem cotensor_basepoint (Y : C) (K : PointedSSet.{vC}) :
    cotensorProjection a Y K ≫ (a.cotensor.map K.hom.op).app Y = 0 :=
  pullback.condition.trans comp_zero

/-- The entire point-set tensor map is induced by the original action on the coefficient arrow. -/
def tensorMap {X X' : C} (i : X ⟶ X') (K : PointedSSet.{vC}) :
    tensorObj a X K ⟶ tensorObj a X' K :=
  pushout.map ((a.tensor.obj X).map K.hom)
    (0 : (a.tensor.obj X).obj (Δ[0] : SSet.{vC}) ⟶ (0 : C))
    ((a.tensor.obj X').map K.hom)
    (0 : (a.tensor.obj X').obj (Δ[0] : SSet.{vC}) ⟶ (0 : C))
    ((a.tensor.map i).app K.right) (𝟙 (0 : C)) ((a.tensor.map i).app (Δ[0] : SSet.{vC}))
    ((a.tensor.map i).naturality K.hom) (by simp)

@[reassoc (attr := simp)]
theorem tensorMap_quotient {X X' : C} (i : X ⟶ X') (K : PointedSSet.{vC}) :
    tensorQuotient a X K ≫ tensorMap a i K =
      (a.tensor.map i).app K.right ≫ tensorQuotient a X' K := pushout.inl_desc _ _ _

/-- The entire point-set cotensor map is induced by the same original coefficient arrow. -/
def cotensorMap {Y Y' : C} (p : Y ⟶ Y') (K : PointedSSet.{vC}) :
    cotensorObj a Y K ⟶ cotensorObj a Y' K :=
  pullback.map ((a.cotensor.map K.hom.op).app Y)
    (0 : (0 : C) ⟶ (a.cotensor.obj (op (Δ[0] : SSet.{vC}))).obj Y)
    ((a.cotensor.map K.hom.op).app Y')
    (0 : (0 : C) ⟶ (a.cotensor.obj (op (Δ[0] : SSet.{vC}))).obj Y')
    ((a.cotensor.obj (op K.right)).map p) (𝟙 (0 : C))
    ((a.cotensor.obj (op (Δ[0] : SSet.{vC}))).map p)
    ((a.cotensor.map K.hom.op).naturality p).symm (by simp)

@[reassoc (attr := simp)]
theorem cotensorMap_projection {Y Y' : C} (p : Y ⟶ Y') (K : PointedSSet.{vC}) :
    cotensorMap a p K ≫ cotensorProjection a Y' K =
      cotensorProjection a Y K ≫ (a.cotensor.obj (op K.right)).map p := pullback.lift_fst _ _ _

theorem tensorMap_id (X : C) (K : PointedSSet.{vC}) : tensorMap a (𝟙 X) K = 𝟙 _ := by
  apply pushout.hom_ext
  · change tensorQuotient a X K ≫ tensorMap a (𝟙 X) K = tensorQuotient a X K ≫ 𝟙 _
    rw [tensorMap_quotient, a.tensor.map_id X, NatTrans.id_app,
      Category.id_comp, Category.comp_id]
  · exact HasZeroObject.zeroIsInitial.hom_ext _ _

theorem tensorMap_comp {X X' X'' : C} (i : X ⟶ X') (j : X' ⟶ X'') (K : PointedSSet.{vC}) :
    tensorMap a (i ≫ j) K = tensorMap a i K ≫ tensorMap a j K := by
  apply pushout.hom_ext
  · change tensorQuotient a X K ≫ tensorMap a (i ≫ j) K =
      tensorQuotient a X K ≫ (tensorMap a i K ≫ tensorMap a j K)
    rw [tensorMap_quotient, a.tensor.map_comp i j, NatTrans.comp_app,
      tensorMap_quotient_assoc, tensorMap_quotient]
    exact Category.assoc _ _ _
  · exact HasZeroObject.zeroIsInitial.hom_ext _ _

theorem cotensorMap_id (Y : C) (K : PointedSSet.{vC}) : cotensorMap a (𝟙 Y) K = 𝟙 _ := by
  apply pullback.hom_ext
  · change cotensorMap a (𝟙 Y) K ≫ cotensorProjection a Y K = 𝟙 _ ≫ cotensorProjection a Y K
    rw [cotensorMap_projection, (a.cotensor.obj (op K.right)).map_id Y,
      Category.comp_id, Category.id_comp]
  · exact HasZeroObject.zeroIsTerminal.hom_ext _ _

theorem cotensorMap_comp {Y Y' Y'' : C} (p : Y ⟶ Y') (q : Y' ⟶ Y'') (K : PointedSSet.{vC}) :
    cotensorMap a (p ≫ q) K = cotensorMap a p K ≫ cotensorMap a q K := by
  apply pullback.hom_ext
  · change cotensorMap a (p ≫ q) K ≫ cotensorProjection a Y'' K =
      (cotensorMap a p K ≫ cotensorMap a q K) ≫ cotensorProjection a Y'' K
    rw [cotensorMap_projection, (a.cotensor.obj (op K.right)).map_comp p q,
      Category.assoc, cotensorMap_projection,
      ← Category.assoc (cotensorMap a p K) (cotensorProjection a Y' K), cotensorMap_projection,
      Category.assoc]
  · exact HasZeroObject.zeroIsTerminal.hom_ext _ _

/-- Fixed pointed tensoring is an actual endofunctor on the original point-set model. -/
@[implicit_reducible]
def tensorFunctor (K : PointedSSet.{vC}) : C ⥤ C where
  obj X := tensorObj a X K
  map i := tensorMap a i K
  map_id X := tensorMap_id a X K
  map_comp i j := tensorMap_comp a i j K

/-- Fixed pointed cotensoring is an actual endofunctor on that same point-set model. -/
@[implicit_reducible]
def cotensorFunctor (K : PointedSSet.{vC}) : C ⥤ C where
  obj Y := cotensorObj a Y K
  map p := cotensorMap a p K
  map_id Y := cotensorMap_id a Y K
  map_comp p q := cotensorMap_comp a p q K

theorem rawHomEquiv_zero (K : SSet.{vC}) (X Y : C) :
    (a.tensorCotensor.adj K).homEquiv X Y 0 = 0 := by
  let : PreservesLimitsOfSize.{0, 0} (a.cotensor.obj (op K)) :=
    (a.tensorCotensor.adj K).rightAdjoint_preservesLimits
  rw [Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]

theorem rawHomEquiv_symm_zero (K : SSet.{vC}) (X Y : C) :
    ((a.tensorCotensor.adj K).homEquiv X Y).symm 0 = 0 := by
  apply ((a.tensorCotensor.adj K).homEquiv X Y).injective
  rw [Equiv.apply_symm_apply, rawHomEquiv_zero]

/-- The actual pointed adjunct is the original action transpose followed by the zero-fiber lift. -/
def homForward (X : C) (K : PointedSSet.{vC}) (Y : C) (f : tensorObj a X K ⟶ Y) :
    X ⟶ cotensorObj a Y K :=
  pullback.lift ((a.tensorCotensor.adj K.right).homEquiv X Y (tensorQuotient a X K ≫ f)) 0 (by
    have hn := a.tensorCotensor.homEquiv_naturality_one K.hom (tensorQuotient a X K ≫ f)
    change (a.tensorCotensor.adj (Δ[0] : SSet.{vC})).homEquiv X Y
        ((a.tensor.obj X).map K.hom ≫ (tensorQuotient a X K ≫ f)) =
      (a.tensorCotensor.adj K.right).homEquiv X Y (tensorQuotient a X K ≫ f) ≫
        (a.cotensor.map K.hom.op).app Y at hn
    rw [← Category.assoc, tensor_basepoint, zero_comp, rawHomEquiv_zero] at hn
    simpa only [comp_zero] using hn.symm)

@[reassoc]
theorem homForward_projection (X : C) (K : PointedSSet.{vC}) (Y : C) (f : tensorObj a X K ⟶ Y) :
    homForward a X K Y f ≫ cotensorProjection a Y K =
      (a.tensorCotensor.adj K.right).homEquiv X Y (tensorQuotient a X K ≫ f) :=
  pullback.lift_fst _ _ _

/-- The inverse pointed adjunct is the original inverse transpose and its actual quotient descent. -/
def homBackward (X : C) (K : PointedSSet.{vC}) (Y : C) (f : X ⟶ cotensorObj a Y K) :
    tensorObj a X K ⟶ Y :=
  pushout.desc (((a.tensorCotensor.adj K.right).homEquiv X Y).symm
    (f ≫ cotensorProjection a Y K)) 0 (by
    have hn := a.tensorCotensor.homEquiv_symm_naturality_one K.hom (f ≫ cotensorProjection a Y K)
    change ((a.tensorCotensor.adj (Δ[0] : SSet.{vC})).homEquiv X Y).symm
        ((f ≫ cotensorProjection a Y K) ≫ (a.cotensor.map K.hom.op).app Y) =
      (a.tensor.obj X).map K.hom ≫ ((a.tensorCotensor.adj K.right).homEquiv X Y).symm
        (f ≫ cotensorProjection a Y K) at hn
    rw [Category.assoc, cotensor_basepoint, comp_zero, rawHomEquiv_symm_zero] at hn
    simpa only [zero_comp] using hn.symm)

@[reassoc]
theorem homBackward_quotient (X : C) (K : PointedSSet.{vC}) (Y : C) (f : X ⟶ cotensorObj a Y K) :
    tensorQuotient a X K ≫ homBackward a X K Y f =
      ((a.tensorCotensor.adj K.right).homEquiv X Y).symm (f ≫ cotensorProjection a Y K) :=
  pushout.inl_desc _ _ _

/-- The full actual pointed tensor/cotensor Hom equivalence retains both original inverse maps. -/
def homEquiv (X : C) (K : PointedSSet.{vC}) (Y : C) :
    (tensorObj a X K ⟶ Y) ≃ (X ⟶ cotensorObj a Y K) where
  toFun := homForward a X K Y
  invFun := homBackward a X K Y
  left_inv f := by
    apply pushout.hom_ext
    · change tensorQuotient a X K ≫ homBackward a X K Y (homForward a X K Y f) =
        tensorQuotient a X K ≫ f
      rw [homBackward_quotient, homForward_projection, Equiv.symm_apply_apply]
    · exact HasZeroObject.zeroIsInitial.hom_ext _ _
  right_inv f := by
    apply pullback.hom_ext
    · change homForward a X K Y (homBackward a X K Y f) ≫ cotensorProjection a Y K =
        f ≫ cotensorProjection a Y K
      rw [homForward_projection, homBackward_quotient, Equiv.apply_symm_apply]
    · exact HasZeroObject.zeroIsTerminal.hom_ext _ _

/-- Every original coefficient source map retains the entire pointed adjunct. -/
theorem homEquiv_source {X X' : C} (i : X ⟶ X') (K : PointedSSet.{vC}) (Y : C)
    (f : tensorObj a X' K ⟶ Y) :
    homEquiv a X K Y (tensorMap a i K ≫ f) = i ≫ homEquiv a X' K Y f := by
  apply pullback.hom_ext
  · change homForward a X K Y (tensorMap a i K ≫ f) ≫ cotensorProjection a Y K =
      (i ≫ homForward a X' K Y f) ≫ cotensorProjection a Y K
    rw [homForward_projection, Category.assoc, homForward_projection,
      ← Category.assoc (tensorQuotient a X K), tensorMap_quotient, Category.assoc]
    exact a.tensorCotensor.homEquiv_naturality_two i (tensorQuotient a X' K ≫ f)
  · exact HasZeroObject.zeroIsTerminal.hom_ext _ _

/-- Every original coefficient target map retains the entire pointed adjunct. -/
theorem homEquiv_target (X : C) (K : PointedSSet.{vC}) {Y Y' : C} (p : Y ⟶ Y')
    (f : tensorObj a X K ⟶ Y) :
    homEquiv a X K Y' (f ≫ p) = homEquiv a X K Y f ≫ cotensorMap a p K := by
  apply pullback.hom_ext
  · change homForward a X K Y' (f ≫ p) ≫ cotensorProjection a Y' K =
      (homForward a X K Y f ≫ cotensorMap a p K) ≫ cotensorProjection a Y' K
    rw [homForward_projection, Category.assoc, cotensorMap_projection,
      homForward_projection_assoc, ← Category.assoc,
      Adjunction.homEquiv_naturality_right]
  · exact HasZeroObject.zeroIsTerminal.hom_ext _ _

/-- The compatible action constructs the point-set pointed tensor/cotensor endoadjunction. -/
def adjunction (K : PointedSSet.{vC}) : tensorFunctor a K ⊣ cotensorFunctor a K :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y => homEquiv a X K Y
      homEquiv_naturality_left_symm := by
        intro X X' Y i f
        change (homEquiv a X K Y).symm (i ≫ f) =
          tensorMap a i K ≫ (homEquiv a X' K Y).symm f
        apply (homEquiv a X K Y).injective
        rw [Equiv.apply_symm_apply, homEquiv_source, Equiv.apply_symm_apply]
      homEquiv_naturality_right := by
        intro X Y Y' f p
        exact homEquiv_target a X K p f }

theorem adjunction_homEquiv (K : PointedSSet.{vC}) (X Y : C) (f : tensorObj a X K ⟶ Y) :
    (adjunction a K).homEquiv X Y f = homEquiv a X K Y f := by
  unfold adjunction
  rw [Adjunction.mkOfHomEquiv_homEquiv]

/-- The original action pushout product descends through the entire source pointed quotient. -/
def tensorPushoutQuotient {X X' : C} (i : X ⟶ X') (K : PointedSSet.{vC})
    (s : a.tensor.PushoutObjObj i K.hom) : s.pt ⟶ tensorObj a X K :=
  s.isPushout.desc 0 (tensorQuotient a X K) (by rw [comp_zero, tensor_basepoint])

@[reassoc (attr := simp)]
theorem tensorPushoutQuotient_inl {X X' : C} (i : X ⟶ X') (K : PointedSSet.{vC})
    (s : a.tensor.PushoutObjObj i K.hom) : s.inl ≫ tensorPushoutQuotient a i K s = 0 :=
  s.isPushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem tensorPushoutQuotient_inr {X X' : C} (i : X ⟶ X') (K : PointedSSet.{vC})
    (s : a.tensor.PushoutObjObj i K.hom) :
    s.inr ≫ tensorPushoutQuotient a i K s = tensorQuotient a X K :=
  s.isPushout.inr_desc _ _ _

/-- The actual pointed tensor arrow is a cobase change of the original basepoint pushout product. -/
theorem tensorMap_isPushout {X X' : C} (i : X ⟶ X') (K : PointedSSet.{vC})
    (s : a.tensor.PushoutObjObj i K.hom) :
    IsPushout s.ι (tensorPushoutQuotient a i K s)
      (tensorQuotient a X' K) (tensorMap a i K) := by
  apply IsPushout.mk'
  · apply s.hom_ext
    · rw [← Category.assoc s.inl, s.inl_ι, tensor_basepoint,
        ← Category.assoc s.inl, tensorPushoutQuotient_inl, zero_comp]
    · rw [← Category.assoc s.inr, s.inr_ι,
        ← Category.assoc s.inr, tensorPushoutQuotient_inr]
      exact (tensorMap_quotient a i K).symm
  · intro Z f g h₁ _
    exact pushout.hom_ext h₁ (HasZeroObject.zeroIsInitial.hom_ext _ _)
  · intro Z u v h
    have hu : (a.tensor.obj X').map K.hom ≫ u = 0 := by
      have ht := congrArg (fun z => s.inl ≫ z) h
      simpa only [← Category.assoc, s.inl_ι, tensorPushoutQuotient_inl, zero_comp] using ht
    let l : tensorObj a X' K ⟶ Z := pushout.desc u 0 (by simpa only [zero_comp] using hu)
    refine ⟨l, pushout.inl_desc _ _ _, ?_⟩
    apply pushout.hom_ext
    · change tensorQuotient a X K ≫ (tensorMap a i K ≫ l) = tensorQuotient a X K ≫ v
      rw [tensorMap_quotient_assoc]
      dsimp only [l]
      rw [tensorQuotient, pushout.inl_desc]
      have ht := congrArg (fun z => s.inr ≫ z) h
      simpa only [← Category.assoc, s.inr_ι, tensorPushoutQuotient_inr] using ht
    · exact HasZeroObject.zeroIsInitial.hom_ext _ _

/-- Cofibrancy of the actual pointed weight and the original action PP laws give the Quillen pair. -/
theorem adjunction_isQuillen (K : PointedSSet.{vC}) [IsCofibrant K] :
    (adjunction a K).IsQuillenAdjunction := by
  let f : Under.mk (𝟙 (Δ[0] : SSet.{vC})) ⟶ K := Under.homMk K.hom (Category.id_comp _)
  have hf : Cofibration f := (isCofibrant_iff_of_isInitial f Under.mkIdInitial).mp inferInstance
  have hK : cofibrations SSet.{vC} K.hom :=
    (cofibration_iff K.hom).mp ((cofibrations_under_iff (Δ[0] : SSet.{vC}) f).mp hf)
  constructor
  · intro X X' i hi
    let s := Functor.PushoutObjObj.ofHasPushout a.tensor i K.hom
    exact (cofibrations C).of_isPushout (tensorMap_isPushout a i K s).flip
      (a.cof_cof i K.hom s hi hK)
  · intro X X' i hi
    let s := Functor.PushoutObjObj.ofHasPushout a.tensor i K.hom
    exact (trivialCofibrations C).of_isPushout (tensorMap_isPushout a i K s).flip
      (a.trivial_cof i K.hom s hi hK)

/-- The actual original cofibrant circle gives the point-set suspension/loop endoadjunction. -/
abbrev circleAdjunction : tensorFunctor a circle.{vC} ⊣ cotensorFunctor a circle.{vC} :=
  adjunction a circle

/-- The model action axiom proves the actual circle endoadjunction is Quillen. -/
theorem circleAdjunction_isQuillen : (circleAdjunction a).IsQuillenAdjunction := by
  let : IsCofibrant circle.{vC} := circle_isCofibrant
  exact adjunction_isQuillen a circle

attribute [local instance] circleAdjunction_isQuillen

/-- The full total-derived circle adjunction uses the same original Q and R records. -/
def derivedData (d : GeneratedFunctorialReplacements.Data (C := C)) :
    QuillenDerivedAdjunctionData (circleAdjunction a) :=
  DerivedAdjunctionCoherence.chosenDerivedAdjunctionData (circleAdjunction a) d d

/-- The genuine total left derived circle tensor on the original ordinary homotopy category. -/
abbrev derivedSuspension (d : GeneratedFunctorialReplacements.Data (C := C)) :=
  DerivedFunctorCoherence.left (circleAdjunction a) d

/-- The genuine total right derived circle cotensor retains the original fibrant replacement. -/
abbrev derivedLoops (d : GeneratedFunctorialReplacements.Data (C := C)) :=
  DerivedFunctorCoherence.right (circleAdjunction a) d

/-- Every ordinary-Ho object and arrow participates in the same full total-derived circle adjunction. -/
abbrev derivedAdjunction (d : GeneratedFunctorialReplacements.Data (C := C)) :
    derivedSuspension a d ⊣ derivedLoops a d :=
  DerivedAdjunctionCoherence.chosenAdjunction (circleAdjunction a) d d

/-- The total left derived object is exactly the actual circle tensor of the original QX. -/
theorem derivedSuspension_obj (d : GeneratedFunctorialReplacements.Data (C := C)) (X : C) :
    (derivedSuspension a d).obj ((weakEquivalences C).Q.obj X) =
      (weakEquivalences C).Q.obj (tensorObj a (d.Q.obj X) circle) := rfl

/-- The total right derived object is exactly the actual circle cotensor of the original RY. -/
theorem derivedLoops_obj (d : GeneratedFunctorialReplacements.Data (C := C)) (Y : C) :
    (derivedLoops a d).obj ((weakEquivalences C).Q.obj Y) =
      (weakEquivalences C).Q.obj (cotensorObj a (d.R.obj Y) circle) := rfl

theorem derivedSuspension_map (d : GeneratedFunctorialReplacements.Data (C := C))
    {X X' : C} (i : X ⟶ X') :
    (derivedSuspension a d).map ((weakEquivalences C).Q.map i) =
      (weakEquivalences C).Q.map (tensorMap a (d.Q.map i) circle) :=
  DerivedFunctorCoherence.left_map (circleAdjunction a) d i

theorem derivedLoops_map (d : GeneratedFunctorialReplacements.Data (C := C))
    {Y Y' : C} (p : Y ⟶ Y') :
    (derivedLoops a d).map ((weakEquivalences C).Q.map p) =
      (weakEquivalences C).Q.map (cotensorMap a (d.R.map p) circle) :=
  DerivedFunctorCoherence.right_map (circleAdjunction a) d p

section FrameComparison

open PointedFramingAction

variable (d : GeneratedFunctorialReplacements.Data (C := C))

/-- The compatible cotensor frame is formed on the same original R object and every original R map. -/
abbrev actionFrame : C ⥤ SimplicialObject C := d.R ⋙ CompatibleCotensorFraming.resolution a

omit [HasZeroObject C] in
theorem actionFrame_obj (Y : C) :
    (actionFrame a d).obj Y = (CompatibleCotensorFraming.resolution a).obj (d.R.obj Y) := rfl

omit [HasZeroObject C] in
theorem actionFrame_map {Y Y' : C} (p : Y ⟶ Y') :
    (actionFrame a d).map p = (CompatibleCotensorFraming.resolution a).map (d.R.map p) := rfl

/-- The pointed action mapping object has exactly the same original Q and R endpoints. -/
abbrev actionRightSpace (X Y : C) : PointedSSet.{vC} :=
  pointedRightHom (d.Q.obj X) ((actionFrame a d).obj Y)

/-- The comparison retains the entire original left factory frame and the entire compatible R frame. -/
abbrev actionTwoSidedSpace (X Y : C) : PointedSSet.{vC} :=
  pointedHom ((leftFrame d).obj X) ((actionFrame a d).obj Y)

/-- The complete original Q-resolution map gives the actual compatible right-to-two-sided leg. -/
def rightToTwoSided (X Y : C) : actionRightSpace a d X Y ⟶ actionTwoSidedSpace a d X Y :=
  pointedHomPrecomp ((leftResolution d).app X) ((actionFrame a d).obj Y)

/-- The compatible cotensor coaugmentation on the original RY gives the other actual frame leg. -/
def leftToTwoSided (X Y : C) : pointedLeftSpace d X Y ⟶ actionTwoSidedSpace a d X Y :=
  pointedHomPostcomp ((leftFrame d).obj X)
    ((CompatibleCotensorFraming.coaugmentation a).app (d.R.obj Y))

omit [HasZeroObject C] in
/-- Fibrancy of the actual original RY proves every compatible-frame matching map is a fibration. -/
theorem actionFrame_matching_fibration (Y : C) (j : SimplexCategoryᵒᵖ) :
    fibrations C (ReedyStructure.matchingMap SimplexCategory.reedyOp ((actionFrame a d).obj Y) j) := by
  let : IsFibrant (d.R.obj Y) := d.r_fibrant Y
  exact CompatibleCotensorFraming.matchingMap_fibration a (d.R.obj Y) j.unop

/-- The original full augmentation and the actual matching fibrations prove the first leg weak. -/
theorem rightToTwoSided_weak (X Y : C) :
    weakEquivalences PointedSSet.{vC} (rightToTwoSided a d X Y) := by
  change weakEquivalences SSet.{vC}
    (ResolutionHomComplex.fromAugmentation ((leftResolution d).app X) ((actionFrame a d).obj Y))
  let : IsCofibrant (d.Q.obj X) := d.q_cofibrant X
  exact (weakEquivalence_iff _).mp
    (GeneratedFrameHomComparison.fromAugmentation_weak _ _ _
      (leftFrame_latching_cofibration d X) (actionFrame_matching_fibration a d Y)
      (leftResolution_weak d X))

/-- The genuine action coaugmentation and original left latching maps prove the other leg weak. -/
theorem leftToTwoSided_weak (X Y : C) :
    weakEquivalences PointedSSet.{vC} (leftToTwoSided a d X Y) := by
  change weakEquivalences SSet.{vC}
    (ResolutionHomComplex.fromCoaugmentation ((leftFrame d).obj X)
      ((CompatibleCotensorFraming.coaugmentation a).app (d.R.obj Y)))
  let : IsFibrant (d.R.obj Y) := d.r_fibrant Y
  exact (weakEquivalence_iff _).mp
    (GeneratedFrameHomComparison.fromCoaugmentation_weak _ _ _
      (leftFrame_latching_cofibration d X) (actionFrame_matching_fibration a d Y)
      (fun j => (weakEquivalence_iff _).mp
        (CompatibleCotensorFraming.coaugmentation_weak a (d.R.obj Y) j)))

/-- Every original Q source arrow induces the same full compatible mapping-space precomposition. -/
def actionRightSourceMap {X X' : C} (f : X ⟶ X') (Y : C) :
    actionRightSpace a d X' Y ⟶ actionRightSpace a d X Y :=
  pointedHomPrecomp ((CosimplicialObject.const C).map (d.Q.map f)) ((actionFrame a d).obj Y)

/-- Every original R target arrow induces the same full compatible mapping-space postcomposition. -/
def actionRightTargetMap (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    actionRightSpace a d X Y ⟶ actionRightSpace a d X Y' :=
  pointedHomPostcomp ((CosimplicialObject.const C).obj (d.Q.obj X)) ((actionFrame a d).map g)

/-- The same complete original source frame map acts on the compatible two-sided HFC. -/
def actionTwoSidedSourceMap {X X' : C} (f : X ⟶ X') (Y : C) :
    actionTwoSidedSpace a d X' Y ⟶ actionTwoSidedSpace a d X Y :=
  pointedHomPrecomp ((leftFrame d).map f) ((actionFrame a d).obj Y)

/-- The same complete original target frame map acts on the compatible two-sided HFC. -/
def actionTwoSidedTargetMap (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    actionTwoSidedSpace a d X Y ⟶ actionTwoSidedSpace a d X Y' :=
  pointedHomPostcomp ((leftFrame d).obj X) ((actionFrame a d).map g)

/-- The entire original augmentation leg retains every original source arrow. -/
theorem rightToTwoSided_source {X X' : C} (f : X ⟶ X') (Y : C) :
    actionRightSourceMap a d f Y ≫ rightToTwoSided a d X Y =
      rightToTwoSided a d X' Y ≫ actionTwoSidedSourceMap a d f Y := by
  apply Under.UnderMorphism.ext
  change ResolutionHomComplex.precomp ((CosimplicialObject.const C).map (d.Q.map f))
      ((actionFrame a d).obj Y) ≫ ResolutionHomComplex.precomp ((leftResolution d).app X)
        ((actionFrame a d).obj Y) =
    ResolutionHomComplex.precomp ((leftResolution d).app X') ((actionFrame a d).obj Y) ≫
      ResolutionHomComplex.precomp ((leftFrame d).map f) ((actionFrame a d).obj Y)
  rw [← ResolutionHomComplex.precomp_comp, ← ResolutionHomComplex.precomp_comp]
  exact congrArg (fun b => ResolutionHomComplex.precomp b ((actionFrame a d).obj Y))
    ((leftResolution d).naturality f).symm

/-- The entire compatible coaugmentation leg retains every original source arrow. -/
theorem leftToTwoSided_source {X X' : C} (f : X ⟶ X') (Y : C) :
    pointedLeftSourceMap d f Y ≫ leftToTwoSided a d X Y =
      leftToTwoSided a d X' Y ≫ actionTwoSidedSourceMap a d f Y :=
  pointedHomPrecomp_postcomp ((leftFrame d).map f)
    ((CompatibleCotensorFraming.coaugmentation a).app (d.R.obj Y))

/-- The full original augmentation comparison retains every actual R target map. -/
theorem rightToTwoSided_target (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    actionRightTargetMap a d X g ≫ rightToTwoSided a d X Y' =
      rightToTwoSided a d X Y ≫ actionTwoSidedTargetMap a d X g :=
  (pointedHomPrecomp_postcomp ((leftResolution d).app X) ((actionFrame a d).map g)).symm

/-- The full compatible coaugmentation comparison retains every actual R target map. -/
theorem leftToTwoSided_target (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    pointedLeftTargetMap d X g ≫ leftToTwoSided a d X Y' =
      leftToTwoSided a d X Y ≫ actionTwoSidedTargetMap a d X g := by
  apply Under.UnderMorphism.ext
  change ResolutionHomComplex.postcomp ((leftFrame d).obj X)
      ((SimplicialObject.const C).map (d.R.map g)) ≫
        ResolutionHomComplex.postcomp ((leftFrame d).obj X)
          ((CompatibleCotensorFraming.coaugmentation a).app (d.R.obj Y')) =
    ResolutionHomComplex.postcomp ((leftFrame d).obj X)
      ((CompatibleCotensorFraming.coaugmentation a).app (d.R.obj Y)) ≫
        ResolutionHomComplex.postcomp ((leftFrame d).obj X) ((actionFrame a d).map g)
  rw [← ResolutionHomComplex.postcomp_comp, ← ResolutionHomComplex.postcomp_comp]
  exact congrArg (ResolutionHomComplex.postcomp ((leftFrame d).obj X))
    ((CompatibleCotensorFraming.coaugmentation a).naturality (d.R.map g))

/-- The genuine compatible right frame leg becomes its actual localization isomorphism. -/
def rightComparisonIso (X Y : C) :
    pointedProjection.obj (actionRightSpace a d X Y) ≅
      pointedProjection.obj (actionTwoSidedSpace a d X Y) := by
  let : IsIso (pointedProjection.map (rightToTwoSided a d X Y)) :=
    Localization.inverts pointedProjection (weakEquivalences PointedSSet.{vC}) _
      (rightToTwoSided_weak a d X Y)
  exact asIso (pointedProjection.map (rightToTwoSided a d X Y))

/-- The genuine compatible left frame leg becomes its actual localization isomorphism. -/
def leftComparisonIso (X Y : C) :
    pointedLeftHoSpace d X Y ≅ pointedProjection.obj (actionTwoSidedSpace a d X Y) := by
  let : IsIso (pointedProjection.map (leftToTwoSided a d X Y)) :=
    Localization.inverts pointedProjection (weakEquivalences PointedSSet.{vC}) _
      (leftToTwoSided_weak a d X Y)
  exact asIso (pointedProjection.map (leftToTwoSided a d X Y))

/-- Both full genuine weak frame legs compare the original left HFC with the compatible action HFC. -/
def leftActionIso (X Y : C) :
    pointedLeftHoSpace d X Y ≅ pointedProjection.obj (actionRightSpace a d X Y) :=
  leftComparisonIso a d X Y ≪≫ (rightComparisonIso a d X Y).symm

/-- The original right HFC comparison also retains the complete original ordinary left/right span. -/
def rightActionIso (X Y : C) :
    pointedRightHoSpace d X Y ≅ pointedProjection.obj (actionRightSpace a d X Y) :=
  (pointedLeftRightIso d X Y).symm ≪≫ leftActionIso a d X Y

theorem leftActionIso_hom (X Y : C) :
    (leftActionIso a d X Y).hom = pointedProjection.map (leftToTwoSided a d X Y) ≫
      (rightComparisonIso a d X Y).inv := rfl

theorem rightActionIso_hom (X Y : C) :
    (rightActionIso a d X Y).hom = (pointedLeftRightIso d X Y).inv ≫
      (leftActionIso a d X Y).hom := rfl

theorem leftActionIso_inv (X Y : C) :
    (leftActionIso a d X Y).inv = pointedProjection.map (rightToTwoSided a d X Y) ≫
      (leftComparisonIso a d X Y).inv := rfl

theorem rightActionIso_inv (X Y : C) :
    (rightActionIso a d X Y).inv = (leftActionIso a d X Y).inv ≫
      (pointedLeftRightIso d X Y).hom := rfl

/-- Both genuine weak frame legs compare naturally under every original R target map. -/
theorem leftActionIso_target (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    pointedProjection.map (pointedLeftTargetMap d X g) ≫ (leftActionIso a d X Y').hom =
      (leftActionIso a d X Y).hom ≫ pointedProjection.map (actionRightTargetMap a d X g) := by
  have hL : pointedProjection.map (pointedLeftTargetMap d X g) ≫ (leftComparisonIso a d X Y').hom =
      (leftComparisonIso a d X Y).hom ≫ pointedProjection.map (actionTwoSidedTargetMap a d X g) :=
    (pointedProjection.map_comp _ _).symm.trans
      ((congrArg pointedProjection.map (leftToTwoSided_target a d X g)).trans (pointedProjection.map_comp _ _))
  have hR : pointedProjection.map (actionRightTargetMap a d X g) ≫ (rightComparisonIso a d X Y').hom =
      (rightComparisonIso a d X Y).hom ≫ pointedProjection.map (actionTwoSidedTargetMap a d X g) :=
    (pointedProjection.map_comp _ _).symm.trans
      ((congrArg pointedProjection.map (rightToTwoSided_target a d X g)).trans (pointedProjection.map_comp _ _))
  apply (cancel_mono (rightComparisonIso a d X Y').hom).mp
  change (pointedProjection.map (pointedLeftTargetMap d X g) ≫
      ((leftComparisonIso a d X Y').hom ≫ (rightComparisonIso a d X Y').inv)) ≫
        (rightComparisonIso a d X Y').hom =
    (((leftComparisonIso a d X Y).hom ≫ (rightComparisonIso a d X Y).inv) ≫
      pointedProjection.map (actionRightTargetMap a d X g)) ≫ (rightComparisonIso a d X Y').hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hR]
  simp only [Iso.inv_hom_id_assoc]
  exact hL

/-- Both genuine weak frame legs compare naturally under every original Q source map. -/
theorem leftActionIso_source {X X' : C} (f : X ⟶ X') (Y : C) :
    pointedProjection.map (pointedLeftSourceMap d f Y) ≫ (leftActionIso a d X Y).hom =
      (leftActionIso a d X' Y).hom ≫ pointedProjection.map (actionRightSourceMap a d f Y) := by
  have hL : pointedProjection.map (pointedLeftSourceMap d f Y) ≫ (leftComparisonIso a d X Y).hom =
      (leftComparisonIso a d X' Y).hom ≫ pointedProjection.map (actionTwoSidedSourceMap a d f Y) :=
    (pointedProjection.map_comp _ _).symm.trans
      ((congrArg pointedProjection.map (leftToTwoSided_source a d f Y)).trans (pointedProjection.map_comp _ _))
  have hR : pointedProjection.map (actionRightSourceMap a d f Y) ≫ (rightComparisonIso a d X Y).hom =
      (rightComparisonIso a d X' Y).hom ≫ pointedProjection.map (actionTwoSidedSourceMap a d f Y) :=
    (pointedProjection.map_comp _ _).symm.trans
      ((congrArg pointedProjection.map (rightToTwoSided_source a d f Y)).trans (pointedProjection.map_comp _ _))
  apply (cancel_mono (rightComparisonIso a d X Y).hom).mp
  change (pointedProjection.map (pointedLeftSourceMap d f Y) ≫
      ((leftComparisonIso a d X Y).hom ≫ (rightComparisonIso a d X Y).inv)) ≫
        (rightComparisonIso a d X Y).hom =
    (((leftComparisonIso a d X' Y).hom ≫ (rightComparisonIso a d X' Y).inv) ≫
      pointedProjection.map (actionRightSourceMap a d f Y)) ≫ (rightComparisonIso a d X Y).hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hR]
  simp only [Iso.inv_hom_id_assoc]
  exact hL

/-- The complete ordinary-right-to-action comparison retains every original target arrow. -/
theorem rightActionIso_target (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    pointedProjection.map (pointedRightTargetMap d X g) ≫ (rightActionIso a d X Y').hom =
      (rightActionIso a d X Y).hom ≫ pointedProjection.map (actionRightTargetMap a d X g) := by
  have h := congrArg (fun b => (pointedLeftRightIso d X Y).inv ≫ b ≫
      (pointedLeftRightIso d X Y').inv) (pointedLeftRightIso_target d X g)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc] at h
  rw [rightActionIso_hom, rightActionIso_hom,
    ← Category.assoc (pointedProjection.map (pointedRightTargetMap d X g)), ← h,
    Category.assoc, leftActionIso_target, ← Category.assoc]

/-- The complete ordinary-right-to-action comparison retains every original source arrow. -/
theorem rightActionIso_source {X X' : C} (f : X ⟶ X') (Y : C) :
    pointedProjection.map (pointedRightSourceMap d f Y) ≫ (rightActionIso a d X Y).hom =
      (rightActionIso a d X' Y).hom ≫ pointedProjection.map (actionRightSourceMap a d f Y) := by
  have h := congrArg (fun b => (pointedLeftRightIso d X' Y).inv ≫ b ≫
      (pointedLeftRightIso d X Y).inv) (pointedLeftRightIso_source d f Y)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc] at h
  rw [rightActionIso_hom, rightActionIso_hom,
    ← Category.assoc (pointedProjection.map (pointedRightSourceMap d f Y)), ← h,
    Category.assoc, leftActionIso_source, ← Category.assoc]

end FrameComparison

section UnpointedCotensorComparison

omit [HasZeroObject C]
variable [HasLimitsOfSize.{0, vC} C]

/-- The actual action Hom functions and original simplex calculation identify both full cotensors. -/
def cotensorFrameHomEquiv (X : C) (K : SSet.{vC}) (Y : C) :
    (X ⟶ (a.cotensor.obj (op K)).obj Y) ≃
      (X ⟶ PointedFramingAction.cotensor ((CompatibleCotensorFraming.resolution a).obj Y) K) :=
  (CompatibleCotensorFraming.homEquiv a X K Y).trans
    ((Iso.homCongr (Iso.refl K) (CompatibleCotensorFraming.complexIso a X Y).symm).trans
      (PointedFramingAction.cotensorHomEquiv X K ((CompatibleCotensorFraming.resolution a).obj Y)).symm)

theorem cotensorFrameHomEquiv_apply (X : C) (K : SSet.{vC}) (Y : C)
    (f : X ⟶ (a.cotensor.obj (op K)).obj Y) :
    cotensorFrameHomEquiv a X K Y f =
      (PointedFramingAction.cotensorHomEquiv X K ((CompatibleCotensorFraming.resolution a).obj Y)).symm
        (CompatibleCotensorFraming.homEquiv a X K Y f ≫ (CompatibleCotensorFraming.complexIso a X Y).inv) := by
  simp only [cotensorFrameHomEquiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv,
    Iso.symm_hom, Category.id_comp]

/-- The weighted cotensor comparison preserves every full source map. -/
theorem cotensorFrameHomEquiv_source {X X' : C} (i : X ⟶ X') (K : SSet.{vC}) (Y : C)
    (f : X' ⟶ (a.cotensor.obj (op K)).obj Y) :
    cotensorFrameHomEquiv a X K Y (i ≫ f) = i ≫ cotensorFrameHomEquiv a X' K Y f := by
  rw [cotensorFrameHomEquiv_apply, cotensorFrameHomEquiv_apply]
  apply (PointedFramingAction.cotensorHomEquiv X K ((CompatibleCotensorFraming.resolution a).obj Y)).injective
  rw [Equiv.apply_symm_apply, PointedFramingAction.cotensorHomEquiv_source, Equiv.apply_symm_apply,
    CompatibleCotensorFraming.homEquiv_source]
  have hn := congrArg (fun b => b.app Y) ((CompatibleCotensorFraming.calculation a).inv.naturality i.op)
  change (((SimplicialCategory.sHomFunctor C).map i.op).app Y) ≫
      (CompatibleCotensorFraming.complexIso a X Y).inv =
    (CompatibleCotensorFraming.complexIso a X' Y).inv ≫
      ResolutionHomComplex.precomp ((CosimplicialObject.const C).map i)
        ((CompatibleCotensorFraming.resolution a).obj Y) at hn
  rw [Category.assoc]
  exact congrArg (fun b => CompatibleCotensorFraming.homEquiv a X' K Y f ≫ b) hn

/-- The entire weighted cotensor comparison preserves every action-parameter map. -/
theorem cotensorFrameHomEquiv_parameter (X : C) {K L : SSet.{vC}} (k : K ⟶ L) (Y : C)
    (f : X ⟶ (a.cotensor.obj (op L)).obj Y) :
    cotensorFrameHomEquiv a X K Y (f ≫ (a.cotensor.map k.op).app Y) =
      cotensorFrameHomEquiv a X L Y f ≫
        PointedFramingAction.cotensorMap (𝟙 ((CompatibleCotensorFraming.resolution a).obj Y)) k := by
  apply (PointedFramingAction.cotensorHomEquiv X K ((CompatibleCotensorFraming.resolution a).obj Y)).injective
  rw [cotensorFrameHomEquiv_apply, Equiv.apply_symm_apply, PointedFramingAction.cotensorHomEquiv_parameter,
    cotensorFrameHomEquiv_apply, Equiv.apply_symm_apply, CompatibleCotensorFraming.homEquiv_parameter]
  exact Category.assoc _ _ _

/-- The entire weighted cotensor comparison preserves every original action target map. -/
theorem cotensorFrameHomEquiv_target (X : C) (K : SSet.{vC}) {Y Y' : C} (p : Y ⟶ Y')
    (f : X ⟶ (a.cotensor.obj (op K)).obj Y) :
    cotensorFrameHomEquiv a X K Y' (f ≫ (a.cotensor.obj (op K)).map p) =
      cotensorFrameHomEquiv a X K Y f ≫
        PointedFramingAction.cotensorMap ((CompatibleCotensorFraming.resolution a).map p) (𝟙 K) := by
  apply (PointedFramingAction.cotensorHomEquiv X K ((CompatibleCotensorFraming.resolution a).obj Y')).injective
  rw [cotensorFrameHomEquiv_apply, Equiv.apply_symm_apply, PointedFramingAction.cotensorHomEquiv_target,
    cotensorFrameHomEquiv_apply, Equiv.apply_symm_apply, CompatibleCotensorFraming.homEquiv_target]
  have hn := (((CompatibleCotensorFraming.calculation a).inv.app (op X)).naturality p)
  change (((SimplicialCategory.sHomFunctor C).obj (op X)).map p) ≫
      (CompatibleCotensorFraming.complexIso a X Y').inv =
    (CompatibleCotensorFraming.complexIso a X Y).inv ≫
      ResolutionHomComplex.postcomp ((CosimplicialObject.const C).obj X)
        ((CompatibleCotensorFraming.resolution a).map p) at hn
  rw [Category.assoc]
  exact congrArg (fun b => CompatibleCotensorFraming.homEquiv a X K Y f ≫ b) hn

/-- The weighted full simplex cotensor is the same actual external cotensor on its original carrier. -/
def unpointedFrameIso (Y : C) (K : SSet.{vC}) :
    (a.cotensor.obj (op K)).obj Y ≅
      PointedFramingAction.cotensor ((CompatibleCotensorFraming.resolution a).obj Y) K := by
  let U := (a.cotensor.obj (op K)).obj Y
  let V := PointedFramingAction.cotensor ((CompatibleCotensorFraming.resolution a).obj Y) K
  let e (X : C) := cotensorFrameHomEquiv a X K Y
  let f : U ⟶ V := e U (𝟙 U)
  let g : V ⟶ U := (e V).symm (𝟙 V)
  refine ⟨f, g, ?_, ?_⟩
  · apply (e U).injective
    have hn := cotensorFrameHomEquiv_source a f K Y g
    change e U (f ≫ g) = f ≫ e V g at hn
    rw [hn]
    dsimp only [g]
    rw [Equiv.apply_symm_apply, Category.comp_id]
  · have hn := cotensorFrameHomEquiv_source a g K Y (𝟙 U)
    change e V (g ≫ 𝟙 U) = g ≫ f at hn
    rw [Category.comp_id] at hn
    rw [← hn]
    dsimp only [g]
    exact (e V).apply_symm_apply _

theorem unpointedFrameIso_hom (Y : C) (K : SSet.{vC}) :
    (unpointedFrameIso a Y K).hom =
      cotensorFrameHomEquiv a ((a.cotensor.obj (op K)).obj Y) K Y (𝟙 _) := rfl

theorem unpointedFrameIso_inv (Y : C) (K : SSet.{vC}) :
    (unpointedFrameIso a Y K).inv =
      (cotensorFrameHomEquiv a
        (PointedFramingAction.cotensor ((CompatibleCotensorFraming.resolution a).obj Y) K) K Y).symm (𝟙 _) := rfl

/-- The actual external restriction and the full simplex restriction are the same complete map. -/
theorem unpointedFrameIso_parameter (Y : C) {K L : SSet.{vC}} (k : K ⟶ L) :
    (a.cotensor.map k.op).app Y ≫ (unpointedFrameIso a Y K).hom =
      (unpointedFrameIso a Y L).hom ≫
        PointedFramingAction.cotensorMap (𝟙 ((CompatibleCotensorFraming.resolution a).obj Y)) k := by
  rw [unpointedFrameIso_hom, unpointedFrameIso_hom]
  have hs := cotensorFrameHomEquiv_source a ((a.cotensor.map k.op).app Y) K Y (𝟙 _)
  have hp := cotensorFrameHomEquiv_parameter a ((a.cotensor.obj (op L)).obj Y) k Y (𝟙 _)
  rw [Category.comp_id] at hs
  rw [Category.id_comp] at hp
  exact hs.symm.trans hp

/-- The full cotensor carrier comparison retains every original coefficient morphism. -/
theorem unpointedFrameIso_target {Y Y' : C} (p : Y ⟶ Y') (K : SSet.{vC}) :
    (a.cotensor.obj (op K)).map p ≫ (unpointedFrameIso a Y' K).hom =
      (unpointedFrameIso a Y K).hom ≫
        PointedFramingAction.cotensorMap ((CompatibleCotensorFraming.resolution a).map p) (𝟙 K) := by
  rw [unpointedFrameIso_hom, unpointedFrameIso_hom]
  have hs := cotensorFrameHomEquiv_source a ((a.cotensor.obj (op K)).map p) K Y' (𝟙 _)
  have hp := cotensorFrameHomEquiv_target a ((a.cotensor.obj (op K)).obj Y) K p (𝟙 _)
  rw [Category.comp_id] at hs
  rw [Category.id_comp] at hp
  exact hs.symm.trans hp

end UnpointedCotensorComparison

section PointedCotensorComparison

variable [HasLimitsOfSize.{0, vC} C]

/-- The full pointed action cotensor is the same original zero fiber of the full simplex cotensor. -/
def pointedFrameIso (Y : C) (K : PointedSSet.{vC}) :
    cotensorObj a Y K ≅
      PointedFramingAction.pointedCotensor ((CompatibleCotensorFraming.resolution a).obj Y) K := by
  let B := (CompatibleCotensorFraming.resolution a).obj Y
  let m := pullback.map ((a.cotensor.map K.hom.op).app Y)
    (0 : (0 : C) ⟶ (a.cotensor.obj (op (Δ[0] : SSet.{vC}))).obj Y)
    (PointedFramingAction.cotensorMap (𝟙 B) K.hom)
    (0 : (0 : C) ⟶ PointedFramingAction.cotensor B (Δ[0] : SSet.{vC}))
    (unpointedFrameIso a Y K.right).hom (𝟙 (0 : C))
    (unpointedFrameIso a Y (Δ[0] : SSet.{vC})).hom
    (unpointedFrameIso_parameter a Y K.hom) (by simp)
  let : IsIso m := by dsimp only [m]; infer_instance
  exact asIso m

/-- The full pointed comparison retains the original actual cotensor projection and weighted Hom comparison. -/
@[reassoc]
theorem pointedFrameIso_projection (Y : C) (K : PointedSSet.{vC}) :
    (pointedFrameIso a Y K).hom ≫
        PointedFramingAction.pointedCotensorProjection ((CompatibleCotensorFraming.resolution a).obj Y) K =
      cotensorProjection a Y K ≫ (unpointedFrameIso a Y K.right).hom := pullback.lift_fst _ _ _

/-- The inverse pointed comparison retains both entire inverse cotensor projection maps. -/
@[reassoc]
theorem pointedFrameIso_inv_projection (Y : C) (K : PointedSSet.{vC}) :
    (pointedFrameIso a Y K).inv ≫ cotensorProjection a Y K =
      PointedFramingAction.pointedCotensorProjection ((CompatibleCotensorFraming.resolution a).obj Y) K ≫
        (unpointedFrameIso a Y K.right).inv := by
  apply (cancel_epi (pointedFrameIso a Y K).hom).mp
  rw [← Category.assoc (pointedFrameIso a Y K).hom (pointedFrameIso a Y K).inv,
    Iso.hom_inv_id, Category.id_comp,
    ← Category.assoc (pointedFrameIso a Y K).hom,
    pointedFrameIso_projection, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The actual pointed action cotensor comparison retains every original coefficient map. -/
theorem pointedFrameIso_target {Y Y' : C} (p : Y ⟶ Y') (K : PointedSSet.{vC}) :
    cotensorMap a p K ≫ (pointedFrameIso a Y' K).hom =
      (pointedFrameIso a Y K).hom ≫
        PointedFramingAction.pointedCotensorMap ((CompatibleCotensorFraming.resolution a).map p) (𝟙 K) := by
  apply pullback.hom_ext
  · change (cotensorMap a p K ≫ (pointedFrameIso a Y' K).hom) ≫
        PointedFramingAction.pointedCotensorProjection ((CompatibleCotensorFraming.resolution a).obj Y') K =
      ((pointedFrameIso a Y K).hom ≫
        PointedFramingAction.pointedCotensorMap ((CompatibleCotensorFraming.resolution a).map p) (𝟙 K)) ≫
        PointedFramingAction.pointedCotensorProjection ((CompatibleCotensorFraming.resolution a).obj Y') K
    rw [Category.assoc, pointedFrameIso_projection,
      ← Category.assoc (cotensorMap a p K), cotensorMap_projection, Category.assoc,
      Category.assoc (pointedFrameIso a Y K).hom, PointedFramingAction.pointedCotensorMap_projection,
      ← Category.assoc (pointedFrameIso a Y K).hom, pointedFrameIso_projection, Category.assoc,
      unpointedFrameIso_target]
    simp only [Under.id_right]
  · exact HasZeroObject.zeroIsTerminal.hom_ext _ _

/-- The whole full-simplex pointed cotensor functor on the original action frames. -/
abbrev frameCotensorFunctor (K : PointedSSet.{vC}) : C ⥤ C :=
  CompatibleCotensorFraming.resolution a ⋙ (PointedFramingAction.pointedCotensorBifunctor.obj (op K))

/-- Both complete pointed cotensor functors and all original arrows are naturally isomorphic. -/
def pointedFrameFunctorIso (K : PointedSSet.{vC}) : cotensorFunctor a K ≅ frameCotensorFunctor a K :=
  NatIso.ofComponents (fun Y => pointedFrameIso a Y K) (fun p => pointedFrameIso_target a p K)

/-- The full inverse pointed cotensor comparison retains every original coefficient arrow. -/
theorem pointedFrameIso_target_inv {Y Y' : C} (p : Y ⟶ Y') (K : PointedSSet.{vC}) :
    PointedFramingAction.pointedCotensorMap ((CompatibleCotensorFraming.resolution a).map p) (𝟙 K) ≫
        (pointedFrameIso a Y' K).inv = (pointedFrameIso a Y K).inv ≫ cotensorMap a p K :=
  (pointedFrameFunctorIso a K).inv.naturality p

end PointedCotensorComparison

section CotensorHomotopyComparison

open PointedFramingAction

/-- The actual pointed action cotensor is fibrant at every original fibrant target. -/
theorem cotensorObj_isFibrant (Y : C) [IsFibrant Y] (K : PointedSSet.{vC}) :
    IsFibrant (cotensorObj a Y K) := by
  let : IsCofibrant K := pointedSSet_isCofibrant K
  let : (adjunction a K).IsQuillenAdjunction := adjunction_isQuillen a K
  exact Adjunction.IsQuillenAdjunction.preservesFibrantObjects (adj := adjunction a K) inferInstance

variable [HasLimitsOfSize.{0, vC} C]

/-- The actual compatible cotensor frame has the full scalar Quillen adjunction. -/
theorem frameCotensor_isQuillen (Y : C) [IsFibrant Y] :
    (pointedCotensorHomAdjunction ((CompatibleCotensorFraming.resolution a).obj Y)).IsQuillenAdjunction :=
  pointedCotensorHomAdjunction_isQuillen _
    (fun j => CompatibleCotensorFraming.matchingMap_fibration a Y j.unop)
    (fun f => (weakEquivalence_iff _).mp (CompatibleCotensorFraming.resolution_map_weak a Y f))

/-- The actual pointed action cotensor retains the full original scalar ordinary-Ho Hom functions. -/
def cotensorHoHomEquiv (X : C) [IsCofibrant X] (K : PointedSSet.{vC}) (Y : C) [IsFibrant Y] :
    ((weakEquivalences C).Q.obj X ⟶ (weakEquivalences C).Q.obj (cotensorObj a Y K)) ≃
      (pointedProjection.obj K ⟶
        pointedProjection.obj (pointedRightHom X ((CompatibleCotensorFraming.resolution a).obj Y))) := by
  let B := (CompatibleCotensorFraming.resolution a).obj Y
  let adj := pointedCotensorHomAdjunction B
  let : adj.IsQuillenAdjunction := frameCotensor_isQuillen a Y
  let : IsCofibrant K := pointedSSet_isCofibrant K
  let : IsFibrant (op X) := by
    apply (isFibrant_iff_of_isTerminal (initial.to X).op initialIsInitial.op).mpr
    rw [fibration_op_iff]
    infer_instance
  let : ((weakEquivalences C).Q.op).IsLocalization (weakEquivalences Cᵒᵖ) := by
    rw [weakEquivalences_op]
    infer_instance
  exact (Iso.homCongr (Iso.refl _) ((weakEquivalences C).Q.mapIso (pointedFrameIso a Y K))).trans
    (Quiver.Hom.opEquiv.trans (LocalQuillenHom.homEquiv adj pointedProjection (weakEquivalences C).Q.op K (op X)))

/-- Every represented action-cotensor arrow retains its actual pointed simplex transpose. -/
theorem cotensorHoHomEquiv_map (X : C) [IsCofibrant X] (K : PointedSSet.{vC}) (Y : C) [IsFibrant Y]
    (f : X ⟶ cotensorObj a Y K) :
    cotensorHoHomEquiv a X K Y ((weakEquivalences C).Q.map f) =
      pointedProjection.map (pointedCotensorHomEquiv X K ((CompatibleCotensorFraming.resolution a).obj Y)
        (f ≫ (pointedFrameIso a Y K).hom)) := by
  let : (pointedCotensorHomAdjunction ((CompatibleCotensorFraming.resolution a).obj Y)).IsQuillenAdjunction :=
    frameCotensor_isQuillen a Y
  let : IsCofibrant K := pointedSSet_isCofibrant K
  let : IsFibrant (op X) := by
    apply (isFibrant_iff_of_isTerminal (initial.to X).op initialIsInitial.op).mpr
    rw [fibration_op_iff]
    infer_instance
  let : ((weakEquivalences C).Q.op).IsLocalization (weakEquivalences Cᵒᵖ) := by
    rw [weakEquivalences_op]
    infer_instance
  change LocalQuillenHom.homEquiv
    (pointedCotensorHomAdjunction ((CompatibleCotensorFraming.resolution a).obj Y))
    pointedProjection (weakEquivalences C).Q.op K (op X)
    (((weakEquivalences C).Q.map f ≫ (weakEquivalences C).Q.map (pointedFrameIso a Y K).hom).op) = _
  rw [← Functor.map_comp]
  exact (LocalQuillenHom.homEquiv_map
    (pointedCotensorHomAdjunction ((CompatibleCotensorFraming.resolution a).obj Y))
    pointedProjection (weakEquivalences C).Q.op K (op X) (f ≫ (pointedFrameIso a Y K).hom).op).trans
      (congrArg pointedProjection.map (pointedCotensorHomAdjunction_homEquiv _ _ _ _))

/-- The compatible scalar Ho transpose retains every original cofibrant source arrow. -/
theorem cotensorHoHomEquiv_source {X X' : C} [IsCofibrant X] [IsCofibrant X']
    (i : X ⟶ X') (K : PointedSSet.{vC}) (Y : C) [IsFibrant Y]
    (h : (weakEquivalences C).Q.obj X' ⟶ (weakEquivalences C).Q.obj (cotensorObj a Y K)) :
    cotensorHoHomEquiv a X K Y ((weakEquivalences C).Q.map i ≫ h) =
      cotensorHoHomEquiv a X' K Y h ≫ pointedProjection.map
        (pointedHomPrecomp ((CosimplicialObject.const C).map i) ((CompatibleCotensorFraming.resolution a).obj Y)) := by
  let : IsFibrant (cotensorObj a Y K) := cotensorObj_isFibrant a Y K
  obtain ⟨f, rfl⟩ := map_surjective_of_isLocalization (weakEquivalences C).Q X' (cotensorObj a Y K) h
  rw [← Functor.map_comp, cotensorHoHomEquiv_map, cotensorHoHomEquiv_map,
    Category.assoc, pointedCotensorHomEquiv_source, Functor.map_comp]

/-- The compatible scalar Ho transpose retains every original map between fibrant action targets. -/
theorem cotensorHoHomEquiv_target (X : C) [IsCofibrant X] (K : PointedSSet.{vC})
    {Y Y' : C} [IsFibrant Y] [IsFibrant Y'] (p : Y ⟶ Y')
    (h : (weakEquivalences C).Q.obj X ⟶ (weakEquivalences C).Q.obj (cotensorObj a Y K)) :
    cotensorHoHomEquiv a X K Y' (h ≫ (weakEquivalences C).Q.map (cotensorMap a p K)) =
      cotensorHoHomEquiv a X K Y h ≫ pointedProjection.map
        (pointedHomPostcomp ((CosimplicialObject.const C).obj X) ((CompatibleCotensorFraming.resolution a).map p)) := by
  let : IsFibrant (cotensorObj a Y K) := cotensorObj_isFibrant a Y K
  obtain ⟨f, rfl⟩ := map_surjective_of_isLocalization (weakEquivalences C).Q X (cotensorObj a Y K) h
  rw [← Functor.map_comp, cotensorHoHomEquiv_map, cotensorHoHomEquiv_map,
    Category.assoc, pointedFrameIso_target, ← Category.assoc,
    pointedCotensorHomEquiv_target, Functor.map_comp]

/-- The inverse compatible scalar Ho transpose retains every original source arrow. -/
theorem cotensorHoHomEquiv_symm_source {X X' : C} [IsCofibrant X] [IsCofibrant X']
    (i : X ⟶ X') (K : PointedSSet.{vC}) (Y : C) [IsFibrant Y]
    (h : pointedProjection.obj K ⟶
      pointedProjection.obj (pointedRightHom X' ((CompatibleCotensorFraming.resolution a).obj Y))) :
    (cotensorHoHomEquiv a X K Y).symm (h ≫ pointedProjection.map
        (pointedHomPrecomp ((CosimplicialObject.const C).map i) ((CompatibleCotensorFraming.resolution a).obj Y))) =
      (weakEquivalences C).Q.map i ≫ (cotensorHoHomEquiv a X' K Y).symm h := by
  apply (cotensorHoHomEquiv a X K Y).injective
  rw [Equiv.apply_symm_apply, cotensorHoHomEquiv_source, Equiv.apply_symm_apply]

/-- The inverse compatible scalar Ho transpose retains every original fibrant target arrow. -/
theorem cotensorHoHomEquiv_symm_target (X : C) [IsCofibrant X] (K : PointedSSet.{vC})
    {Y Y' : C} [IsFibrant Y] [IsFibrant Y'] (p : Y ⟶ Y')
    (h : pointedProjection.obj K ⟶
      pointedProjection.obj (pointedRightHom X ((CompatibleCotensorFraming.resolution a).obj Y))) :
    (cotensorHoHomEquiv a X K Y').symm (h ≫ pointedProjection.map
        (pointedHomPostcomp ((CosimplicialObject.const C).obj X) ((CompatibleCotensorFraming.resolution a).map p))) =
      (cotensorHoHomEquiv a X K Y).symm h ≫ (weakEquivalences C).Q.map (cotensorMap a p K) := by
  apply (cotensorHoHomEquiv a X K Y').injective
  rw [Equiv.apply_symm_apply, cotensorHoHomEquiv_target, Equiv.apply_symm_apply]

end CotensorHomotopyComparison

section OrdinaryLoopComparison

open PointedFramingAction
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable [HasLimitsOfSize.{0, vC} C] [HasColimitsOfSize.{0, vC} C]
  (d : GeneratedFunctorialReplacements.Data (C := C))

/-- The genuine original weak frame span compares ordinary loops with the same total-derived actual circle cotensor. -/
def loopHomEquiv (X Y : C) :
    ((weakEquivalences C).Q.obj X ⟶ (loops d).obj ((weakEquivalences C).Q.obj Y)) ≃
      ((weakEquivalences C).Q.obj X ⟶ (derivedLoops a d).obj ((weakEquivalences C).Q.obj Y)) := by
  let : IsCofibrant (d.Q.obj X) := d.q_cofibrant X
  let : IsFibrant (d.R.obj Y) := d.r_fibrant Y
  exact (Iso.homCongr (qHomotopyIso d X).symm (Iso.refl _)).trans
    ((pointedCotensorHoHomEquiv d X circle Y).trans
      ((Iso.homCongr (Iso.refl (pointedProjection.obj circle)) (rightActionIso a d X Y)).trans
        ((cotensorHoHomEquiv a (d.Q.obj X) circle (d.R.obj Y)).symm.trans
          (Iso.homCongr (qHomotopyIso d X) (Iso.refl _)))))

/-- The entire comparison retains the original q isomorphism, both actual frame spans, and the complete weighted
transpose. -/
theorem loopHomEquiv_apply (X Y : C)
    (f : (weakEquivalences C).Q.obj X ⟶ (loops d).obj ((weakEquivalences C).Q.obj Y)) :
    loopHomEquiv a d X Y f =
      let : IsCofibrant (d.Q.obj X) := d.q_cofibrant X
      let : IsFibrant (d.R.obj Y) := d.r_fibrant Y
      (qHomotopyIso d X).inv ≫ (cotensorHoHomEquiv a (d.Q.obj X) circle (d.R.obj Y)).symm
        (pointedCotensorHoHomEquiv d X circle Y ((qHomotopyIso d X).hom ≫ f) ≫
          (rightActionIso a d X Y).hom) := by
  change (weakEquivalences C).Q.obj X ⟶
    (weakEquivalences C).Q.obj (pointedCotensor ((rightFrame d).obj Y) circle) at f
  dsimp only [loopHomEquiv]
  simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv,
    Iso.refl_hom, Iso.refl_inv, Category.comp_id, Category.id_comp]
  rfl

/-- The full original loop comparison is natural under every original coefficient source arrow. -/
theorem loopHomEquiv_source {X X' : C} (i : X ⟶ X') (Y : C)
    (h : (weakEquivalences C).Q.obj X' ⟶ (loops d).obj ((weakEquivalences C).Q.obj Y)) :
    loopHomEquiv a d X Y ((weakEquivalences C).Q.map i ≫ h) =
      (weakEquivalences C).Q.map i ≫ loopHomEquiv a d X' Y h := by
  let : IsCofibrant (d.Q.obj X) := d.q_cofibrant X
  let : IsCofibrant (d.Q.obj X') := d.q_cofibrant X'
  let : IsFibrant (d.R.obj Y) := d.r_fibrant Y
  change (weakEquivalences C).Q.obj X' ⟶
    (weakEquivalences C).Q.obj (pointedCotensor ((rightFrame d).obj Y) circle) at h
  have hq : (qHomotopyIso d X).hom ≫ (weakEquivalences C).Q.map i =
      (weakEquivalences C).Q.map (d.Q.map i) ≫ (qHomotopyIso d X').hom :=
    ((weakEquivalences C).Q.map_comp _ _).symm.trans
      ((congrArg (weakEquivalences C).Q.map (d.q.naturality i).symm).trans
        ((weakEquivalences C).Q.map_comp _ _))
  rw [loopHomEquiv_apply, loopHomEquiv_apply]
  dsimp only
  rw [← Category.assoc (qHomotopyIso d X).hom, hq, Category.assoc,
    pointedCotensorHoHomEquiv_source, Category.assoc, rightActionIso_source,
    ← Category.assoc, actionRightSourceMap]
  dsimp only [actionFrame, Functor.comp_obj]
  have hs := cotensorHoHomEquiv_symm_source a (d.Q.map i) circle (d.R.obj Y)
    (pointedCotensorHoHomEquiv d X' circle Y ((qHomotopyIso d X').hom ≫ h) ≫
      (rightActionIso a d X' Y).hom)
  rw [hs, ← Category.assoc, qHomotopyIso_inv_naturality, Category.assoc]

/-- The full original loop comparison is natural under every original coefficient target arrow. -/
theorem loopHomEquiv_target (X : C) {Y Y' : C} (p : Y ⟶ Y')
    (h : (weakEquivalences C).Q.obj X ⟶ (loops d).obj ((weakEquivalences C).Q.obj Y)) :
    loopHomEquiv a d X Y' (h ≫ (loops d).map ((weakEquivalences C).Q.map p)) =
      loopHomEquiv a d X Y h ≫ (derivedLoops a d).map ((weakEquivalences C).Q.map p) := by
  let : IsCofibrant (d.Q.obj X) := d.q_cofibrant X
  let : IsFibrant (d.R.obj Y) := d.r_fibrant Y
  let : IsFibrant (d.R.obj Y') := d.r_fibrant Y'
  change (weakEquivalences C).Q.obj X ⟶
    (weakEquivalences C).Q.obj (pointedCotensor ((rightFrame d).obj Y) circle) at h
  rw [loopHomEquiv_apply, loopHomEquiv_apply, loops_map, derivedLoops_map]
  dsimp only
  have hOrd := pointedCotensorHoHomEquiv_target d X circle p ((qHomotopyIso d X).hom ≫ h)
  have hSpace := rightActionIso_target a d X p
  rw [← Category.assoc (qHomotopyIso d X).hom, hOrd,
    Category.assoc, hSpace, ← Category.assoc,
    actionRightTargetMap]
  dsimp only [actionFrame, Functor.comp_map]
  have ht := cotensorHoHomEquiv_symm_target a (d.Q.obj X) circle (d.R.map p)
    (pointedCotensorHoHomEquiv d X circle Y ((qHomotopyIso d X).hom ≫ h) ≫
      (rightActionIso a d X Y).hom)
  rw [ht, Category.assoc]

/-- The complete comparison acts on every original Ho source object and every Ho arrow. -/
def loopHomEquivHo (X : (weakEquivalences C).Localization) (Y : C) :
    (X ⟶ (loops d).obj ((weakEquivalences C).Q.obj Y)) ≃
      (X ⟶ (derivedLoops a d).obj ((weakEquivalences C).Q.obj Y)) := by
  rcases X with ⟨⟨X⟩⟩
  exact loopHomEquiv a d X Y

theorem loopHomEquivHo_original (X Y : C) :
    loopHomEquivHo a d ((weakEquivalences C).Q.obj X) Y = loopHomEquiv a d X Y := rfl

/-- The actual loop Hom comparison is natural on all ordinary-Ho source arrows, including formal inverses. -/
theorem loopHomEquivHo_source {X X' : (weakEquivalences C).Localization} (i : X ⟶ X') (Y : C)
    (h : X' ⟶ (loops d).obj ((weakEquivalences C).Q.obj Y)) :
    loopHomEquivHo a d X Y (i ≫ h) = i ≫ loopHomEquivHo a d X' Y h := by
  let γ := (weakEquivalences C).Q
  let F₁ := yoneda.obj ((loops d).obj (γ.obj Y))
  let F₂ := yoneda.obj ((derivedLoops a d).obj (γ.obj Y))
  let τ₀ : γ.op ⋙ F₁ ⟶ γ.op ⋙ F₂ :=
    { app X := ↾(loopHomEquivHo a d (γ.obj X.unop) Y)
      naturality {X X'} f := by
        ext g
        change loopHomEquiv a d X'.unop Y (γ.map f.unop ≫ g) =
          γ.map f.unop ≫ loopHomEquiv a d X.unop Y g
        exact loopHomEquiv_source a d f.unop Y g }
  let τ : F₁ ⟶ F₂ := Localization.liftNatTrans γ.op (weakEquivalences C).op
    (γ.op ⋙ F₁) (γ.op ⋙ F₂) F₁ F₂ τ₀
  have hτ (Z : C) : τ.app (op (γ.obj Z)) = ↾(loopHomEquivHo a d (γ.obj Z) Y) := by
    change (Localization.liftNatTrans γ.op (weakEquivalences C).op
      (γ.op ⋙ F₁) (γ.op ⋙ F₂) F₁ F₂ τ₀).app (γ.op.obj (op Z)) = _
    rw [Localization.liftNatTrans_app]
    rfl
  rcases X with ⟨⟨X⟩⟩
  rcases X' with ⟨⟨X'⟩⟩
  have hn := τ.naturality_apply i.op h
  change (τ.app (op (γ.obj X))) (i ≫ h) = i ≫ (τ.app (op (γ.obj X'))) h at hn
  rw [hτ X, hτ X'] at hn
  exact hn

/-- Yoneda constructs the actual object comparison from the genuine full original frame Hom maps. -/
def loopObjectIso (Y : C) :
    (loops d).obj ((weakEquivalences C).Q.obj Y) ≅
      (derivedLoops a d).obj ((weakEquivalences C).Q.obj Y) :=
  Yoneda.ext _ _
    (fun {X} h => loopHomEquivHo a d X Y h)
    (fun {X} h => (loopHomEquivHo a d X Y).symm h)
    (fun h => (loopHomEquivHo a d _ Y).symm_apply_apply h)
    (fun h => (loopHomEquivHo a d _ Y).apply_symm_apply h)
    (fun i h => loopHomEquivHo_source a d i Y h)

/-- The full forward object comparison is the original frame comparison evaluated on its entire identity. -/
theorem loopObjectIso_hom (Y : C) :
    (loopObjectIso a d Y).hom =
      loopHomEquivHo a d ((loops d).obj ((weakEquivalences C).Q.obj Y)) Y (𝟙 _) := rfl

/-- The full inverse object comparison is the same original inverse frame Hom comparison. -/
theorem loopObjectIso_inv (Y : C) :
    (loopObjectIso a d Y).inv =
      (loopHomEquivHo a d ((derivedLoops a d).obj ((weakEquivalences C).Q.obj Y)) Y).symm (𝟙 _) := rfl

/-- Every original Ho map recovers its entire genuine frame comparison through the actual object isomorphism. -/
theorem loopObjectIso_hom_comp (X : (weakEquivalences C).Localization) (Y : C)
    (h : X ⟶ (loops d).obj ((weakEquivalences C).Q.obj Y)) :
    h ≫ (loopObjectIso a d Y).hom = loopHomEquivHo a d X Y h := by
  rw [loopObjectIso_hom]
  have hn := loopHomEquivHo_source a d h Y (𝟙 _)
  rw [Category.comp_id] at hn
  exact hn.symm

/-- Every original Ho map also retains the complete inverse genuine frame comparison. -/
theorem loopObjectIso_inv_comp (X : (weakEquivalences C).Localization) (Y : C)
    (h : X ⟶ (derivedLoops a d).obj ((weakEquivalences C).Q.obj Y)) :
    h ≫ (loopObjectIso a d Y).inv = (loopHomEquivHo a d X Y).symm h := by
  obtain ⟨g, rfl⟩ := (loopHomEquivHo a d X Y).surjective h
  rw [← loopObjectIso_hom_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    loopObjectIso_hom_comp, Equiv.symm_apply_apply]

/-- The entire object comparison retains every original coefficient arrow. -/
theorem loopObjectIso_naturality {Y Y' : C} (p : Y ⟶ Y') :
    (loops d).map ((weakEquivalences C).Q.map p) ≫ (loopObjectIso a d Y').hom =
      (loopObjectIso a d Y).hom ≫ (derivedLoops a d).map ((weakEquivalences C).Q.map p) := by
  let U := pointedCotensor ((rightFrame d).obj Y) circle
  have hn := loopHomEquiv_target a d U p (𝟙 ((weakEquivalences C).Q.obj U))
  change loopHomEquivHo a d ((loops d).obj ((weakEquivalences C).Q.obj Y)) Y'
      (𝟙 _ ≫ (loops d).map ((weakEquivalences C).Q.map p)) =
    loopHomEquivHo a d ((loops d).obj ((weakEquivalences C).Q.obj Y)) Y (𝟙 _) ≫
      (derivedLoops a d).map ((weakEquivalences C).Q.map p) at hn
  rw [Category.id_comp, ← loopObjectIso_hom_comp, ← loopObjectIso_hom_comp,
    Category.id_comp] at hn
  exact hn

/-- The complete original loop comparison object on every ordinary homotopy-category object. -/
def loopComparisonObject (Y : (weakEquivalences C).Localization) :
    (loops d).obj Y ≅ (derivedLoops a d).obj Y := by
  rcases Y with ⟨⟨Y⟩⟩
  exact loopObjectIso a d Y

/-- The original ordinary loop functor is naturally the total-derived actual-circle cotensor on all Ho arrows. -/
def loopsComparison : loops d ≅ derivedLoops a d := by
  let γ := (weakEquivalences C).Q
  let : Localization.Lifting γ (weakEquivalences C) (γ ⋙ loops d) (loops d) := ⟨Iso.refl _⟩
  let : Localization.Lifting γ (weakEquivalences C) (γ ⋙ derivedLoops a d) (derivedLoops a d) :=
    ⟨Iso.refl _⟩
  let τ₀ : γ ⋙ loops d ⟶ γ ⋙ derivedLoops a d :=
    { app Y := (loopObjectIso a d Y).hom
      naturality {_ _} p := loopObjectIso_naturality a d p }
  let τ : loops d ⟶ derivedLoops a d := Localization.liftNatTrans γ (weakEquivalences C)
    (γ ⋙ loops d) (γ ⋙ derivedLoops a d) (loops d) (derivedLoops a d) τ₀
  have hτ (Y : C) : τ.app (γ.obj Y) = (loopObjectIso a d Y).hom := by
    rw [Localization.liftNatTrans_app]
    change 𝟙 _ ≫ (loopObjectIso a d Y).hom ≫ 𝟙 _ = _
    rw [Category.id_comp, Category.comp_id]
  refine NatIso.ofComponents (loopComparisonObject a d) ?_
  intro Y Y' p
  rcases Y with ⟨⟨Y⟩⟩
  rcases Y' with ⟨⟨Y'⟩⟩
  change (loops d).map p ≫ (loopObjectIso a d Y').hom =
    (loopObjectIso a d Y).hom ≫ (derivedLoops a d).map p
  have hn := τ.naturality p
  change (loops d).map p ≫ τ.app (γ.obj Y') = τ.app (γ.obj Y) ≫ (derivedLoops a d).map p at hn
  rw [hτ Y, hτ Y'] at hn
  exact hn

/-- Every original represented object retains the entire same forward loop comparison. -/
theorem loopsComparison_hom_app (Y : C) :
    (loopsComparison a d).hom.app ((weakEquivalences C).Q.obj Y) = (loopObjectIso a d Y).hom := rfl

/-- Every original represented object retains the entire same inverse loop comparison. -/
theorem loopsComparison_inv_app (Y : C) :
    (loopsComparison a d).inv.app ((weakEquivalences C).Q.obj Y) = (loopObjectIso a d Y).inv := rfl

/-- The full loop natural isomorphism recovers the original complete frame Hom function. -/
theorem loopsComparison_hom_comp (X Y : C)
    (h : (weakEquivalences C).Q.obj X ⟶ (loops d).obj ((weakEquivalences C).Q.obj Y)) :
    h ≫ (loopsComparison a d).hom.app ((weakEquivalences C).Q.obj Y) = loopHomEquiv a d X Y h := by
  rw [loopsComparison_hom_app]
  exact loopObjectIso_hom_comp a d _ Y h

/-- The actual derived circle adjunction is transported through the genuine original loop comparison. -/
def ordinaryRightAdjunction : derivedSuspension a d ⊣ loops d :=
  (derivedAdjunction a d).ofNatIsoRight (loopsComparison a d).symm

/-- The suspension comparison is the actual adjunction mate of the genuine original framing loop comparison. -/
def suspensionComparison : suspension d ≅ derivedSuspension a d :=
  (DerivedSuspensionLoopAdjunction.adjunction d).leftAdjointUniq (ordinaryRightAdjunction a d)

/-- The entire ordinary Hom function compares to the same actual total-derived circle Hom function. -/
theorem comparison_homEquiv (X Y : (weakEquivalences C).Localization)
    (f : (derivedSuspension a d).obj X ⟶ Y) :
    (DerivedSuspensionLoopAdjunction.adjunction d).homEquiv X Y
        ((suspensionComparison a d).hom.app X ≫ f) ≫ (loopsComparison a d).hom.app Y =
      (derivedAdjunction a d).homEquiv X Y f := by
  have hn : (DerivedSuspensionLoopAdjunction.adjunction d).homEquiv X Y
        ((suspensionComparison a d).hom.app X ≫ f) =
      (ordinaryRightAdjunction a d).homEquiv X Y f := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
    exact congrArg (fun b => b ≫ (loops d).map f)
      (Adjunction.unit_leftAdjointUniq_hom_app
        (DerivedSuspensionLoopAdjunction.adjunction d) (ordinaryRightAdjunction a d) X)
  rw [hn]
  rw [ordinaryRightAdjunction, Adjunction.homEquiv_ofNatIsoRight_apply, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- The complete inverse ordinary Hom function retains both actual inverse comparison maps. -/
theorem comparison_homEquiv_symm (X Y : (weakEquivalences C).Localization)
    (g : X ⟶ (derivedLoops a d).obj Y) :
    (suspensionComparison a d).inv.app X ≫
        ((DerivedSuspensionLoopAdjunction.adjunction d).homEquiv X Y).symm
          (g ≫ (loopsComparison a d).inv.app Y) =
      ((derivedAdjunction a d).homEquiv X Y).symm g := by
  apply ((derivedAdjunction a d).homEquiv X Y).injective
  rw [← comparison_homEquiv, ← Category.assoc,
    Iso.hom_inv_id_app, Category.id_comp, Equiv.apply_symm_apply,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id, Equiv.apply_symm_apply]

/-- Every full original ordinary unit is the same actual total-derived unit under the complete comparisons. -/
theorem comparison_unit (X : (weakEquivalences C).Localization) :
    (DerivedSuspensionLoopAdjunction.unit d).app X ≫
        (loops d).map ((suspensionComparison a d).hom.app X) ≫
        (loopsComparison a d).hom.app ((derivedSuspension a d).obj X) =
      (derivedAdjunction a d).unit.app X := by
  have hn := congrArg (fun b => b ≫ (loopsComparison a d).hom.app ((derivedSuspension a d).obj X))
    (Adjunction.unit_leftAdjointUniq_hom_app
      (DerivedSuspensionLoopAdjunction.adjunction d) (ordinaryRightAdjunction a d) X)
  change ((DerivedSuspensionLoopAdjunction.unit d).app X ≫
      (loops d).map ((suspensionComparison a d).hom.app X)) ≫
        (loopsComparison a d).hom.app ((derivedSuspension a d).obj X) =
    ((derivedAdjunction a d).unit.app X ≫
      (loopsComparison a d).inv.app ((derivedSuspension a d).obj X)) ≫
        (loopsComparison a d).hom.app ((derivedSuspension a d).obj X) at hn
  rw [Category.assoc ((derivedAdjunction a d).unit.app X), Iso.inv_hom_id_app] at hn
  exact (Category.assoc _ _ _).symm.trans (hn.trans (Category.comp_id _))

/-- Every full original ordinary counit is the same actual total-derived counit under the complete comparisons. -/
theorem comparison_counit (Y : (weakEquivalences C).Localization) :
    (suspension d).map ((loopsComparison a d).hom.app Y) ≫
        (suspensionComparison a d).hom.app ((derivedLoops a d).obj Y) ≫
        (derivedAdjunction a d).counit.app Y = (DerivedSuspensionLoopAdjunction.counit d).app Y := by
  have hn := Adjunction.leftAdjointUniq_hom_app_counit
    (DerivedSuspensionLoopAdjunction.adjunction d) (ordinaryRightAdjunction a d) Y
  rw [← Category.assoc, (suspensionComparison a d).hom.naturality]
  change ((suspensionComparison a d).hom.app ((loops d).obj Y) ≫
      (derivedSuspension a d).map ((loopsComparison a d).hom.app Y)) ≫
        (derivedAdjunction a d).counit.app Y = _
  exact (Category.assoc _ _ _).trans hn

omit [HasLimitsOfSize.{0, vC} C] [HasColimitsOfSize.{0, vC} C] in
/-- The entire original total-derived circle suspension has its full first triangle on every Ho object. -/
theorem derivedSuspension_triangle (X : (weakEquivalences C).Localization) :
    (derivedSuspension a d).map ((derivedAdjunction a d).unit.app X) ≫
      (derivedAdjunction a d).counit.app ((derivedSuspension a d).obj X) = 𝟙 _ :=
  (derivedAdjunction a d).left_triangle_components X

omit [HasLimitsOfSize.{0, vC} C] [HasColimitsOfSize.{0, vC} C] in
/-- The entire original total-derived circle cotensor has its full second triangle on every Ho object. -/
theorem derivedLoops_triangle (Y : (weakEquivalences C).Localization) :
    (derivedAdjunction a d).unit.app ((derivedLoops a d).obj Y) ≫
      (derivedLoops a d).map ((derivedAdjunction a d).counit.app Y) = 𝟙 _ :=
  (derivedAdjunction a d).right_triangle_components Y

/-- The compatible comparison retains both full original good-cylinder cofiber maps on the same original QX. -/
def originalCylinderComparison (X : C) :
    (weakEquivalences C).Q.obj (originalCylinderCofiber d X) ≅
      (derivedSuspension a d).obj ((weakEquivalences C).Q.obj X) :=
  (suspensionCylinderIso d X).symm ≪≫ (suspensionComparison a d).app ((weakEquivalences C).Q.obj X)

/-- The compatible comparison retains both full original good-path fiber maps on the same original RY. -/
def originalPathComparison (Y : C) :
    (weakEquivalences C).Q.obj (originalPathFiber d Y) ≅
      (derivedLoops a d).obj ((weakEquivalences C).Q.obj Y) :=
  (loopsPathIso d Y).symm ≪≫ (loopsComparison a d).app ((weakEquivalences C).Q.obj Y)

theorem originalCylinderComparison_hom (X : C) :
    (originalCylinderComparison a d X).hom = (suspensionCylinderIso d X).inv ≫
      (suspensionComparison a d).hom.app ((weakEquivalences C).Q.obj X) := rfl

theorem originalPathComparison_hom (Y : C) :
    (originalPathComparison a d Y).hom = (loopsPathIso d Y).inv ≫
      (loopsComparison a d).hom.app ((weakEquivalences C).Q.obj Y) := rfl

end OrdinaryLoopComparison

end HomotopicalAlgebra.DerivedSuspensionLoopAdjunction.Compatible

namespace HomotopicalAlgebra.DerivedSuspensionLoopAdjunction.Topological

set_option backward.defeqAttrib.useBackward true
universe uT
open Opposite MonoidalCategory
open scoped CGWH.modelCategory MonoidalCategory ZeroObject
open PointedCGWH.SingularHomotopyGeometry
open PointedFramingAction (PointedSSet)

/-- The actual unpointed simplicial realization, with its original disjoint native basepoint. -/
abbrev freeRealization : SSet.{vC} ⥤ PointedCGWH.{uT, vC} :=
  SSet.toCGWH.{uT, vC} ⋙ Under.costar CGWH.point.{uT, vC}

/-- The full original geometric realization and free-basepoint adjunctions compose to the actual singular adjunction. -/
def freeRealizationAdjunction : freeRealization.{vC, uT} ⊣ singularFunctor.{uT, vC} :=
  SSet.sSetCGWHAdj.comp (Under.costarAdjForget CGWH.point)

/-- The original native singular fibration classes prove this same actual realization adjunction Quillen. -/
theorem freeRealization_isQuillen : (freeRealizationAdjunction.{vC, uT}).IsQuillenAdjunction := by
  apply Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · exact PointedCGWH.SingularModel.preservesFibrations
  · exact PointedCGWH.SingularModel.preservesTrivialFibrations

/-- The actual pointed CGWH zero object supplies the scalar zero maps. -/
local instance pointedTopologicalZeroMorphisms7 : HasZeroMorphisms PointedCGWH.{uT, vC} :=
  HasZeroObject.zeroMorphismsOfZeroObject

/-- The actual pointed geometric realization collapses precisely the freely realized chosen simplicial basepoint. -/
abbrev realizedWeight (K : PointedSSet.{vC}) : PointedCGWH.{uT, vC} :=
  pushout (freeRealization.map K.hom)
    (0 : freeRealization.obj (Δ[0] : SSet.{vC}) ⟶ (0 : PointedCGWH.{uT, vC}))

/-- The entire original freely realized carrier maps to its actual based realization quotient. -/
def weightQuotient (K : PointedSSet.{vC}) : freeRealization.obj K.right ⟶ realizedWeight.{vC, uT} K :=
  pushout.inl _ _

/-- The original scalar zero leg into the genuine based geometric realization. -/
def weightZeroLeg (K : PointedSSet.{vC}) : (0 : PointedCGWH.{uT, vC}) ⟶ realizedWeight.{vC, uT} K :=
  pushout.inr _ _

@[reassoc]
theorem weight_basepoint (K : PointedSSet.{vC}) :
    freeRealization.map K.hom ≫ weightQuotient.{vC, uT} K = 0 :=
  pushout.condition.trans zero_comp

/-- Actual geometric Quillen preservation and the original basepoint cofibration prove genuine native cofibrancy. -/
theorem realizedWeight_isCofibrant (K : PointedSSet.{vC}) : IsCofibrant (realizedWeight.{vC, uT} K) := by
  let : Mono K.hom := ⟨fun _ _ _ => SSet.stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  let : freeRealizationAdjunction.IsQuillenAdjunction := freeRealization_isQuillen
  let : Cofibration (freeRealization.map K.hom) := (cofibration_iff _).mpr
    (Adjunction.IsQuillenAdjunction.preservesCofibrations (adj := freeRealizationAdjunction) K.hom
      ((cofibration_iff _).mp (SSet.modelCategoryQuillen.cofibration_of_mono K.hom)))
  let : Cofibration (weightZeroLeg.{vC, uT} K) := by dsimp only [weightZeroLeg]; infer_instance
  exact (isCofibrant_iff_of_isInitial (weightZeroLeg K) HasZeroObject.zeroIsInitial).mpr inferInstance


section PointedRealizationComparison

set_option backward.isDefEq.respectTransparency false

/-- The canonical free-basepoint counit into the direct pointed realization. -/
def pointedRealizationQuotient (K : PointedSSet.{vC}) :
    freeRealization.obj K.right ⟶ SSet.pointedToCGWH.{uT, vC}.obj K :=
  (Under.costarAdjForget CGWH.point).counit.app (SSet.pointedToCGWH.obj K)

private theorem costar_counit_unit (Y : PointedCGWH.{uT, vC}) :
    (Under.costarAdjForget CGWH.point).unit.app Y.right ≫
      ((Under.costarAdjForget CGWH.point).counit.app Y).right = 𝟙 Y.right :=
  (Under.costarAdjForget CGWH.point).right_triangle_components Y

private abbrev realizationPoint : PointedCGWH.{uT, vC} := Under.mk (𝟙 CGWH.point)

private def realizationCollapse (A : CGWH.{uT, vC}) :
    (Under.costar CGWH.point).obj A ⟶ realizationPoint.{vC, uT} :=
  Under.homMk (CGWH.point_isTerminal.from _) (CGWH.point_isTerminal.hom_ext _ _)

private def realizationPointLeg (Y : PointedCGWH.{uT, vC}) :
    realizationPoint.{vC, uT} ⟶ Y :=
  Under.homMk Y.hom (by simp)

private theorem costar_counit_isPushout (Y : PointedCGWH.{uT, vC})
    (A : CGWH.{uT, vC}) (e : A ≅ CGWH.point) :
    IsPushout ((Under.costar CGWH.point).map (e.hom ≫ Y.hom)) (realizationCollapse A)
      ((Under.costarAdjForget CGWH.point).counit.app Y) (realizationPointLeg Y) := by
  let adj := Under.costarAdjForget CGWH.point.{uT, vC}
  have hunit : adj.unit.app A ≫ (realizationCollapse A).right = e.hom :=
    CGWH.point_isTerminal.hom_ext _ _
  have hn := adj.unit.naturality (e.hom ≫ Y.hom)
  change (e.hom ≫ Y.hom) ≫ adj.unit.app Y.right =
    adj.unit.app A ≫ ((Under.costar CGWH.point).map (e.hom ≫ Y.hom)).right at hn
  apply IsPushout.mk'
  · apply (adj.homEquiv A Y).injective
    simp only [Adjunction.homEquiv_unit]
    change adj.unit.app A ≫ ((Under.costar CGWH.point).map (e.hom ≫ Y.hom)).right ≫
        (adj.counit.app Y).right =
      adj.unit.app A ≫ (realizationCollapse A).right ≫ (realizationPointLeg Y).right
    rw [← Category.assoc, ← hn, Category.assoc, costar_counit_unit,
      Category.comp_id, ← Category.assoc, hunit]
    rfl
  · intro T f g hq _
    apply Under.UnderMorphism.ext
    have h := congrArg (fun k => adj.unit.app Y.right ≫ k.right) hq
    change adj.unit.app Y.right ≫ (adj.counit.app Y).right ≫ f.right =
      adj.unit.app Y.right ≫ (adj.counit.app Y).right ≫ g.right at h
    have hf : (adj.unit.app Y.right ≫ (adj.counit.app Y).right) ≫ f.right = f.right :=
      (congrArg (fun k : Y.right ⟶ Y.right => k ≫ f.right) (costar_counit_unit Y)).trans
        (Category.id_comp f.right)
    have hg : (adj.unit.app Y.right ≫ (adj.counit.app Y).right) ≫ g.right = g.right :=
      (congrArg (fun k : Y.right ⟶ Y.right => k ≫ g.right) (costar_counit_unit Y)).trans
        (Category.id_comp g.right)
    exact hf.symm.trans ((Category.assoc _ _ _).trans
      (h.trans ((Category.assoc _ _ _).symm.trans hg)))
  · intro T a b hab
    let f : Y.right ⟶ T.right := adj.unit.app Y.right ≫ a.right
    have hb : b.right = T.hom := by simpa using Under.w b
    have h := congrArg (fun k => adj.unit.app A ≫ k.right) hab
    change adj.unit.app A ≫ ((Under.costar CGWH.point).map (e.hom ≫ Y.hom)).right ≫ a.right =
      adj.unit.app A ≫ (realizationCollapse A).right ≫ b.right at h
    rw [← Category.assoc, ← hn, Category.assoc, ← Category.assoc _ _ b.right,
      hunit, hb] at h
    have hp : Y.hom ≫ f = T.hom := by
      have h' := congrArg (fun k => e.inv ≫ k) h
      change e.inv ≫ e.hom ≫ Y.hom ≫ f = e.inv ≫ e.hom ≫ T.hom at h'
      simpa only [Iso.inv_hom_id_assoc] using h'
    let t : Y ⟶ T := Under.homMk f hp
    refine ⟨t, ?_, Under.mkIdInitial.hom_ext _ _⟩
    apply (adj.homEquiv Y.right T).injective
    simp only [Adjunction.homEquiv_unit]
    change adj.unit.app Y.right ≫ (adj.counit.app Y).right ≫ t.right = f
    rw [← Category.assoc, costar_counit_unit]
    change (𝟙 Y.right) ≫ f = f
    exact Category.id_comp f

private theorem canonicalWeight_native_isPushout (K : PointedSSet.{vC}) :
    IsPushout (freeRealization.{vC, uT}.map K.hom)
      (realizationCollapse (SSet.toCGWH.{uT, vC}.obj (Δ[0] : SSet.{vC})))
      (pointedRealizationQuotient.{vC, uT} K)
      (realizationPointLeg (SSet.pointedToCGWH.{uT, vC}.obj K)) := by
  let e : SSet.toCGWH.{uT, vC}.obj (Δ[0] : SSet.{vC}) ≅ CGWH.point :=
    SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{uT, vC}
  have h := costar_counit_isPushout (SSet.pointedToCGWH.obj K)
    (SSet.toCGWH.obj (Δ[0] : SSet.{vC})) e
  have hk : e.hom ≫ (SSet.pointedToCGWH.obj K).hom = SSet.toCGWH.map K.hom := by
    change e.hom ≫ e.inv ≫ SSet.toCGWH.map K.hom = SSet.toCGWH.map K.hom
    exact e.hom_inv_id_assoc _
  rw [hk] at h
  simpa only [freeRealization, Functor.comp_map, pointedRealizationQuotient] using h

/-- Direct pointed realization collapses the same freely realized chosen vertex. -/
theorem pointedRealization_isPushout (K : PointedSSet.{vC}) :
    IsPushout (freeRealization.map K.hom)
      (0 : freeRealization.obj (Δ[0] : SSet.{vC}) ⟶ (0 : PointedCGWH.{uT, vC}))
      (pointedRealizationQuotient K) (0 : (0 : PointedCGWH.{uT, vC}) ⟶ SSet.pointedToCGWH.obj K) := by
  let e : realizationPoint.{vC, uT} ≅ (0 : PointedCGWH.{uT, vC}) :=
    Under.mkIdInitial.uniqueUpToIso HasZeroObject.zeroIsInitial
  apply (canonicalWeight_native_isPushout K).of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _)
  · simp
  · exact HasZeroObject.zeroIsTerminal.hom_ext _ _
  · simp
  · exact Under.mkIdInitial.hom_ext _ _

/-- The original based-realization pushout is the canonical pointed realization. -/
def realizedWeightIsoPointedRealization (K : PointedSSet.{vC}) :
    realizedWeight.{vC, uT} K ≅ SSet.pointedToCGWH.{uT, vC}.obj K :=
  (IsPushout.of_hasPushout (freeRealization.map K.hom)
    (0 : freeRealization.obj (Δ[0] : SSet.{vC}) ⟶ (0 : PointedCGWH.{uT, vC}))).isoIsPushout
      _ _ (pointedRealization_isPushout K)

/-- The realization comparison preserves the entire original free-carrier quotient. -/
theorem weightQuotient_realizationIso (K : PointedSSet.{vC}) :
    weightQuotient K ≫ (realizedWeightIsoPointedRealization.{vC, uT} K).hom = pointedRealizationQuotient K :=
  (IsPushout.of_hasPushout (freeRealization.map K.hom)
    (0 : freeRealization.obj (Δ[0] : SSet.{vC}) ⟶ (0 : PointedCGWH.{uT, vC}))).inl_isoIsPushout_hom
      _ _ (pointedRealization_isPushout K)

end PointedRealizationComparison

/-- The actual native based circle is the geometric realization of the same entire original pointed circle. -/
abbrev realizedCircle : PointedCGWH.{uT, vC} := realizedWeight DerivedSuspensionLoopAdjunction.circle.{vC}

/-- The entire original realized standard one-simplex maps into the actual native circle quotient. -/
def realizedCircleQuotient : freeRealization.obj (SSet.stdSimplex.obj ⦋1⦌) ⟶ realizedCircle.{vC, uT} :=
  freeRealization.map DerivedSuspensionLoopAdjunction.circleQuotient ≫
    weightQuotient DerivedSuspensionLoopAdjunction.circle

/-- The same full original one-simplex boundary and native zero leg give the genuine geometric circle pushout. -/
theorem realizedCircle_isPushout :
    IsPushout (freeRealization.map DerivedSuspensionLoopAdjunction.circleBoundary.{vC})
      (0 : freeRealization.obj (SSet.boundary.{vC} 1 : SSet.{vC}) ⟶ (0 : PointedCGWH.{uT, vC}))
      realizedCircleQuotient (weightZeroLeg DerivedSuspensionLoopAdjunction.circle) := by
  let : PreservesColimitsOfSize.{0, 0} freeRealization.{vC, uT} :=
    freeRealizationAdjunction.leftAdjoint_preservesColimits
  have h₁ : IsPushout (freeRealization.map DerivedSuspensionLoopAdjunction.circleBoundary.{vC})
      (freeRealization.map (SSet.stdSimplex.isTerminalObj₀.from (SSet.boundary.{vC} 1 : SSet.{vC})))
      (freeRealization.map DerivedSuspensionLoopAdjunction.circleQuotient)
      (freeRealization.map DerivedSuspensionLoopAdjunction.circle.hom) :=
    (IsPushout.of_hasPushout DerivedSuspensionLoopAdjunction.circleBoundary
      (SSet.stdSimplex.isTerminalObj₀.from (SSet.boundary.{vC} 1 : SSet.{vC}))).map freeRealization
  have h := h₁.paste_vert
    (IsPushout.of_hasPushout (freeRealization.map DerivedSuspensionLoopAdjunction.circle.hom)
      (0 : freeRealization.obj (Δ[0] : SSet.{vC}) ⟶ (0 : PointedCGWH.{uT, vC})))
  simp only [comp_zero] at h
  exact h

/-- The actual realized original circle is cofibrant in the same native pointed CGWH model. -/
theorem realizedCircle_isCofibrant : IsCofibrant realizedCircle.{vC, uT} :=
  realizedWeight_isCofibrant _


section CanonicalCircleRealization

set_option backward.isDefEq.respectTransparency false

/-- The based-realization pushouts with their canonical functorial maps. -/
def realizedWeightFunctor : PointedSSet.{vC} ⥤ PointedCGWH.{uT, vC} where
  obj K := realizedWeight.{vC, uT} K
  map {K L} f := (realizedWeightIsoPointedRealization.{vC, uT} K).hom ≫
    SSet.pointedToCGWH.map f ≫ (realizedWeightIsoPointedRealization.{vC, uT} L).inv
  map_id K := by simp
  map_comp f g := by simp [Category.assoc]

/-- The original based-realization functor is naturally the canonical pointed realization. -/
def realizedWeightComparison : realizedWeightFunctor.{vC, uT} ≅ SSet.pointedToCGWH.{uT, vC} :=
  NatIso.ofComponents realizedWeightIsoPointedRealization (by
    intro K L f
    simp [realizedWeightFunctor, Category.assoc])

/-- Every pointed scalar map preserves the original entire realization quotient. -/
theorem weightQuotient_naturality {K L : PointedSSet.{vC}} (f : K ⟶ L) :
    weightQuotient.{vC, uT} K ≫ realizedWeightFunctor.map f =
      freeRealization.map f.right ≫ weightQuotient L := by
  rw [← cancel_mono (realizedWeightIsoPointedRealization.{vC, uT} L).hom]
  change (weightQuotient K ≫ ((realizedWeightIsoPointedRealization K).hom ≫ SSet.pointedToCGWH.map f ≫
      (realizedWeightIsoPointedRealization L).inv)) ≫ (realizedWeightIsoPointedRealization L).hom =
    (freeRealization.map f.right ≫ weightQuotient L) ≫ (realizedWeightIsoPointedRealization L).hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, weightQuotient_realizationIso, weightQuotient_realizationIso]
  have h := (Under.costarAdjForget CGWH.point.{uT, vC}).counit.naturality
    (SSet.pointedToCGWH.map f)
  change freeRealization.map f.right ≫ pointedRealizationQuotient L =
    pointedRealizationQuotient K ≫ SSet.pointedToCGWH.map f at h
  exact h.symm

/-- The original realized circle is the canonical realization of the actual simplicial circle. -/
def realizedCircleIsoPointedRealization :
    realizedCircle.{vC, uT} ≅ SSet.pointedToCGWH.{uT, vC}.obj SSet.pointedCircle.{vC} :=
  realizedWeightIsoPointedRealization SSet.pointedCircle

/-- The original realized circle is the native sphere one through the canonical realization iso. -/
def realizedCircleIsoSphereOne : realizedCircle.{vC, uT} ≅ PointedCGWH.sphereOne.{uT, vC} :=
  realizedCircleIsoPointedRealization ≪≫ PointedCGWH.pointedCircleRealizationIsoSphereOne

/-- The canonical comparison retains the entire original one-simplex quotient map. -/
theorem realizedCircleQuotient_realizationIso :
    realizedCircleQuotient.{vC, uT} ≫ realizedCircleIsoPointedRealization.hom =
      freeRealization.map circleQuotient ≫ pointedRealizationQuotient SSet.pointedCircle := by
  change (freeRealization.map circleQuotient ≫ weightQuotient circle) ≫
    (realizedWeightIsoPointedRealization circle).hom = _
  rw [Category.assoc, weightQuotient_realizationIso]

end CanonicalCircleRealization

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [EnrichedOrdinaryCategory PointedCGWH.{uT, vC} C]

/-- A genuine given pointed topological action, with both complete original adjunctions and source PP laws. -/
structure Action where
  /-- The original complete topological scalar tensor bifunctor. -/
  tensor : C ⥤ PointedCGWH.{uT, vC} ⥤ C
  /-- The original complete topological scalar cotensor bifunctor. -/
  cotensor : PointedCGWH.{uT, vC}ᵒᵖ ⥤ C ⥤ C
  /-- The original scalar tensor and enriched Hom adjunction. -/
  tensorHom : tensor ⊣₂ eHomFunctor PointedCGWH.{uT, vC} C
  /-- The original coefficient tensor and cotensor adjunction at every scalar. -/
  tensorCotensor : tensor.flip ⊣₂ cotensor
  cof_cof : ∀ {X X' : C} (i : X ⟶ X') {K L : PointedCGWH.{uT, vC}} (j : K ⟶ L)
    (s : tensor.PushoutObjObj i j),
    cofibrations C i → cofibrations PointedCGWH.{uT, vC} j → cofibrations C s.ι
  trivial_cof : ∀ {X X' : C} (i : X ⟶ X') {K L : PointedCGWH.{uT, vC}} (j : K ⟶ L)
    (s : tensor.PushoutObjObj i j),
    trivialCofibrations C i → cofibrations PointedCGWH.{uT, vC} j → trivialCofibrations C s.ι
  cof_trivial : ∀ {X X' : C} (i : X ⟶ X') {K L : PointedCGWH.{uT, vC}} (j : K ⟶ L)
    (s : tensor.PushoutObjObj i j),
    cofibrations C i → trivialCofibrations PointedCGWH.{uT, vC} j → trivialCofibrations C s.ι

variable (a : Action (C := C))

/-- Use the actual simplicial category induced by the compatible topological enrichment. -/
local instance compatibleSimplicialCategory8 : SimplicialCategory C :=
  PointedCGWH.NativeSimplicial.enrichedOrdinaryCategory C

/-- Singularization of the actual given topological Hom bifunctor. -/
abbrev singularHomBifunctor : Cᵒᵖ ⥤ C ⥤ SSet.{vC} :=
  eHomFunctor PointedCGWH.{uT, vC} C ⋙
    (Functor.whiskeringRight C PointedCGWH.{uT, vC} SSet.{vC}).obj singularFunctor

/-- The genuine singular enrichment retains both entire original topological Hom variance maps. -/
def singularHomFunctorIso : SimplicialCategory.sHomFunctor C ≅ singularHomBifunctor (C := C) :=
  NatIso.ofComponents (fun X => NatIso.ofComponents (fun Y => Iso.refl _) (by
    intro Y Y' p
    change eHomWhiskerLeft SSet.{vC} X.unop p ≫ 𝟙 _ =
      𝟙 _ ≫ singularFunctor.map (eHomWhiskerLeft PointedCGWH.{uT, vC} X.unop p)
    rw [Category.comp_id, Category.id_comp]
    exact PointedCGWH.NativeSimplicial.whiskerLeft C X.unop p)) (by
      intro X X' i
      apply NatTrans.ext
      funext Y
      change eHomWhiskerRight SSet.{vC} i.unop Y ≫ 𝟙 _ =
        𝟙 _ ≫ singularFunctor.map (eHomWhiskerRight PointedCGWH.{uT, vC} i.unop Y)
      rw [Category.comp_id, Category.id_comp]
      exact PointedCGWH.NativeSimplicial.whiskerRight C i.unop Y)

/-- The actual given topological tensor is evaluated on the original freely pointed geometric realization. -/
abbrev simplicialTensor : C ⥤ SSet.{vC} ⥤ C :=
  a.tensor ⋙ (Functor.whiskeringLeft SSet.{vC} PointedCGWH.{uT, vC} C).obj freeRealization

/-- The actual given topological cotensor is restricted along the same original geometric realization. -/
abbrev simplicialCotensor : SSet.{vC}ᵒᵖ ⥤ C ⥤ C := freeRealization.op ⋙ a.cotensor

/-- The original geometric and topological Hom adjunctions give the actual simplicial tensor/Hom pair. -/
def tensorHomAdjunction (X : C) :
    (simplicialTensor a).obj X ⊣ (SimplicialCategory.sHomFunctor C).obj (op X) :=
  ((freeRealizationAdjunction).comp (a.tensorHom.adj X)).ofNatIsoRight
    ((singularHomFunctorIso (C := C)).app (op X)).symm

/-- The full simplicial Hom function is the same original topological transpose followed by geometric adjunction. -/
theorem tensorHomAdjunction_homEquiv (X : C) (K : SSet.{vC}) (Y : C)
    (f : (a.tensor.obj X).obj (freeRealization.obj K) ⟶ Y) :
    (tensorHomAdjunction a X).homEquiv K Y f =
      freeRealizationAdjunction.homEquiv K (X ⟶[PointedCGWH.{uT, vC}] Y)
        ((a.tensorHom.adj X).homEquiv (freeRealization.obj K) Y f) := by
  rw [tensorHomAdjunction, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The genuine simplicial tensor/Hom parameter adjunction preserves every original coefficient map. -/
def tensorHomParametrized : simplicialTensor a ⊣₂ SimplicialCategory.sHomFunctor C :=
  ParametrizedAdjunction.mk' (tensorHomAdjunction a) (by
    intro X X' i K Y f
    rw [tensorHomAdjunction_homEquiv, tensorHomAdjunction_homEquiv]
    change freeRealizationAdjunction.homEquiv K (X ⟶[PointedCGWH.{uT, vC}] Y)
        (a.tensorHom.homEquiv ((a.tensor.map i).app (freeRealization.obj K) ≫ f)) =
      freeRealizationAdjunction.homEquiv K (X' ⟶[PointedCGWH.{uT, vC}] Y)
        (a.tensorHom.homEquiv f) ≫ eHomWhiskerRight SSet.{vC} i Y
    rw [a.tensorHom.homEquiv_naturality_one, PointedCGWH.NativeSimplicial.whiskerRight C i Y]
    exact freeRealizationAdjunction.homEquiv_naturality_right
      (a.tensorHom.homEquiv f) (((eHomFunctor PointedCGWH.{uT, vC} C).map i.op).app Y))

/-- The actual tensor/cotensor adjunction restricts along every original realized scalar arrow. -/
def tensorCotensorParametrized : (simplicialTensor a).flip ⊣₂ simplicialCotensor a :=
  ParametrizedAdjunction.mk' (fun K => a.tensorCotensor.adj (freeRealization.obj K)) (by
    intro K L k X Y f
    exact a.tensorCotensor.homEquiv_naturality_one (freeRealization.map k) f)

/-- The original simplicial action PP square is the identical topological action PP square on realized scalar maps. -/
def realizedPushout {X X' : C} (i : X ⟶ X') {K L : SSet.{vC}} (k : K ⟶ L)
    (s : (simplicialTensor a).PushoutObjObj i k) : a.tensor.PushoutObjObj i (freeRealization.map k) where
  pt := s.pt
  inl := s.inl
  inr := s.inr
  isPushout := s.isPushout
  ι := s.ι
  inl_ι := s.inl_ι
  inr_ι := s.inr_ι

/-- The actual given topological action and genuine geometric Quillen pair construct the compatible simplicial
action. -/
def simplicialAction : CompatibleSimplicialMapping.Action C where
  tensor := simplicialTensor a
  cotensor := simplicialCotensor a
  tensorHom := tensorHomParametrized a
  tensorCotensor := tensorCotensorParametrized a
  cof_cof {_ _} i {_ _} k s hi hk := by
    let : freeRealizationAdjunction.IsQuillenAdjunction := freeRealization_isQuillen
    exact a.cof_cof i (freeRealization.map k) (realizedPushout a i k s) hi
      (Adjunction.IsQuillenAdjunction.preservesCofibrations (adj := freeRealizationAdjunction) k hk)
  trivial_cof {_ _} i {_ _} k s hi hk := by
    let : freeRealizationAdjunction.IsQuillenAdjunction := freeRealization_isQuillen
    exact a.trivial_cof i (freeRealization.map k) (realizedPushout a i k s) hi
      (Adjunction.IsQuillenAdjunction.preservesCofibrations (adj := freeRealizationAdjunction) k hk)
  cof_trivial {_ _} i {_ _} k s hi hk := by
    let : freeRealizationAdjunction.IsQuillenAdjunction := freeRealization_isQuillen
    exact a.cof_trivial i (freeRealization.map k) (realizedPushout a i k s) hi
      (Adjunction.IsQuillenAdjunction.preservesTrivialCofibrations (adj := freeRealizationAdjunction) k hk)

/-- The actual native topological circle tensor is the original fixed-weight action endofunctor. -/
abbrev tensorCircle : C ⥤ C := a.tensor.flip.obj realizedCircle.{vC, uT}

/-- The actual native topological circle cotensor is the original fixed-weight action endofunctor. -/
abbrev cotensorCircle : C ⥤ C := a.cotensor.obj (op realizedCircle.{vC, uT})

/-- The original given full topological action supplies the actual native-circle endoadjunction. -/
abbrev circleAdjunction : tensorCircle a ⊣ cotensorCircle a := a.tensorCotensor.adj realizedCircle

/-- The original action PP law and proven cofibrancy of the actual native circle give the genuine Quillen
endoadjunction. -/
theorem circleAdjunction_isQuillen : (circleAdjunction a).IsQuillenAdjunction := by
  let : IsCofibrant realizedCircle.{vC, uT} := realizedCircle_isCofibrant
  have hK : cofibrations PointedCGWH.{uT, vC} (initial.to realizedCircle) :=
    (cofibration_iff _).mp inferInstance
  constructor
  · intro X X' i hi
    let : PreservesColimitsOfSize.{0, 0} (a.tensor.obj X) := (a.tensorHom.adj X).leftAdjoint_preservesColimits
    let : PreservesColimitsOfSize.{0, 0} (a.tensor.obj X') := (a.tensorHom.adj X').leftAdjoint_preservesColimits
    exact a.cof_cof i (initial.to realizedCircle)
      (Functor.PushoutObjObj.ofIsInitialRight a.tensor i (initial.to realizedCircle) initialIsInitial) hi hK
  · intro X X' i hi
    let : PreservesColimitsOfSize.{0, 0} (a.tensor.obj X) := (a.tensorHom.adj X).leftAdjoint_preservesColimits
    let : PreservesColimitsOfSize.{0, 0} (a.tensor.obj X') := (a.tensorHom.adj X').leftAdjoint_preservesColimits
    exact a.trivial_cof i (initial.to realizedCircle)
      (Functor.PushoutObjObj.ofIsInitialRight a.tensor i (initial.to realizedCircle) initialIsInitial) hi hK

attribute [local instance] circleAdjunction_isQuillen


section CanonicalCircleAction

set_option backward.isDefEq.respectTransparency false

/-- The full original circle tensor uses the canonical pointed-realization carrier. -/
def tensorPointedCircleComparison :
    tensorCircle a ≅ a.tensor.flip.obj (SSet.pointedToCGWH.obj SSet.pointedCircle) :=
  a.tensor.flip.mapIso realizedCircleIsoPointedRealization

/-- The full original circle cotensor uses the same canonical pointed-realization carrier. -/
def cotensorPointedCircleComparison :
    cotensorCircle a ≅ a.cotensor.obj (op (SSet.pointedToCGWH.obj SSet.pointedCircle)) :=
  a.cotensor.mapIso realizedCircleIsoPointedRealization.symm.op

/-- The original circle tensor is naturally the tensor by the native sphere one. -/
def tensorSphereOneComparison : tensorCircle a ≅ a.tensor.flip.obj PointedCGWH.sphereOne :=
  a.tensor.flip.mapIso realizedCircleIsoSphereOne

/-- The original circle cotensor is naturally the cotensor by the native sphere one. -/
def cotensorSphereOneComparison : cotensorCircle a ≅ a.cotensor.obj (op PointedCGWH.sphereOne) :=
  a.cotensor.mapIso realizedCircleIsoSphereOne.symm.op

/-- The full sphere-one tensor comparison is the original action image of the realization iso. -/
theorem tensorSphereOneComparison_hom_app (X : C) :
    (tensorSphereOneComparison a).hom.app X =
      (a.tensor.obj X).map realizedCircleIsoSphereOne.hom := rfl

/-- The full sphere-one cotensor comparison uses the inverse realization map in the opposite category. -/
theorem cotensorSphereOneComparison_hom_app (Y : C) :
    (cotensorSphereOneComparison a).hom.app Y =
      (a.cotensor.map realizedCircleIsoSphereOne.inv.op).app Y := rfl

/-- The given original action adjunction at the actual native sphere one. -/
abbrev sphereOneAdjunction : a.tensor.flip.obj PointedCGWH.sphereOne ⊣
    a.cotensor.obj (op PointedCGWH.sphereOne) := a.tensorCotensor.adj PointedCGWH.sphereOne

/-- The canonical sphere-one action pair is Quillen by the proved circle realization comparison. -/
theorem sphereOneAdjunction_isQuillen : (sphereOneAdjunction a).IsQuillenAdjunction := by
  let h : ((circleAdjunction a).ofNatIsoLeft (tensorSphereOneComparison a)).IsQuillenAdjunction :=
    inferInstance
  exact ⟨h.preservesCofibrations, h.preservesTrivialCofibrations⟩

attribute [local instance] sphereOneAdjunction_isQuillen

/-- Both sphere-one comparisons preserve the entire original action transpose on every Hom set. -/
theorem rawSphereOne_homEquiv (X Y : C) (f : (a.tensor.flip.obj PointedCGWH.sphereOne).obj X ⟶ Y) :
    (circleAdjunction a).homEquiv X Y ((tensorSphereOneComparison a).hom.app X ≫ f) ≫
      (cotensorSphereOneComparison a).hom.app Y = (sphereOneAdjunction a).homEquiv X Y f := by
  let e := realizedCircleIsoSphereOne.{vC, uT}
  have h := a.tensorCotensor.homEquiv_naturality_one e.hom f
  change (circleAdjunction a).homEquiv X Y ((tensorSphereOneComparison a).hom.app X ≫ f) =
    (sphereOneAdjunction a).homEquiv X Y f ≫ (a.cotensor.map e.hom.op).app Y at h
  rw [h, Category.assoc]
  change (sphereOneAdjunction a).homEquiv X Y f ≫
    ((a.cotensor.map e.hom.op).app Y ≫ (a.cotensor.map e.inv.op).app Y) = _
  rw [← NatTrans.comp_app, ← Functor.map_comp, ← op_comp, Iso.inv_hom_id,
    op_id, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.comp_id]

end CanonicalCircleAction

attribute [local instance] sphereOneAdjunction_isQuillen

section TensorCircleComparison

variable [HasZeroObject C]
/-- The same original zero object supplies the coefficient zero maps. -/
local instance coefficientZeroMorphisms9 : HasZeroMorphisms C := HasZeroObject.zeroMorphismsOfZeroObject

/-- The complete original action image of the native based-realization circle quotient. -/
def tensorCircleQuotient (X : C) :
    (a.tensor.obj X).obj (freeRealization.obj DerivedSuspensionLoopAdjunction.circle.right) ⟶
      (tensorCircle a).obj X := (a.tensor.obj X).map (weightQuotient DerivedSuspensionLoopAdjunction.circle)

/-- The actual topological action preserves the full original based-realization cofiber and both zero legs. -/
theorem tensorCircle_isPushout (X : C) :
    IsPushout ((a.tensor.obj X).map (freeRealization.map DerivedSuspensionLoopAdjunction.circle.hom))
      (0 : (a.tensor.obj X).obj (freeRealization.obj (Δ[0] : SSet.{vC})) ⟶ (0 : C))
      (tensorCircleQuotient a X) (0 : (0 : C) ⟶ (tensorCircle a).obj X) := by
  let T := a.tensor.obj X
  let : PreservesColimitsOfSize.{0, 0} T := (a.tensorHom.adj X).leftAdjoint_preservesColimits
  have h : IsPushout (T.map (freeRealization.map DerivedSuspensionLoopAdjunction.circle.hom))
      (T.map (0 : freeRealization.obj (Δ[0] : SSet.{vC}) ⟶ (0 : PointedCGWH.{uT, vC})))
      (T.map (weightQuotient DerivedSuspensionLoopAdjunction.circle))
      (T.map (weightZeroLeg DerivedSuspensionLoopAdjunction.circle)) :=
    (IsPushout.of_hasPushout (freeRealization.map DerivedSuspensionLoopAdjunction.circle.hom)
      (0 : freeRealization.obj (Δ[0] : SSet.{vC}) ⟶ (0 : PointedCGWH.{uT, vC}))).map T
  have hz : weightZeroLeg DerivedSuspensionLoopAdjunction.circle = (0 : (0 : PointedCGWH.{uT, vC}) ⟶ realizedCircle) :=
    zero_of_from_zero _
  exact h.of_iso (Iso.refl _) (Iso.refl _) (Functor.mapZeroObject T) (Iso.refl _)
    (by simp [T]) (by simp) (by simp [T, tensorCircleQuotient]) (by simp [hz])

/-- The constructed simplicial circle tensor is the same actual native topological-circle tensor on the original
carrier. -/
def tensorComparison (X : C) :
    Compatible.tensorObj (simplicialAction a) X DerivedSuspensionLoopAdjunction.circle ≅
      (tensorCircle a).obj X := (tensorCircle_isPushout a X).isoPushout.symm

/-- The complete tensor comparison retains the original action image of the entire native circle quotient. -/
@[reassoc]
theorem tensorComparison_quotient (X : C) :
    Compatible.tensorQuotient (simplicialAction a) X DerivedSuspensionLoopAdjunction.circle ≫
        (tensorComparison a X).hom = tensorCircleQuotient a X :=
  (tensorCircle_isPushout a X).inl_isoPushout_inv

/-- The full tensor comparison preserves every original coefficient action map. -/
theorem tensorComparison_naturality {X X' : C} (i : X ⟶ X') :
    Compatible.tensorMap (simplicialAction a) i DerivedSuspensionLoopAdjunction.circle ≫
        (tensorComparison a X').hom = (tensorComparison a X).hom ≫ (tensorCircle a).map i := by
  apply pushout.hom_ext
  · change Compatible.tensorQuotient (simplicialAction a) X DerivedSuspensionLoopAdjunction.circle ≫
        (Compatible.tensorMap (simplicialAction a) i DerivedSuspensionLoopAdjunction.circle ≫
          (tensorComparison a X').hom) =
      Compatible.tensorQuotient (simplicialAction a) X DerivedSuspensionLoopAdjunction.circle ≫
        ((tensorComparison a X).hom ≫ (tensorCircle a).map i)
    rw [Compatible.tensorMap_quotient_assoc, tensorComparison_quotient,
      ← Category.assoc, tensorComparison_quotient]
    exact ((a.tensor.map i).naturality (weightQuotient DerivedSuspensionLoopAdjunction.circle)).symm
  · exact HasZeroObject.zeroIsInitial.hom_ext _ _

/-- Both actual circle tensor functors retain every original coefficient arrow under the complete natural comparison. -/
def tensorFunctorComparison :
    Compatible.tensorFunctor (simplicialAction a) DerivedSuspensionLoopAdjunction.circle ≅ tensorCircle a :=
  NatIso.ofComponents (tensorComparison a) (fun i => tensorComparison_naturality a i)

/-- The original topological circle adjunction is transported along the genuine geometric tensor comparison. -/
def transportedCircleAdjunction :
    Compatible.tensorFunctor (simplicialAction a) DerivedSuspensionLoopAdjunction.circle ⊣ cotensorCircle a :=
  (circleAdjunction a).ofNatIsoLeft (tensorFunctorComparison a).symm

/-- The actual cotensor comparison is the full adjunction mate of the original geometric circle tensor comparison. -/
def cotensorFunctorComparison :
    Compatible.cotensorFunctor (simplicialAction a) DerivedSuspensionLoopAdjunction.circle ≅ cotensorCircle a :=
  (Compatible.circleAdjunction (simplicialAction a)).rightAdjointUniq (transportedCircleAdjunction a)

/-- The whole raw geometric circle comparison preserves the complete original action Hom functions. -/
theorem rawCircle_homEquiv (X Y : C) (f : (tensorCircle a).obj X ⟶ Y) :
    (Compatible.circleAdjunction (simplicialAction a)).homEquiv X Y
        ((tensorFunctorComparison a).hom.app X ≫ f) ≫ (cotensorFunctorComparison a).hom.app Y =
      (circleAdjunction a).homEquiv X Y f := by
  have hn : (Compatible.circleAdjunction (simplicialAction a)).homEquiv X Y
        ((tensorFunctorComparison a).hom.app X ≫ f) ≫ (cotensorFunctorComparison a).hom.app Y =
      (transportedCircleAdjunction a).homEquiv X Y ((tensorFunctorComparison a).hom.app X ≫ f) := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Category.assoc,
      (cotensorFunctorComparison a).hom.naturality, ← Category.assoc]
    exact congrArg (fun b => b ≫ (cotensorCircle a).map ((tensorFunctorComparison a).hom.app X ≫ f))
      (Adjunction.unit_rightAdjointUniq_hom_app
        (Compatible.circleAdjunction (simplicialAction a)) (transportedCircleAdjunction a) X)
  rw [hn, transportedCircleAdjunction, Adjunction.homEquiv_ofNatIsoLeft_apply, Iso.symm_hom,
    ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

end TensorCircleComparison

section TotalDerivedComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable [HasZeroObject C]
attribute [local instance] Compatible.circleAdjunction_isQuillen

/-- The genuine topological-circle total derived data use the same original Q and R records. -/
def derivedData (d : GeneratedFunctorialReplacements.Data (C := C)) :
    QuillenDerivedAdjunctionData (circleAdjunction a) :=
  DerivedAdjunctionCoherence.chosenDerivedAdjunctionData (circleAdjunction a) d d

/-- The actual total derived topological circle tensor retains the original Q. -/
abbrev derivedSuspension (d : GeneratedFunctorialReplacements.Data (C := C)) :=
  DerivedFunctorCoherence.left (circleAdjunction a) d

/-- The actual total derived topological circle cotensor retains the original R. -/
abbrev derivedLoops (d : GeneratedFunctorialReplacements.Data (C := C)) :=
  DerivedFunctorCoherence.right (circleAdjunction a) d

/-- The full original topological circle adjunction descends through the same Q/R data. -/
abbrev derivedAdjunction (d : GeneratedFunctorialReplacements.Data (C := C)) :
    derivedSuspension a d ⊣ derivedLoops a d :=
  DerivedAdjunctionCoherence.chosenAdjunction (circleAdjunction a) d d

/-- The full original geometric tensor comparison descends through the same actual Q on every Ho arrow. -/
def derivedTensorComparison (d : GeneratedFunctorialReplacements.Data (C := C)) :
    Compatible.derivedSuspension (simplicialAction a) d ≅ derivedSuspension a d where
  hom := DerivedFunctorCoherence.leftNat (Compatible.circleAdjunction (simplicialAction a))
    (circleAdjunction a) d (tensorFunctorComparison a).hom
  inv := DerivedFunctorCoherence.leftNat (circleAdjunction a)
    (Compatible.circleAdjunction (simplicialAction a)) d (tensorFunctorComparison a).inv
  hom_inv_id := by
    rw [DerivedFunctorCoherence.leftNat_comp, Iso.hom_inv_id, DerivedFunctorCoherence.leftNat_id]
  inv_hom_id := by
    rw [DerivedFunctorCoherence.leftNat_comp, Iso.inv_hom_id, DerivedFunctorCoherence.leftNat_id]

/-- The full original geometric cotensor comparison descends through the same actual R on every Ho arrow. -/
def derivedCotensorComparison (d : GeneratedFunctorialReplacements.Data (C := C)) :
    Compatible.derivedLoops (simplicialAction a) d ≅ derivedLoops a d where
  hom := DerivedFunctorCoherence.rightNat (Compatible.circleAdjunction (simplicialAction a))
    (circleAdjunction a) d (cotensorFunctorComparison a).hom
  inv := DerivedFunctorCoherence.rightNat (circleAdjunction a)
    (Compatible.circleAdjunction (simplicialAction a)) d (cotensorFunctorComparison a).inv
  hom_inv_id := by
    rw [DerivedFunctorCoherence.rightNat_comp, Iso.hom_inv_id, DerivedFunctorCoherence.rightNat_id]
  inv_hom_id := by
    rw [DerivedFunctorCoherence.rightNat_comp, Iso.inv_hom_id, DerivedFunctorCoherence.rightNat_id]

/-- Every entire original Q object keeps the actual original geometric tensor comparison map. -/
theorem derivedTensorComparison_hom_app (d : GeneratedFunctorialReplacements.Data (C := C)) (X : C) :
    (derivedTensorComparison a d).hom.app ((weakEquivalences C).Q.obj X) =
      (weakEquivalences C).Q.map ((tensorFunctorComparison a).hom.app (d.Q.obj X)) :=
  DerivedFunctorCoherence.leftNat_app (Compatible.circleAdjunction (simplicialAction a))
    (circleAdjunction a) d (tensorFunctorComparison a).hom X

/-- Every entire original R object keeps the actual original geometric cotensor comparison map. -/
theorem derivedCotensorComparison_hom_app (d : GeneratedFunctorialReplacements.Data (C := C)) (Y : C) :
    (derivedCotensorComparison a d).hom.app ((weakEquivalences C).Q.obj Y) =
      (weakEquivalences C).Q.map ((cotensorFunctorComparison a).hom.app (d.R.obj Y)) :=
  DerivedFunctorCoherence.rightNat_app (Compatible.circleAdjunction (simplicialAction a))
    (circleAdjunction a) d (cotensorFunctorComparison a).hom Y

/-- Both full genuine total-derived geometric comparisons preserve the same original circle adjunct on all Ho arrows. -/
theorem derivedCircle_homEquiv (d : GeneratedFunctorialReplacements.Data (C := C))
    (X Y : (weakEquivalences C).Localization) (f : (derivedSuspension a d).obj X ⟶ Y) :
    (Compatible.derivedAdjunction (simplicialAction a) d).homEquiv X Y
        ((derivedTensorComparison a d).hom.app X ≫ f) ≫ (derivedCotensorComparison a d).hom.app Y =
      (derivedAdjunction a d).homEquiv X Y f := by
  rcases X with ⟨⟨X⟩⟩
  rcases Y with ⟨⟨Y⟩⟩
  let γ := (weakEquivalences C).Q
  change γ.obj ((tensorCircle a).obj (d.Q.obj X)) ⟶ γ.obj Y at f
  let sAdj := Compatible.circleAdjunction (simplicialAction a)
  let tAdj := circleAdjunction a
  let : IsCofibrant (d.Q.obj X) := d.q_cofibrant X
  let : IsCofibrant ((tensorCircle a).obj (d.Q.obj X)) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := tAdj) inferInstance
  let : IsFibrant (d.R.obj Y) := d.r_fibrant Y
  obtain ⟨g, hg⟩ := map_surjective_of_isLocalization γ
    ((tensorCircle a).obj (d.Q.obj X)) (d.R.obj Y) (f ≫ γ.map (d.r.app Y))
  apply (cancel_epi (PointedFramingAction.qHomotopyIso d X).hom).mp
  have hs := DerivedAdjunctionCoherence.homEquiv_original sAdj d d X Y
    ((derivedTensorComparison a d).hom.app (γ.obj X) ≫ f)
  have ht := DerivedAdjunctionCoherence.homEquiv_original tAdj d d X Y f
  change γ.map (d.q.app X) ≫
      ((Compatible.derivedAdjunction (simplicialAction a) d).homEquiv (γ.obj X) (γ.obj Y)
        ((derivedTensorComparison a d).hom.app (γ.obj X) ≫ f) ≫
          (derivedCotensorComparison a d).hom.app (γ.obj Y)) =
    γ.map (d.q.app X) ≫ (derivedAdjunction a d).homEquiv (γ.obj X) (γ.obj Y) f
  rw [← Category.assoc, hs, ht, derivedTensorComparison_hom_app, Category.assoc, ← hg,
    ← Functor.map_comp, derivedCotensorComparison_hom_app]
  have hsm : DerivedAdjunctionCoherence.originalHomEquiv sAdj d d X Y
      (γ.map ((tensorFunctorComparison a).hom.app (d.Q.obj X) ≫ g)) =
    γ.map (sAdj.homEquiv (d.Q.obj X) (d.R.obj Y)
      ((tensorFunctorComparison a).hom.app (d.Q.obj X) ≫ g)) :=
    QuillenOrdinaryHoHom.homEquiv_map sAdj _ _ _
  have htm : DerivedAdjunctionCoherence.originalHomEquiv tAdj d d X Y (γ.map g) =
      γ.map (tAdj.homEquiv (d.Q.obj X) (d.R.obj Y) g) :=
    QuillenOrdinaryHoHom.homEquiv_map tAdj _ _ _
  rw [hsm, htm, ← Functor.map_comp, rawCircle_homEquiv]

section OrdinaryComparison

variable [HasLimitsOfSize.{0, vC} C] [HasColimitsOfSize.{0, vC} C]
  (d : GeneratedFunctorialReplacements.Data (C := C))

/-- Ordinary suspension is the total-derived actual topological-circle tensor through the entire genuine framing and
geometric comparison. -/
def suspensionComparison : suspension d ≅ derivedSuspension a d :=
  Compatible.suspensionComparison (simplicialAction a) d ≪≫ derivedTensorComparison a d

/-- Ordinary loops are the total-derived actual topological-circle cotensor through the entire original framing and
geometric comparison. -/
def loopsComparison : loops d ≅ derivedLoops a d :=
  Compatible.loopsComparison (simplicialAction a) d ≪≫ derivedCotensorComparison a d

/-- The full ordinary Hom function is the same actual topological total-derived Hom function on every Ho object and
arrow. -/
theorem comparison_homEquiv (X Y : (weakEquivalences C).Localization)
    (f : (derivedSuspension a d).obj X ⟶ Y) :
    (DerivedSuspensionLoopAdjunction.adjunction d).homEquiv X Y
        ((suspensionComparison a d).hom.app X ≫ f) ≫ (loopsComparison a d).hom.app Y =
      (derivedAdjunction a d).homEquiv X Y f := by
  have hs := Compatible.comparison_homEquiv (simplicialAction a) d X Y
    ((derivedTensorComparison a d).hom.app X ≫ f)
  have ht := derivedCircle_homEquiv a d X Y f
  dsimp only [suspensionComparison, loopsComparison, Iso.trans_hom, NatTrans.comp_app]
  rw [Category.assoc, ← Category.assoc, hs, ht]

/-- Both inverse ordinary comparison maps retain the full original inverse topological total-derived Hom function. -/
theorem comparison_homEquiv_symm (X Y : (weakEquivalences C).Localization)
    (g : X ⟶ (derivedLoops a d).obj Y) :
    (suspensionComparison a d).inv.app X ≫
        ((DerivedSuspensionLoopAdjunction.adjunction d).homEquiv X Y).symm
          (g ≫ (loopsComparison a d).inv.app Y) =
      ((derivedAdjunction a d).homEquiv X Y).symm g := by
  apply ((derivedAdjunction a d).homEquiv X Y).injective
  rw [← comparison_homEquiv, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp,
    Equiv.apply_symm_apply, Category.assoc, Iso.inv_hom_id_app, Category.comp_id, Equiv.apply_symm_apply]

/-- The actual topological derived unit retains the same entire original ordinary unit and both genuine comparisons. -/
theorem comparison_unit (X : (weakEquivalences C).Localization) :
    (DerivedSuspensionLoopAdjunction.unit d).app X ≫
        (loops d).map ((suspensionComparison a d).hom.app X) ≫
        (loopsComparison a d).hom.app ((derivedSuspension a d).obj X) =
      (derivedAdjunction a d).unit.app X := by
  have h := comparison_homEquiv a d X ((derivedSuspension a d).obj X) (𝟙 _)
  rw [Category.comp_id, Adjunction.homEquiv_id, Adjunction.homEquiv_unit] at h
  exact (Category.assoc _ _ _).symm.trans h

/-- The actual topological derived counit retains the same entire original ordinary counit and both genuine
comparisons. -/
theorem comparison_counit (Y : (weakEquivalences C).Localization) :
    (suspension d).map ((loopsComparison a d).hom.app Y) ≫
        (suspensionComparison a d).hom.app ((derivedLoops a d).obj Y) ≫
        (derivedAdjunction a d).counit.app Y = (DerivedSuspensionLoopAdjunction.counit d).app Y := by
  have h := comparison_homEquiv a d ((derivedLoops a d).obj Y) Y ((derivedAdjunction a d).counit.app Y)
  have hε : (derivedAdjunction a d).homEquiv ((derivedLoops a d).obj Y) Y
      ((derivedAdjunction a d).counit.app Y) = 𝟙 _ := by
    rw [← Adjunction.homEquiv_symm_id, Equiv.apply_symm_apply]
  rw [hε] at h
  change _ = (DerivedSuspensionLoopAdjunction.adjunction d).counit.app Y
  rw [← (DerivedSuspensionLoopAdjunction.adjunction d).homEquiv_symm_id Y]
  apply ((DerivedSuspensionLoopAdjunction.adjunction d).homEquiv ((loops d).obj Y) Y).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_left]
  apply (cancel_mono ((loopsComparison a d).hom.app Y)).mp
  rw [Category.assoc, h, Category.comp_id, Category.id_comp]

omit [HasZeroObject C] [HasLimitsOfSize.{0, vC} C] [HasColimitsOfSize.{0, vC} C] in
/-- The full actual topological total-derived suspension has its genuine first triangle. -/
theorem derivedSuspension_triangle (X : (weakEquivalences C).Localization) :
    (derivedSuspension a d).map ((derivedAdjunction a d).unit.app X) ≫
      (derivedAdjunction a d).counit.app ((derivedSuspension a d).obj X) = 𝟙 _ :=
  (derivedAdjunction a d).left_triangle_components X

omit [HasZeroObject C] [HasLimitsOfSize.{0, vC} C] [HasColimitsOfSize.{0, vC} C] in
/-- The full actual topological total-derived cotensor has its genuine second triangle. -/
theorem derivedLoops_triangle (Y : (weakEquivalences C).Localization) :
    (derivedAdjunction a d).unit.app ((derivedLoops a d).obj Y) ≫
      (derivedLoops a d).map ((derivedAdjunction a d).counit.app Y) = 𝟙 _ :=
  (derivedAdjunction a d).right_triangle_components Y

/-- The same original Q good-cylinder cofiber compares through its complete original maps to the actual native-circle
derived tensor. -/
def originalCylinderComparison (X : C) :
    (weakEquivalences C).Q.obj (originalCylinderCofiber d X) ≅
      (derivedSuspension a d).obj ((weakEquivalences C).Q.obj X) :=
  (suspensionCylinderIso d X).symm ≪≫ (suspensionComparison a d).app ((weakEquivalences C).Q.obj X)

/-- The same original R good-path fiber compares through its complete original maps to the actual native-circle derived
cotensor. -/
def originalPathComparison (Y : C) :
    (weakEquivalences C).Q.obj (originalPathFiber d Y) ≅
      (derivedLoops a d).obj ((weakEquivalences C).Q.obj Y) :=
  (loopsPathIso d Y).symm ≪≫ (loopsComparison a d).app ((weakEquivalences C).Q.obj Y)

end OrdinaryComparison


section SphereOneDerivedComparison

/-- The canonical sphere-one total left derived tensor uses the original Q record. -/
abbrev sphereOneDerivedSuspension (d : GeneratedFunctorialReplacements.Data (C := C)) :=
  DerivedFunctorCoherence.left (sphereOneAdjunction a) d

/-- The canonical sphere-one total right derived cotensor uses the original R record. -/
abbrev sphereOneDerivedLoops (d : GeneratedFunctorialReplacements.Data (C := C)) :=
  DerivedFunctorCoherence.right (sphereOneAdjunction a) d

/-- The entire original circle derived tensor compares naturally with the native sphere-one tensor. -/
def derivedSphereOneTensorComparison (d : GeneratedFunctorialReplacements.Data (C := C)) :
    derivedSuspension a d ≅ sphereOneDerivedSuspension a d where
  hom := DerivedFunctorCoherence.leftNat (circleAdjunction a) (sphereOneAdjunction a) d
    (tensorSphereOneComparison a).hom
  inv := DerivedFunctorCoherence.leftNat (sphereOneAdjunction a) (circleAdjunction a) d
    (tensorSphereOneComparison a).inv
  hom_inv_id := by
    rw [DerivedFunctorCoherence.leftNat_comp, Iso.hom_inv_id, DerivedFunctorCoherence.leftNat_id]
  inv_hom_id := by
    rw [DerivedFunctorCoherence.leftNat_comp, Iso.inv_hom_id, DerivedFunctorCoherence.leftNat_id]

/-- The entire original circle derived cotensor compares naturally with the native sphere-one cotensor. -/
def derivedSphereOneCotensorComparison (d : GeneratedFunctorialReplacements.Data (C := C)) :
    derivedLoops a d ≅ sphereOneDerivedLoops a d where
  hom := DerivedFunctorCoherence.rightNat (circleAdjunction a) (sphereOneAdjunction a) d
    (cotensorSphereOneComparison a).hom
  inv := DerivedFunctorCoherence.rightNat (sphereOneAdjunction a) (circleAdjunction a) d
    (cotensorSphereOneComparison a).inv
  hom_inv_id := by
    rw [DerivedFunctorCoherence.rightNat_comp, Iso.hom_inv_id, DerivedFunctorCoherence.rightNat_id]
  inv_hom_id := by
    rw [DerivedFunctorCoherence.rightNat_comp, Iso.inv_hom_id, DerivedFunctorCoherence.rightNat_id]

omit [HasZeroObject C] in
/-- Each represented object keeps the same original Q and the full realization comparison map. -/
theorem derivedSphereOneTensorComparison_hom_app
    (d : GeneratedFunctorialReplacements.Data (C := C)) (X : C) :
    (derivedSphereOneTensorComparison a d).hom.app ((weakEquivalences C).Q.obj X) =
      (weakEquivalences C).Q.map ((tensorSphereOneComparison a).hom.app (d.Q.obj X)) :=
  DerivedFunctorCoherence.leftNat_app (circleAdjunction a) (sphereOneAdjunction a) d
    (tensorSphereOneComparison a).hom X

omit [HasZeroObject C] in
/-- Each represented object keeps the same original R and the full inverse realization comparison map. -/
theorem derivedSphereOneCotensorComparison_hom_app
    (d : GeneratedFunctorialReplacements.Data (C := C)) (Y : C) :
    (derivedSphereOneCotensorComparison a d).hom.app ((weakEquivalences C).Q.obj Y) =
      (weakEquivalences C).Q.map ((cotensorSphereOneComparison a).hom.app (d.R.obj Y)) :=
  DerivedFunctorCoherence.rightNat_app (circleAdjunction a) (sphereOneAdjunction a) d
    (cotensorSphereOneComparison a).hom Y


section SphereOneOrdinaryComparison

variable [HasLimitsOfSize.{0, vC} C] [HasColimitsOfSize.{0, vC} C]

/-- Ordinary framing suspension is the total derived tensor by the canonical native sphere one. -/
def suspensionSphereOneComparison (d : GeneratedFunctorialReplacements.Data (C := C)) :
    suspension d ≅ sphereOneDerivedSuspension a d :=
  suspensionComparison a d ≪≫ derivedSphereOneTensorComparison a d

/-- Ordinary framing loops are the total derived cotensor by the canonical native sphere one. -/
def loopsSphereOneComparison (d : GeneratedFunctorialReplacements.Data (C := C)) :
    loops d ≅ sphereOneDerivedLoops a d :=
  loopsComparison a d ≪≫ derivedSphereOneCotensorComparison a d

end SphereOneOrdinaryComparison

end SphereOneDerivedComparison

end TotalDerivedComparison

end HomotopicalAlgebra.DerivedSuspensionLoopAdjunction.Topological

section supplied_branch
universe uSup vSup
open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.DerivedSuspensionLoopAdjunction.Supplied

variable {C : Type uSup} [Category.{vSup} C] [ModelCategory C]
  {L R : C ⥤ C} (a : L ⊣ R) [a.IsQuillenAdjunction]
  (q r : GeneratedFunctorialReplacements.Data (C := C))

/-- The full total-derived data of the supplied original Quillen endoadjunction. -/
def derivedData : QuillenDerivedAdjunctionData a :=
  DerivedAdjunctionCoherence.chosenDerivedAdjunctionData a q r

/-- The supplied pair's actual chosen total-derived adjunction. -/
abbrev derivedAdjunction : DerivedFunctorCoherence.left a q ⊣ DerivedFunctorCoherence.right a r :=
  DerivedAdjunctionCoherence.chosenAdjunction a q r

/-- The total-derived unit retains the supplied point-set unit and both original comparison maps. -/
theorem derivedUnit_source (X : C) :
    (derivedAdjunction a q r).unit.app ((weakEquivalences C).Q.obj X) ≫
        (DerivedFunctorCoherence.right a r).map ((DerivedFunctorCoherence.leftComparison a q).app X) =
      (weakEquivalences C).Q.map (a.unit.app X) ≫
        (DerivedFunctorCoherence.rightComparison a r).app (L.obj X) :=
  DerivedAdjunctionCoherence.unit_fac a q r X

/-- The total-derived counit retains the supplied point-set counit and both original comparison maps. -/
theorem derivedCounit_source (Y : C) :
    (DerivedFunctorCoherence.left a q).map ((DerivedFunctorCoherence.rightComparison a r).app Y) ≫
        (derivedAdjunction a q r).counit.app ((weakEquivalences C).Q.obj Y) =
      (DerivedFunctorCoherence.leftComparison a q).app (R.obj Y) ≫
        (weakEquivalences C).Q.map (a.counit.app Y) :=
  DerivedAdjunctionCoherence.counit_fac a q r Y

variable [HasZeroObject C] [HasLimitsOfSize.{0, vSup} C] [HasColimitsOfSize.{0, vSup} C]
  (d : GeneratedFunctorialReplacements.Data (C := C))

/-- The two specified source identifications of the supplied derived functors with ordinary suspension and loops.
No compatibility with an adjunction is assumed; that compatibility is constructed below. -/
structure Comparisons where
  /-- The original specified suspension comparison. -/
  suspension : DerivedSuspensionLoopAdjunction.suspension d ≅ DerivedFunctorCoherence.left a q
  /-- The original specified loop comparison. -/
  loops : DerivedSuspensionLoopAdjunction.loops d ≅ DerivedFunctorCoherence.right a r

variable (e : Comparisons a q r d)

/-- Transport the actual supplied derived adjunction along both specified comparison maps. -/
def ordinaryAdjunction : DerivedSuspensionLoopAdjunction.suspension d ⊣
    DerivedSuspensionLoopAdjunction.loops d :=
  ((derivedAdjunction a q r).ofNatIsoLeft e.suspension.symm).ofNatIsoRight e.loops.symm

/-- The complete transported Hom equivalence on the same ordinary functors. -/
def homEquiv (X Y : (weakEquivalences C).Localization) :
    ((DerivedSuspensionLoopAdjunction.suspension d).obj X ⟶ Y) ≃
      (X ⟶ (DerivedSuspensionLoopAdjunction.loops d).obj Y) :=
  (ordinaryAdjunction a q r d e).homEquiv X Y

/-- The actual transported ordinary unit retains both specified comparison maps. -/
def unit : 𝟭 (weakEquivalences C).Localization ⟶
    DerivedSuspensionLoopAdjunction.suspension d ⋙ DerivedSuspensionLoopAdjunction.loops d :=
  (ordinaryAdjunction a q r d e).unit

/-- The actual transported ordinary counit retains both specified comparison maps. -/
def counit : DerivedSuspensionLoopAdjunction.loops d ⋙
    DerivedSuspensionLoopAdjunction.suspension d ⟶ 𝟭 (weakEquivalences C).Localization :=
  (ordinaryAdjunction a q r d e).counit

/-- Both specified comparisons recover the entire supplied total-derived Hom function. -/
theorem comparison_homEquiv (X Y : (weakEquivalences C).Localization)
    (f : (DerivedFunctorCoherence.left a q).obj X ⟶ Y) :
    homEquiv a q r d e X Y (e.suspension.hom.app X ≫ f) ≫ e.loops.hom.app Y =
      (derivedAdjunction a q r).homEquiv X Y f := by
  rw [homEquiv, ordinaryAdjunction, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.homEquiv_ofNatIsoLeft_apply, Iso.symm_hom, Iso.symm_hom]
  have h : e.suspension.inv.app X ≫ (e.suspension.hom.app X ≫ f) = f := by
    rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  rw [h, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- Both inverse specified maps retain the entire inverse supplied total-derived Hom function. -/
theorem comparison_homEquiv_symm (X Y : (weakEquivalences C).Localization)
    (g : X ⟶ (DerivedFunctorCoherence.right a r).obj Y) :
    e.suspension.inv.app X ≫ (homEquiv a q r d e X Y).symm (g ≫ e.loops.inv.app Y) =
      ((derivedAdjunction a q r).homEquiv X Y).symm g := by
  apply ((derivedAdjunction a q r).homEquiv X Y).injective
  rw [← comparison_homEquiv a q r d e, ← Category.assoc, Iso.hom_inv_id_app,
    Category.id_comp, Equiv.apply_symm_apply, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id, Equiv.apply_symm_apply]

/-- Every supplied source Ho arrow retains the transported Hom naturality. -/
theorem homEquiv_source {X X' Y : (weakEquivalences C).Localization}
    (u : X' ⟶ X) (f : (DerivedSuspensionLoopAdjunction.suspension d).obj X ⟶ Y) :
    homEquiv a q r d e X' Y ((DerivedSuspensionLoopAdjunction.suspension d).map u ≫ f) =
      u ≫ homEquiv a q r d e X Y f :=
  (ordinaryAdjunction a q r d e).homEquiv_naturality_left u f

/-- Every supplied target arrow retains the transported Hom naturality. -/
theorem homEquiv_target {X Y Y' : (weakEquivalences C).Localization}
    (f : (DerivedSuspensionLoopAdjunction.suspension d).obj X ⟶ Y) (v : Y ⟶ Y') :
    homEquiv a q r d e X Y' (f ≫ v) =
      homEquiv a q r d e X Y f ≫ (DerivedSuspensionLoopAdjunction.loops d).map v :=
  (ordinaryAdjunction a q r d e).homEquiv_naturality_right f v

/-- Both original specified maps recover the complete supplied total-derived unit. -/
theorem comparison_unit (X : (weakEquivalences C).Localization) :
    (unit a q r d e).app X ≫
        (DerivedSuspensionLoopAdjunction.loops d).map (e.suspension.hom.app X) ≫
        e.loops.hom.app ((DerivedFunctorCoherence.left a q).obj X) =
      (derivedAdjunction a q r).unit.app X := by
  have h := comparison_homEquiv a q r d e X ((DerivedFunctorCoherence.left a q).obj X) (𝟙 _)
  rw [Category.comp_id, Adjunction.homEquiv_id] at h
  change ((ordinaryAdjunction a q r d e).unit.app X ≫
    (DerivedSuspensionLoopAdjunction.loops d).map (e.suspension.hom.app X)) ≫ _ = _ at h
  exact (Category.assoc _ _ _).symm.trans h

/-- Both original specified maps recover the complete supplied total-derived counit. -/
theorem comparison_counit (Y : (weakEquivalences C).Localization) :
    (DerivedSuspensionLoopAdjunction.suspension d).map (e.loops.hom.app Y) ≫
        e.suspension.hom.app ((DerivedFunctorCoherence.right a r).obj Y) ≫
        (derivedAdjunction a q r).counit.app Y = (counit a q r d e).app Y := by
  have h := comparison_homEquiv a q r d e ((DerivedFunctorCoherence.right a r).obj Y) Y
    ((derivedAdjunction a q r).counit.app Y)
  have hε : (derivedAdjunction a q r).homEquiv ((DerivedFunctorCoherence.right a r).obj Y) Y
      ((derivedAdjunction a q r).counit.app Y) = 𝟙 _ := by
    rw [← Adjunction.homEquiv_symm_id, Equiv.apply_symm_apply]
  rw [hε] at h
  change _ = (ordinaryAdjunction a q r d e).counit.app Y
  rw [← (ordinaryAdjunction a q r d e).homEquiv_symm_id Y]
  apply ((ordinaryAdjunction a q r d e).homEquiv ((DerivedSuspensionLoopAdjunction.loops d).obj Y) Y).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_left]
  apply (cancel_mono (e.loops.hom.app Y)).mp
  dsimp only [homEquiv] at h
  rw [Category.assoc, h, Category.comp_id, Category.id_comp]

/-- The supplied ordinary adjunction has its actual first triangle on every Ho object. -/
theorem left_triangle (X : (weakEquivalences C).Localization) :
    (DerivedSuspensionLoopAdjunction.suspension d).map ((unit a q r d e).app X) ≫
      (counit a q r d e).app ((DerivedSuspensionLoopAdjunction.suspension d).obj X) = 𝟙 _ :=
  (ordinaryAdjunction a q r d e).left_triangle_components X

/-- The supplied ordinary adjunction has its actual second triangle on every Ho object. -/
theorem right_triangle (Y : (weakEquivalences C).Localization) :
    (unit a q r d e).app ((DerivedSuspensionLoopAdjunction.loops d).obj Y) ≫
      (DerivedSuspensionLoopAdjunction.loops d).map ((counit a q r d e).app Y) = 𝟙 _ :=
  (ordinaryAdjunction a q r d e).right_triangle_components Y

/-- Adjoint uniqueness supplies the actual correction from framing to the supplied ordinary adjunction. -/
def framingAdjustment : DerivedSuspensionLoopAdjunction.suspension d ≅
    DerivedSuspensionLoopAdjunction.suspension d :=
  (DerivedSuspensionLoopAdjunction.adjunction d).leftAdjointUniq (ordinaryAdjunction a q r d e)

/-- The canonical framing suspension comparison is constructed from the specified map and its adjunction correction. -/
def framingSuspensionComparison : DerivedSuspensionLoopAdjunction.suspension d ≅
    DerivedFunctorCoherence.left a q :=
  framingAdjustment a q r d e ≪≫ e.suspension

/-- The original framing unit is identified with the supplied transported unit by the actual correction. -/
theorem framingAdjustment_unit (X : (weakEquivalences C).Localization) :
    (DerivedSuspensionLoopAdjunction.unit d).app X ≫
      (DerivedSuspensionLoopAdjunction.loops d).map ((framingAdjustment a q r d e).hom.app X) =
        (unit a q r d e).app X :=
  Adjunction.unit_leftAdjointUniq_hom_app
    (DerivedSuspensionLoopAdjunction.adjunction d) (ordinaryAdjunction a q r d e) X

/-- The original framing counit is identified with the supplied transported counit by the actual correction. -/
theorem framingAdjustment_counit (Y : (weakEquivalences C).Localization) :
    (framingAdjustment a q r d e).hom.app ((DerivedSuspensionLoopAdjunction.loops d).obj Y) ≫
      (counit a q r d e).app Y = (DerivedSuspensionLoopAdjunction.counit d).app Y :=
  Adjunction.leftAdjointUniq_hom_app_counit
    (DerivedSuspensionLoopAdjunction.adjunction d) (ordinaryAdjunction a q r d e) Y

/-- The genuine framing Hom function identifies the supplied derived adjunction through both constructed maps. -/
theorem framing_homEquiv (X Y : (weakEquivalences C).Localization)
    (f : (DerivedFunctorCoherence.left a q).obj X ⟶ Y) :
    (DerivedSuspensionLoopAdjunction.adjunction d).homEquiv X Y
        ((framingSuspensionComparison a q r d e).hom.app X ≫ f) ≫ e.loops.hom.app Y =
      (derivedAdjunction a q r).homEquiv X Y f := by
  have h (g : (DerivedSuspensionLoopAdjunction.suspension d).obj X ⟶ Y) :
      (DerivedSuspensionLoopAdjunction.adjunction d).homEquiv X Y
          ((framingAdjustment a q r d e).hom.app X ≫ g) = homEquiv a q r d e X Y g := by
    rw [Adjunction.homEquiv_unit, homEquiv, Adjunction.homEquiv_unit,
      Functor.map_comp, ← Category.assoc]
    exact congrArg (fun u => u ≫ (DerivedSuspensionLoopAdjunction.loops d).map g)
      (Adjunction.unit_leftAdjointUniq_hom_app
        (DerivedSuspensionLoopAdjunction.adjunction d) (ordinaryAdjunction a q r d e) X)
  dsimp only [framingSuspensionComparison, Iso.trans_hom, NatTrans.comp_app]
  rw [Category.assoc, h, comparison_homEquiv]

/-- An arbitrary original point-set adjunct is preserved through the supplied comparisons and original Q/R maps. -/
theorem pointset_homEquiv (X Y : C) (f : L.obj X ⟶ Y) :
    homEquiv a q r d e ((weakEquivalences C).Q.obj X) ((weakEquivalences C).Q.obj Y)
        (e.suspension.hom.app ((weakEquivalences C).Q.obj X) ≫
          (DerivedFunctorCoherence.leftComparison a q).app X ≫ (weakEquivalences C).Q.map f) ≫
        e.loops.hom.app ((weakEquivalences C).Q.obj Y) =
      (weakEquivalences C).Q.map (a.homEquiv X Y f) ≫
        (DerivedFunctorCoherence.rightComparison a r).app Y := by
  rw [comparison_homEquiv]
  exact DerivedAdjunctionCoherence.homEquiv_source_map a q r X Y f

/-- Every original inverse point-set adjunct retains the same Q/R and specified comparison maps. -/
theorem pointset_homEquiv_symm (X Y : C) (g : X ⟶ R.obj Y) :
    e.suspension.inv.app ((weakEquivalences C).Q.obj X) ≫
        (homEquiv a q r d e ((weakEquivalences C).Q.obj X) ((weakEquivalences C).Q.obj Y)).symm
          (((weakEquivalences C).Q.map g ≫ (DerivedFunctorCoherence.rightComparison a r).app Y) ≫
            e.loops.inv.app ((weakEquivalences C).Q.obj Y)) =
      (DerivedFunctorCoherence.leftComparison a q).app X ≫
        (weakEquivalences C).Q.map ((a.homEquiv X Y).symm g) := by
  rw [comparison_homEquiv_symm]
  exact DerivedAdjunctionCoherence.homEquiv_source_map_symm a q r X Y g

/-- Every Ho arrow preserves the actual supplied ordinary unit. -/
theorem unit_naturality {X Y : (weakEquivalences C).Localization} (u : X ⟶ Y) :
    u ≫ (unit a q r d e).app Y = (unit a q r d e).app X ≫
      (DerivedSuspensionLoopAdjunction.loops d).map
        ((DerivedSuspensionLoopAdjunction.suspension d).map u) :=
  (unit a q r d e).naturality u

/-- Every Ho arrow preserves the actual supplied ordinary counit. -/
theorem counit_naturality {X Y : (weakEquivalences C).Localization} (u : X ⟶ Y) :
    (DerivedSuspensionLoopAdjunction.suspension d).map
        ((DerivedSuspensionLoopAdjunction.loops d).map u) ≫ (counit a q r d e).app Y =
      (counit a q r d e).app X ≫ u :=
  (counit a q r d e).naturality u

/-- The caller's entire specified left comparison retains every Ho-arrow naturality. -/
theorem specifiedSuspension_naturality {X Y : (weakEquivalences C).Localization} (u : X ⟶ Y) :
    (DerivedSuspensionLoopAdjunction.suspension d).map u ≫ e.suspension.hom.app Y =
      e.suspension.hom.app X ≫ (DerivedFunctorCoherence.left a q).map u :=
  e.suspension.hom.naturality u

/-- The caller's entire specified right comparison retains every Ho-arrow naturality. -/
theorem specifiedLoops_naturality {X Y : (weakEquivalences C).Localization} (u : X ⟶ Y) :
    (DerivedSuspensionLoopAdjunction.loops d).map u ≫ e.loops.hom.app Y =
      e.loops.hom.app X ≫ (DerivedFunctorCoherence.right a r).map u :=
  e.loops.hom.naturality u

/-- The inverse framing Hom function retains both genuine inverse supplied comparisons. -/
theorem framing_homEquiv_symm (X Y : (weakEquivalences C).Localization)
    (g : X ⟶ (DerivedFunctorCoherence.right a r).obj Y) :
    (framingSuspensionComparison a q r d e).inv.app X ≫
        ((DerivedSuspensionLoopAdjunction.adjunction d).homEquiv X Y).symm
          (g ≫ e.loops.inv.app Y) = ((derivedAdjunction a q r).homEquiv X Y).symm g := by
  apply ((derivedAdjunction a q r).homEquiv X Y).injective
  rw [← framing_homEquiv a q r d e, ← Category.assoc, Iso.hom_inv_id_app,
    Category.id_comp, Equiv.apply_symm_apply, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id, Equiv.apply_symm_apply]

/-- The framing unit identifies the supplied derived unit through the constructed mate and specified loop map. -/
theorem framing_comparison_unit (X : (weakEquivalences C).Localization) :
    (DerivedSuspensionLoopAdjunction.unit d).app X ≫
        (DerivedSuspensionLoopAdjunction.loops d).map
          ((framingSuspensionComparison a q r d e).hom.app X) ≫
        e.loops.hom.app ((DerivedFunctorCoherence.left a q).obj X) =
      (derivedAdjunction a q r).unit.app X := by
  have h := framing_homEquiv a q r d e X ((DerivedFunctorCoherence.left a q).obj X) (𝟙 _)
  rw [Category.comp_id, Adjunction.homEquiv_id, Adjunction.homEquiv_unit] at h
  exact (Category.assoc _ _ _).symm.trans h

/-- The framing counit identifies the supplied derived counit through both constructed maps. -/
theorem framing_comparison_counit (Y : (weakEquivalences C).Localization) :
    (DerivedSuspensionLoopAdjunction.suspension d).map (e.loops.hom.app Y) ≫
        (framingSuspensionComparison a q r d e).hom.app ((DerivedFunctorCoherence.right a r).obj Y) ≫
        (derivedAdjunction a q r).counit.app Y = (DerivedSuspensionLoopAdjunction.counit d).app Y := by
  have h := framing_homEquiv a q r d e ((DerivedFunctorCoherence.right a r).obj Y) Y
    ((derivedAdjunction a q r).counit.app Y)
  have hε : (derivedAdjunction a q r).homEquiv ((DerivedFunctorCoherence.right a r).obj Y) Y
      ((derivedAdjunction a q r).counit.app Y) = 𝟙 _ := by
    rw [← Adjunction.homEquiv_symm_id, Equiv.apply_symm_apply]
  rw [hε] at h
  change _ = (DerivedSuspensionLoopAdjunction.adjunction d).counit.app Y
  rw [← (DerivedSuspensionLoopAdjunction.adjunction d).homEquiv_symm_id Y]
  apply ((DerivedSuspensionLoopAdjunction.adjunction d).homEquiv
    ((DerivedSuspensionLoopAdjunction.loops d).obj Y) Y).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_left]
  apply (cancel_mono (e.loops.hom.app Y)).mp
  rw [Category.assoc, h, Category.comp_id, Category.id_comp]

/-- The original cylinder cofiber is identified with the supplied left derived functor through the caller's map. -/
def specifiedCylinderComparison (X : C) :
    (weakEquivalences C).Q.obj (originalCylinderCofiber d X) ≅
      (DerivedFunctorCoherence.left a q).obj ((weakEquivalences C).Q.obj X) :=
  (suspensionCylinderIso d X).symm ≪≫ e.suspension.app ((weakEquivalences C).Q.obj X)

/-- The original cylinder cofiber has the coherent framing comparison to the actual supplied left derived functor. -/
def originalCylinderComparison (X : C) :
    (weakEquivalences C).Q.obj (originalCylinderCofiber d X) ≅
      (DerivedFunctorCoherence.left a q).obj ((weakEquivalences C).Q.obj X) :=
  (suspensionCylinderIso d X).symm ≪≫
    (framingSuspensionComparison a q r d e).app ((weakEquivalences C).Q.obj X)

/-- The original path fiber retains the caller's entire specified comparison to the supplied right derived functor. -/
def originalPathComparison (Y : C) :
    (weakEquivalences C).Q.obj (originalPathFiber d Y) ≅
      (DerivedFunctorCoherence.right a r).obj ((weakEquivalences C).Q.obj Y) :=
  (loopsPathIso d Y).symm ≪≫ e.loops.app ((weakEquivalences C).Q.obj Y)

end HomotopicalAlgebra.DerivedSuspensionLoopAdjunction.Supplied
end supplied_branch
