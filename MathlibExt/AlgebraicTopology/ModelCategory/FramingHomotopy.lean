/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import Mathlib.AlgebraicTopology.ModelCategory.FundamentalLemma
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import MathlibExt.AlgebraicTopology.ModelCategory.FiniteResolutionTensor
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedReplacementConstruction
public import MathlibExt.AlgebraicTopology.ModelCategory.Reedy
public import MathlibExt.AlgebraicTopology.SimplexCategory.Reedy
public import MathlibExt.CategoryTheory.Reedy.Boundary
public import MathlibExt.CategoryTheory.Reedy.Corner
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory

/-!
# Original endpoint diagrams for functorial framings

The evaluation adjoints use the actual finite coproducts and products of
the original coefficient category. Their fold and diagonal keep every
original map, and are naturally isomorphisms in degree zero. Restricting
these same diagrams along the original generated Q and R retains both
replacement arrows. No frame or homotopical mapping outcome is asserted.
-/

section

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uC vC w

open CategoryTheory Limits MorphismProperty Simplicial

namespace HomotopicalAlgebra.FramingEndpoints

variable {C : Type uC} [Category.{vC} C]

section Left

variable [HasFiniteColimits C]

/-- The original evaluation-left-adjoint cosimplicial diagram of finite copies of an object. -/
abbrev leftFree : C ⥤ CosimplicialObject C := evaluationLeftAdjoint C ⦋0⦌

/-- The original finite-copy fold to the same object's constant cosimplicial diagram. -/
def cosimplicialFold : leftFree (C := C) ⟶ CosimplicialObject.const C where
  app X :=
    { app j := Sigma.desc (fun _ : ⦋0⦌ ⟶ j => 𝟙 X)
      naturality j k f := by
        apply Sigma.hom_ext
        intro g
        simp [leftFree, evaluationLeftAdjoint] }
  naturality X Y f := by
    apply NatTrans.ext
    funext j
    apply Sigma.hom_ext
    intro g
    simp [leftFree, evaluationLeftAdjoint]

/-- Every original summand maps by the identity under the original fold. -/
@[reassoc]
theorem cosimplicialFold_ι (X : C) (j : SimplexCategory) (g : ⦋0⦌ ⟶ j) :
    Sigma.ι (fun _ : ⦋0⦌ ⟶ j => X) g ≫ ((cosimplicialFold (C := C)).app X).app j =
      𝟙 X := by
  simp [cosimplicialFold]

set_option backward.isDefEq.respectTransparency false in
/-- The original left endpoint diagram is naturally the original object in degree zero. -/
def leftDegreeZeroIso : leftFree (C := C) ⋙ (evaluation SimplexCategory C).obj ⦋0⦌ ≅ 𝟭 C :=
  NatIso.ofComponents
    (fun X =>
      { hom := ((cosimplicialFold (C := C)).app X).app ⦋0⦌
        inv := Sigma.ι (fun _ : ⦋0⦌ ⟶ ⦋0⦌ => X) (𝟙 ⦋0⦌)
        hom_inv_id := by
          apply Sigma.hom_ext
          intro g
          have h : g = 𝟙 ⦋0⦌ := SimplexCategory.hom_zero_zero g
          subst g
          rw [← Category.assoc, cosimplicialFold_ι]
          exact (Category.id_comp _).trans (Category.comp_id _).symm
        inv_hom_id := cosimplicialFold_ι X ⦋0⦌ (𝟙 ⦋0⦌) })
    (by
      intro X Y f
      apply Sigma.hom_ext
      intro g
      simp [leftFree, evaluationLeftAdjoint, cosimplicialFold])

/-- The degree-zero isomorphism retains the original whole finite-copy fold. -/
theorem leftDegreeZeroIso_hom (X : C) :
    (leftDegreeZeroIso (C := C)).hom.app X = ((cosimplicialFold (C := C)).app X).app ⦋0⦌ := rfl

/-- Its inverse retains the original identity-labelled summand inclusion. -/
theorem leftDegreeZeroIso_inv (X : C) :
    (leftDegreeZeroIso (C := C)).inv.app X =
      Sigma.ι (fun _ : ⦋0⦌ ⟶ ⦋0⦌ => X) (𝟙 ⦋0⦌) := rfl

end Left

section Right

variable [HasFiniteLimits C]

/-- The original evaluation-right-adjoint simplicial diagram of finite powers of an object. -/
abbrev rightFree : C ⥤ SimplicialObject C := evaluationRightAdjoint C (Opposite.op ⦋0⦌)

/-- The original finite-power diagonal from the same object's constant simplicial diagram. -/
def simplicialDiagonal : SimplicialObject.const C ⟶ rightFree (C := C) where
  app X :=
    { app j := Pi.lift (fun _ : j ⟶ Opposite.op ⦋0⦌ => 𝟙 X)
      naturality j k f := by
        apply Pi.hom_ext
        intro g
        simp [rightFree, evaluationRightAdjoint] }
  naturality X Y f := by
    apply NatTrans.ext
    funext j
    apply Pi.hom_ext
    intro g
    simp [rightFree, evaluationRightAdjoint]

/-- Every original factor projection recovers the identity from the original diagonal. -/
@[reassoc]
theorem simplicialDiagonal_π (X : C) (j : SimplexCategoryᵒᵖ) (g : j ⟶ Opposite.op ⦋0⦌) :
    ((simplicialDiagonal (C := C)).app X).app j ≫ Pi.π (fun _ : j ⟶ Opposite.op ⦋0⦌ => X) g =
      𝟙 X := by
  dsimp only [simplicialDiagonal]
  exact Pi.lift_comp_π (fun _ : j ⟶ Opposite.op ⦋0⦌ => 𝟙 X) g

set_option backward.isDefEq.respectTransparency false in
/-- The original right endpoint diagram is naturally the original object in degree zero. -/
def rightDegreeZeroIso : rightFree (C := C) ⋙ (evaluation SimplexCategoryᵒᵖ C).obj (Opposite.op
  ⦋0⦌) ≅
    𝟭 C :=
  NatIso.ofComponents
    (fun X =>
      { hom := Pi.π (fun _ : (Opposite.op ⦋0⦌ : SimplexCategoryᵒᵖ) ⟶ Opposite.op ⦋0⦌ => X) (𝟙
        (Opposite.op ⦋0⦌))
        inv := ((simplicialDiagonal (C := C)).app X).app (Opposite.op ⦋0⦌)
        hom_inv_id := by
          apply Pi.hom_ext
          intro g
          have h : g = 𝟙 (Opposite.op ⦋0⦌) := Quiver.Hom.unop_inj (SimplexCategory.hom_zero_zero
            g.unop)
          subst g
          rw [Category.assoc, simplicialDiagonal_π]
          exact (Category.comp_id _).trans (Category.id_comp _).symm
        inv_hom_id := simplicialDiagonal_π X (Opposite.op ⦋0⦌) (𝟙 (Opposite.op ⦋0⦌)) })
    (by
      intro X Y f
      simp [rightFree, evaluationRightAdjoint])

/-- The degree-zero isomorphism retains the original identity-labelled factor projection. -/
theorem rightDegreeZeroIso_hom (X : C) :
    (rightDegreeZeroIso (C := C)).hom.app X =
      Pi.π (fun _ : (Opposite.op ⦋0⦌ : SimplexCategoryᵒᵖ) ⟶ Opposite.op ⦋0⦌ => X) (𝟙 (Opposite.op
        ⦋0⦌)) := rfl

/-- Its inverse retains the original whole finite-power diagonal. -/
theorem rightDegreeZeroIso_inv (X : C) :
    (rightDegreeZeroIso (C := C)).inv.app X =
      ((simplicialDiagonal (C := C)).app X).app (Opposite.op ⦋0⦌) := rfl

end Right

section Generated

variable [ModelCategory C] {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

open GeneratedFunctorialReplacements

/-- The same original generated Q functor acts on every cosimplicial endpoint diagram. -/
abbrev originalLeft : C ⥤ CosimplicialObject C := Q d ⋙ leftFree

/-- The same original generated R functor acts on every simplicial endpoint diagram. -/
abbrev originalRight : C ⥤ SimplicialObject C := R d ⋙ rightFree

/-- Every original Q object is retained as the coefficient of the left endpoint diagram. -/
theorem originalLeft_obj (X : C) : (originalLeft d).obj X = leftFree.obj ((Q d).obj X) := rfl

/-- Every original Q map is retained as the whole left endpoint diagram map. -/
theorem originalLeft_map {X Y : C} (f : X ⟶ Y) :
    (originalLeft d).map f = leftFree.map ((Q d).map f) := rfl

/-- Every original R object is retained as the coefficient of the right endpoint diagram. -/
theorem originalRight_obj (X : C) : (originalRight d).obj X = rightFree.obj ((R d).obj X) := rfl

/-- Every original R map is retained as the whole right endpoint diagram map. -/
theorem originalRight_map {X Y : C} (f : X ⟶ Y) :
    (originalRight d).map f = rightFree.map ((R d).map f) := rfl

/-- The original whole fold is restricted along the same original generated Q. -/
def originalCosimplicialFold : originalLeft d ⟶ Q d ⋙ CosimplicialObject.const C :=
  Functor.whiskerLeft (Q d) cosimplicialFold

/-- The original whole diagonal is restricted along the same original generated R. -/
def originalSimplicialDiagonal : R d ⋙ SimplicialObject.const C ⟶ originalRight d :=
  Functor.whiskerLeft (R d) simplicialDiagonal

/-- The left generated endpoint in degree zero retains the same original Q functor. -/
def originalLeftZeroIso : originalLeft d ⋙ (evaluation SimplexCategory C).obj ⦋0⦌ ≅ Q d :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (Q d) leftDegreeZeroIso ≪≫
    Functor.rightUnitor _

/-- The right generated endpoint in degree zero retains the same original R functor. -/
def originalRightZeroIso :
    originalRight d ⋙ (evaluation SimplexCategoryᵒᵖ C).obj (Opposite.op ⦋0⦌) ≅ R d :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (R d) rightDegreeZeroIso ≪≫
    Functor.rightUnitor _

/-- The generated left degree-zero isomorphism is the unchanged original Q fold. -/
theorem originalLeftZeroIso_hom (X : C) :
    (originalLeftZeroIso d).hom.app X =
      ((cosimplicialFold (C := C)).app ((Q d).obj X)).app ⦋0⦌ := by
  simp [originalLeftZeroIso, leftDegreeZeroIso_hom]

/-- The generated right degree-zero inverse is the unchanged original R diagonal. -/
theorem originalRightZeroIso_inv (X : C) :
    (originalRightZeroIso d).inv.app X =
      ((simplicialDiagonal (C := C)).app ((R d).obj X)).app (Opposite.op ⦋0⦌) := by
  simp [originalRightZeroIso, rightDegreeZeroIso_inv]

/-- The left original replacement projection is retained in the whole endpoint augmentation. -/
def originalAugmentation : originalLeft d ⟶ CosimplicialObject.const C :=
  originalCosimplicialFold d ≫
    Functor.whiskerRight (counit d) (CosimplicialObject.const C) ≫
      (Functor.leftUnitor (CosimplicialObject.const C)).hom

/-- The right original replacement inclusion is retained in the whole endpoint coaugmentation. -/
def originalCoaugmentation : SimplicialObject.const C ⟶ originalRight d :=
  (Functor.leftUnitor (SimplicialObject.const C)).inv ≫
    Functor.whiskerRight (unit d) (SimplicialObject.const C) ≫ originalSimplicialDiagonal d

/-- Every component is the original Q fold followed by the same original Q counit. -/
theorem originalAugmentation_app (X : C) (j : SimplexCategory) :
    ((originalAugmentation d).app X).app j =
      ((cosimplicialFold (C := C)).app ((Q d).obj X)).app j ≫ (counit d).app X := by
  simp [originalAugmentation, originalCosimplicialFold]

/-- Every component is the same original R unit followed by the original R diagonal. -/
theorem originalCoaugmentation_app (X : C) (j : SimplexCategoryᵒᵖ) :
    ((originalCoaugmentation d).app X).app j =
      (unit d).app X ≫ ((simplicialDiagonal (C := C)).app ((R d).obj X)).app j := by
  change 𝟙 X ≫ (unit d).app X ≫
    ((simplicialDiagonal (C := C)).app ((R d).obj X)).app j = _
  exact Category.id_comp _

/-- The exact original Q counit is retained after the left degree-zero isomorphism. -/
theorem originalAugmentation_zero (X : C) :
    ((originalAugmentation d).app X).app ⦋0⦌ =
      (originalLeftZeroIso d).hom.app X ≫ (counit d).app X := by
  rw [originalAugmentation_app, originalLeftZeroIso_hom]

/-- The exact original R unit is retained before the right degree-zero inverse. -/
theorem originalCoaugmentation_zero (X : C) :
    ((originalCoaugmentation d).app X).app (Opposite.op ⦋0⦌) =
      (unit d).app X ≫ (originalRightZeroIso d).inv.app X := by
  rw [originalCoaugmentation_app, originalRightZeroIso_inv]

/-- The complete augmentation retains every original input morphism. -/
theorem originalAugmentation_naturality {X Y : C} (f : X ⟶ Y) (j : SimplexCategory) :
    ((originalLeft d).map f).app j ≫ ((originalAugmentation d).app Y).app j =
      ((originalAugmentation d).app X).app j ≫ f :=
  congrArg (fun a : (originalLeft d).obj X ⟶ (CosimplicialObject.const C).obj Y => a.app j)
    ((originalAugmentation d).naturality f)

/-- The complete coaugmentation retains every original input morphism. -/
theorem originalCoaugmentation_naturality {X Y : C} (f : X ⟶ Y) (j : SimplexCategoryᵒᵖ) :
    f ≫ ((originalCoaugmentation d).app Y).app j =
      ((originalCoaugmentation d).app X).app j ≫ ((originalRight d).map f).app j :=
  congrArg (fun a : (SimplicialObject.const C).obj X ⟶ (originalRight d).obj Y => a.app j)
    ((originalCoaugmentation d).naturality f)

end Generated

end HomotopicalAlgebra.FramingEndpoints

end
end
end

section



/-!
# Actual finite free endpoint boundaries

In positive degree, the original free cosimplicial endpoint cocone is
already its latching colimit. Dually, the original cofree simplicial
endpoint cone is already its matching limit. The universal maps retain
every original vertex and every original comparison triangle.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uC vC

open CategoryTheory Limits Simplicial
open CategoryTheory.ReedyStructure

namespace HomotopicalAlgebra.FramingEndpoints

/-- Every original vertex determines its actual positive-degree latching object. -/
def latchingVertex (j : SimplexCategory) (hj : 0 < j.len) (g : ⦋0⦌ ⟶ j) :
    SimplexCategory.reedy.Latching j := by
  let _ : Mono g := SimplexCategory.mono_iff_injective.mpr (fun x y _ => @Subsingleton.elim (Fin 1)
    inferInstance x y)
  exact SimplexCategory.reedy.latchingMk g ((SimplexCategory.reedy_direct g).2 inferInstance) hj

/-- Each original lower vertex gives its actual latching comparison triangle. -/
def latchingVertexComparison (j : SimplexCategory) (hj : 0 < j.len)
    (a : SimplexCategory.reedy.Latching j) (h : ⦋0⦌ ⟶ SimplexCategory.reedy.latchingSource a) :
    latchingVertex j hj (h ≫ SimplexCategory.reedy.latchingArrow a) ⟶ a := by
  let _ : Mono h := SimplexCategory.mono_iff_injective.mpr (fun x y _ => @Subsingleton.elim (Fin 1)
    inferInstance x y)
  exact ObjectProperty.homMk
    (Over.homMk ⟨h, (SimplexCategory.reedy_direct h).2 inferInstance⟩ (by
      apply WideSubcategory.hom_ext SimplexCategory.reedy.direct
      rfl))

/-- The latching comparison retains the same original vertex map. -/
theorem latchingVertexComparison_map (j : SimplexCategory) (hj : 0 < j.len)
    (a : SimplexCategory.reedy.Latching j) (h : ⦋0⦌ ⟶ SimplexCategory.reedy.latchingSource a) :
    SimplexCategory.reedy.latchingComparison (latchingVertexComparison j hj a h) = h := rfl

/-- Every original vertex determines its actual positive-degree matching object in the opposite
simplex category. -/
def matchingVertex (j : SimplexCategoryᵒᵖ) (hj : 0 < j.unop.len) (g : j ⟶ Opposite.op ⦋0⦌) :
    SimplexCategory.reedyOp.Matching j := by
  let _ : Mono g.unop :=
    SimplexCategory.mono_iff_injective.mpr (fun x y _ => @Subsingleton.elim (Fin 1) inferInstance
      x y)
  exact SimplexCategory.reedyOp.matchingMk g
    ((SimplexCategory.reedyOp_inverse g).2 inferInstance) hj

/-- Each original lower projection gives its actual matching comparison triangle. -/
def matchingVertexComparison (j : SimplexCategoryᵒᵖ) (hj : 0 < j.unop.len)
    (a : SimplexCategory.reedyOp.Matching j)
    (h : SimplexCategory.reedyOp.matchingTarget a ⟶ Opposite.op ⦋0⦌) :
    a ⟶ matchingVertex j hj (SimplexCategory.reedyOp.matchingArrow a ≫ h) := by
  let _ : Mono h.unop :=
    SimplexCategory.mono_iff_injective.mpr (fun x y _ => @Subsingleton.elim (Fin 1) inferInstance
      x y)
  exact ObjectProperty.homMk
    (Under.homMk ⟨h, (SimplexCategory.reedyOp_inverse h).2 inferInstance⟩ (by
      apply WideSubcategory.hom_ext SimplexCategory.reedyOp.inverse
      rfl))

/-- The matching comparison retains the same original projection map. -/
theorem matchingVertexComparison_map (j : SimplexCategoryᵒᵖ) (hj : 0 < j.unop.len)
    (a : SimplexCategory.reedyOp.Matching j)
    (h : SimplexCategory.reedyOp.matchingTarget a ⟶ Opposite.op ⦋0⦌) :
    SimplexCategory.reedyOp.matchingComparison (matchingVertexComparison j hj a h) = h := rfl

variable {C : Type uC} [Category.{vC} C]

section Latching

variable [HasFiniteColimits C]

/-- The original free endpoint diagram sends each original summand by the original simplex map. -/
@[reassoc]
theorem leftFree_map_ι (X : C) {i j : SimplexCategory} (f : i ⟶ j) (g : ⦋0⦌ ⟶ i) :
    Sigma.ι (fun _ : ⦋0⦌ ⟶ i => X) g ≫ (leftFree.obj X).map f =
      Sigma.ι (fun _ : ⦋0⦌ ⟶ j => X) (g ≫ f) := by
  simp [leftFree, evaluationLeftAdjoint]

set_option backward.isDefEq.respectTransparency false in
/-- The whole original positive-degree free endpoint cocone is its actual latching colimit. -/
def leftFreeLatchingIsColimit (X : C) (j : SimplexCategory) (hj : 0 < j.len) :
    IsColimit (SimplexCategory.reedy.latchingCocone (leftFree.obj X) j) where
  desc s := Sigma.desc (fun g : ⦋0⦌ ⟶ j =>
    Sigma.ι (fun _ : ⦋0⦌ ⟶ ⦋0⦌ => X) (𝟙 ⦋0⦌) ≫ s.ι.app (latchingVertex j hj g))
  fac s a := by
    apply Sigma.hom_ext
    intro h
    change Sigma.ι (fun _ : ⦋0⦌ ⟶ SimplexCategory.reedy.latchingSource a => X) h ≫
        (leftFree.obj X).map (SimplexCategory.reedy.latchingArrow a) ≫
          Sigma.desc (fun g : ⦋0⦌ ⟶ j =>
            Sigma.ι (fun _ : ⦋0⦌ ⟶ ⦋0⦌ => X) (𝟙 ⦋0⦌) ≫ s.ι.app (latchingVertex j hj g)) =
      Sigma.ι (fun _ : ⦋0⦌ ⟶ SimplexCategory.reedy.latchingSource a => X) h ≫ s.ι.app a
    rw [← Category.assoc, leftFree_map_ι, Sigma.ι_comp_desc]
    have hn := s.ι.naturality (latchingVertexComparison j hj a h)
    change (leftFree.obj X).map h ≫ s.ι.app a =
      s.ι.app (latchingVertex j hj (h ≫ SimplexCategory.reedy.latchingArrow a)) ≫ 𝟙 s.pt at hn
    have hn0 : (leftFree.obj X).map h ≫ s.ι.app a =
        s.ι.app (latchingVertex j hj (h ≫ SimplexCategory.reedy.latchingArrow a)) :=
      hn.trans (Category.comp_id _)
    have hc := congrArg (fun m => Sigma.ι (fun _ : ⦋0⦌ ⟶ ⦋0⦌ => X) (𝟙 ⦋0⦌) ≫ m) hn0
    rw [← Category.assoc, leftFree_map_ι] at hc
    simpa only [Category.id_comp] using hc.symm
  uniq s m hm := by
    apply Sigma.hom_ext
    intro g
    have hn := hm (latchingVertex j hj g)
    change (leftFree.obj X).map g ≫ m = s.ι.app (latchingVertex j hj g) at hn
    have hc := congrArg (fun k => Sigma.ι (fun _ : ⦋0⦌ ⟶ ⦋0⦌ => X) (𝟙 ⦋0⦌) ≫ k) hn
    rw [← Category.assoc, leftFree_map_ι] at hc
    rw [Sigma.ι_comp_desc]
    simpa only [Category.id_comp] using hc

/-- The actual positive-degree free latching map is the isomorphism of those same complete colimits.
-/
theorem leftFreeLatchingMap_isIso (X : C) (j : SimplexCategory) (hj : 0 < j.len) :
    IsIso (SimplexCategory.reedy.latchingMap (leftFree.obj X) j) :=
  ((colimit.isColimit (SimplexCategory.reedy.latchingDiagram (leftFree.obj X)
    j)).coconePointUniqueUpToIso
    (leftFreeLatchingIsColimit X j hj)).isIso_hom

end Latching

section Matching

variable [HasFiniteLimits C]

/-- The original cofree endpoint diagram sends each original projection by the original simplex map.
-/
@[reassoc]
theorem rightFree_map_π (X : C) {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) (g : j ⟶ Opposite.op ⦋0⦌) :
    (rightFree.obj X).map f ≫ Pi.π (fun _ : j ⟶ Opposite.op ⦋0⦌ => X) g =
      Pi.π (fun _ : i ⟶ Opposite.op ⦋0⦌ => X) (f ≫ g) := by
  simp [rightFree, evaluationRightAdjoint]

set_option backward.isDefEq.respectTransparency false in
/-- The whole original positive-degree cofree endpoint cone is its actual matching limit. -/
def rightFreeMatchingIsLimit (X : C) (j : SimplexCategoryᵒᵖ) (hj : 0 < j.unop.len) :
    IsLimit (SimplexCategory.reedyOp.matchingCone (rightFree.obj X) j) where
  lift s := Pi.lift (fun g : j ⟶ Opposite.op ⦋0⦌ =>
    s.π.app (matchingVertex j hj g) ≫
      Pi.π (fun _ : (Opposite.op ⦋0⦌ : SimplexCategoryᵒᵖ) ⟶ Opposite.op ⦋0⦌ => X) (𝟙 (Opposite.op
        ⦋0⦌)))
  fac s a := by
    apply Pi.hom_ext
    intro h
    change (Pi.lift (fun g : j ⟶ Opposite.op ⦋0⦌ =>
        s.π.app (matchingVertex j hj g) ≫
          Pi.π (fun _ : (Opposite.op ⦋0⦌ : SimplexCategoryᵒᵖ) ⟶ Opposite.op ⦋0⦌ => X) (𝟙
            (Opposite.op ⦋0⦌))) ≫
        (rightFree.obj X).map (SimplexCategory.reedyOp.matchingArrow a)) ≫
          Pi.π (fun _ : SimplexCategory.reedyOp.matchingTarget a ⟶ Opposite.op ⦋0⦌ => X) h =
      s.π.app a ≫ Pi.π (fun _ : SimplexCategory.reedyOp.matchingTarget a ⟶ Opposite.op ⦋0⦌ => X) h
    rw [Category.assoc, rightFree_map_π, Pi.lift_comp_π]
    have hn := s.π.naturality (matchingVertexComparison j hj a h)
    change 𝟙 s.pt ≫ s.π.app
        (matchingVertex j hj (SimplexCategory.reedyOp.matchingArrow a ≫ h)) =
      s.π.app a ≫ (rightFree.obj X).map h at hn
    rw [Category.id_comp] at hn
    have hc := congrArg (fun m => m ≫
      Pi.π (fun _ : (Opposite.op ⦋0⦌ : SimplexCategoryᵒᵖ) ⟶ Opposite.op ⦋0⦌ => X) (𝟙 (Opposite.op
        ⦋0⦌))) hn
    rw [Category.assoc, rightFree_map_π] at hc
    simpa only [Category.comp_id] using hc
  uniq s m hm := by
    apply Pi.hom_ext
    intro g
    have hn := hm (matchingVertex j hj g)
    change m ≫ (rightFree.obj X).map g = s.π.app (matchingVertex j hj g) at hn
    have hc := congrArg (fun k => k ≫
      Pi.π (fun _ : (Opposite.op ⦋0⦌ : SimplexCategoryᵒᵖ) ⟶ Opposite.op ⦋0⦌ => X) (𝟙 (Opposite.op
        ⦋0⦌))) hn
    rw [Category.assoc, rightFree_map_π] at hc
    rw [Pi.lift_comp_π]
    simpa only [Category.comp_id] using hc

/-- The actual positive-degree cofree matching map is the isomorphism of those same complete limits.
-/
theorem rightFreeMatchingMap_isIso (X : C) (j : SimplexCategoryᵒᵖ) (hj : 0 < j.unop.len) :
    IsIso (SimplexCategory.reedyOp.matchingMap (rightFree.obj X) j) :=
  ((rightFreeMatchingIsLimit X j hj).conePointUniqueUpToIso
    (limit.isLimit (SimplexCategory.reedyOp.matchingDiagram (rightFree.obj X) j))).isIso_hom

end Matching

end HomotopicalAlgebra.FramingEndpoints

end
end
end

section



/-!
# The actual collapse object of a positive simplicial latching boundary

For a positive simplex degree, the original collapse to the zero simplex gives an initial
object in the actual opposite-simplex latching category. Thus the original constant
simplicial latching cocone is colimiting. Only finite coefficient colimits are required.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uC vC

open CategoryTheory Limits MorphismProperty Simplicial

namespace HomotopicalAlgebra.FramingEndpoints

/-- The original simplex collapse, as the actual opposite arrow from degree zero. -/
def simplicialCollapse (j : SimplexCategoryᵒᵖ) : Opposite.op ⦋0⦌ ⟶ j :=
  (SimplexCategory.const j.unop ⦋0⦌ 0).op

/-- The original underlying collapse is an epimorphism of the original simplex category. -/
theorem simplicialCollapse_epi (j : SimplexCategoryᵒᵖ) : Epi (simplicialCollapse j).unop := by
  change Epi (SimplexCategory.const j.unop ⦋0⦌ 0)
  apply SimplexCategory.epi_iff_surjective.mpr
  intro b
  exact ⟨0, Subsingleton.elim (0 : Fin 1) b⟩

/-- The original collapse is an actual direct map of the opposite Reedy structure. -/
theorem simplicialCollapse_direct (j : SimplexCategoryᵒᵖ) :
    SimplexCategory.reedyOp.direct (simplicialCollapse j) :=
  (SimplexCategory.reedyOp_direct _).mpr (simplicialCollapse_epi j)

/-- The original positive-degree collapse is an actual object of its original latching category. -/
def collapseLatchingObject (j : SimplexCategoryᵒᵖ) (hj : 0 < j.unop.len) :
    SimplexCategory.reedyOp.Latching j :=
  SimplexCategory.reedyOp.latchingMk (simplicialCollapse j) (simplicialCollapse_direct j) hj

/-- Every original proper incoming arrow receives the original zero-source collapse triangle. -/
def collapseLatchingComparison (j : SimplexCategoryᵒᵖ) (hj : 0 < j.unop.len)
    (a : SimplexCategory.reedyOp.Latching j) : collapseLatchingObject j hj ⟶ a :=
  ObjectProperty.homMk (Over.homMk
    (⟨simplicialCollapse (SimplexCategory.reedyOp.latchingSource a),
      simplicialCollapse_direct (SimplexCategory.reedyOp.latchingSource a)⟩)
    (by
      apply WideSubcategory.hom_ext
      apply Quiver.Hom.unop_inj
      exact SimplexCategory.eq_const_to_zero _))

/-- The actual zero-source collapse object is initial in the original positive latching category. -/
def collapseLatchingIsInitial (j : SimplexCategoryᵒᵖ) (hj : 0 < j.unop.len) :
    IsInitial (collapseLatchingObject j hj) :=
  IsInitial.ofUniqueHom (collapseLatchingComparison j hj) (fun a f ↦ by
    apply SimplexCategory.reedyOp.latchingComparison_injective j (collapseLatchingObject j hj) a
    apply Quiver.Hom.unop_inj
    exact (SimplexCategory.eq_const_to_zero _).trans (SimplexCategory.eq_const_to_zero _).symm)

variable {C : Type uC} [Category.{vC} C]

/-- The whole original constant simplicial latching cocone is colimiting at every positive degree.
-/
def constantSimplicialLatchingIsColimit (X : C) (j : SimplexCategoryᵒᵖ)
    (hj : 0 < j.unop.len) :
    IsColimit (SimplexCategory.reedyOp.latchingCocone ((SimplicialObject.const C).obj X) j) where
  desc s := s.ι.app (collapseLatchingObject j hj)
  fac s a := by
    have hn := s.w (collapseLatchingComparison j hj a)
    change 𝟙 X ≫ s.ι.app a = s.ι.app (collapseLatchingObject j hj) at hn
    change 𝟙 X ≫ s.ι.app (collapseLatchingObject j hj) = s.ι.app a
    calc
      𝟙 X ≫ s.ι.app (collapseLatchingObject j hj) =
          s.ι.app (collapseLatchingObject j hj) := Category.id_comp _
      _ = 𝟙 X ≫ s.ι.app a := hn.symm
      _ = s.ι.app a := Category.id_comp _
  uniq s m hm := by
    have h := hm (collapseLatchingObject j hj)
    change 𝟙 X ≫ m = s.ι.app (collapseLatchingObject j hj) at h
    exact (Category.id_comp m).symm.trans h

/-- The actual constant simplicial latching map is an isomorphism at every positive degree. -/
theorem constantSimplicialLatchingMap_isIso [HasFiniteColimits C] (X : C)
    (j : SimplexCategoryᵒᵖ) (hj : 0 < j.unop.len) :
    IsIso (CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedyOp
      ((SimplicialObject.const C).obj X) j) := by
  let c := SimplexCategory.reedyOp.latchingCocone ((SimplicialObject.const C).obj X) j
  let hc : IsColimit c := constantSimplicialLatchingIsColimit X j hj
  let e : colimit (SimplexCategory.reedyOp.latchingDiagram
      ((SimplicialObject.const C).obj X) j) ≅ X := colimit.isoColimitCocone ⟨c, hc⟩
  have he : CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedyOp
      ((SimplicialObject.const C).obj X) j = e.hom := by
    apply colimit.hom_ext
    intro a
    rw [CategoryTheory.ReedyStructure.latchingMap_ι]
    exact (colimit.isoColimitCocone_ι_hom ⟨c, hc⟩ a).symm
  rw [he]
  infer_instance

end HomotopicalAlgebra.FramingEndpoints

end
end
end

section



/-!
# Actual Reedy model objects from original boundary maps

The constant original initial and terminal diagrams identify the actual Reedy
object conditions with the original latching and matching maps. Only the
original boundary shapes are assumed to have the required limits or colimits.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uJ vJ uD uC vC

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.ReedyModel.Shape

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]

/-- The actual latching boundary of the original constant initial diagram is initial. -/
def initialLatchingIsInitial [HasInitial C] [∀ j, HasColimitsOfShape (r.Latching j) C] (j : J) :
    IsInitial (colimit (r.latchingDiagram ((Functor.const J).obj (⊥_ C)) j)) := by
  change IsInitial (colimit ((Functor.const (r.Latching j)).obj (⊥_ C)))
  exact initialIsInitial.ofIso colimitConstInitial.symm

/-- The actual matching boundary of the original constant terminal diagram is terminal. -/
def terminalMatchingIsTerminal [HasTerminal C] [∀ j, HasLimitsOfShape (r.Matching j) C] (j : J) :
    IsTerminal (limit (r.matchingDiagram ((Functor.const J).obj (⊤_ C)) j)) := by
  change IsTerminal (limit ((Functor.const (r.Matching j)).obj (⊤_ C)))
  exact terminalIsTerminal.ofIso limitConstTerminal.symm

/-- The original constant initial latching map is an actual isomorphism between initial objects. -/
theorem initialLatchingMap_isIso [HasInitial C] [∀ j, HasColimitsOfShape (r.Latching j) C] (j : J) :
    IsIso (CategoryTheory.ReedyStructure.latchingMap r ((Functor.const J).obj (⊥_ C)) j) :=
  isIso_of_isInitial (initialLatchingIsInitial r j) initialIsInitial _

/-- The original constant terminal matching map is an actual isomorphism between terminal objects.
-/
theorem terminalMatchingMap_isIso [HasTerminal C] [∀ j, HasLimitsOfShape (r.Matching j) C] (j : J) :
    IsIso (CategoryTheory.ReedyStructure.matchingMap r ((Functor.const J).obj (⊤_ C)) j) :=
  isIso_of_isTerminal terminalIsTerminal (terminalMatchingIsTerminal r j) _

/-- The original initial-diagram corner retains its actual complete latching map Arrow. -/
def initialLatchingArrowIso [HasInitial C] [HasPushouts C]
    [∀ j, HasColimitsOfShape (r.Latching j) C] (X : J ⥤ C) (j : J) :
    Arrow.mk (CategoryTheory.ReedyStructure.latchingMap r X j) ≅
      Arrow.mk (CategoryTheory.ReedyStructure.latchingCorner r
        ((Functor.isInitialConst J initialIsInitial).to X) j) := by
  let _ := initialLatchingMap_isIso (C := C) r j
  let f := (Functor.isInitialConst J initialIsInitial).to X
  let i := pushout.inr (CategoryTheory.ReedyStructure.latchingMap r ((Functor.const J).obj (⊥_
    C)) j)
    (colimMap (r.latchingTransformation f j))
  let _ : IsIso i := by dsimp only [i]; infer_instance
  exact Arrow.isoMk (asIso i) (Iso.refl _) (by
    change i ≫ CategoryTheory.ReedyStructure.latchingCorner r f j =
      CategoryTheory.ReedyStructure.latchingMap r X j ≫ 𝟙 _
    rw [Category.comp_id]
    exact CategoryTheory.ReedyStructure.latchingCorner_inr r f j)

/-- The original terminal-diagram corner retains its actual complete matching map Arrow. -/
def terminalMatchingArrowIso [HasTerminal C] [HasPullbacks C]
    [∀ j, HasLimitsOfShape (r.Matching j) C] (X : J ⥤ C) (j : J) :
    Arrow.mk (CategoryTheory.ReedyStructure.matchingCorner r
      ((Functor.isTerminalConst J terminalIsTerminal).from X) j) ≅
      Arrow.mk (CategoryTheory.ReedyStructure.matchingMap r X j) := by
  let _ := terminalMatchingMap_isIso (C := C) r j
  let f := (Functor.isTerminalConst J terminalIsTerminal).from X
  let p := pullback.fst (limMap (r.matchingTransformation f j))
    (CategoryTheory.ReedyStructure.matchingMap r ((Functor.const J).obj (⊤_ C)) j)
  let _ : IsIso p := by dsimp only [p]; infer_instance
  exact Arrow.isoMk (Iso.refl _) (asIso p) (by
    change 𝟙 _ ≫ CategoryTheory.ReedyStructure.matchingMap r X j =
      CategoryTheory.ReedyStructure.matchingCorner r f j ≫ p
    rw [Category.id_comp]
    exact (CategoryTheory.ReedyStructure.matchingCorner_fst r f j).symm)

section Model

variable [ModelCategory C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

/-- Actual Reedy cofibrancy is exactly source cofibrancy of every whole original latching map. -/
theorem isCofibrant_iff_latching (X : J ⥤ C) :
    letI := modelCategory r Fc Ff
    IsCofibrant X ↔ ∀ j : J, Cofibration (CategoryTheory.ReedyStructure.latchingMap r X j) := by
  let _ := modelCategory r Fc Ff
  rw [isCofibrant_iff_of_isInitial ((Functor.isInitialConst J initialIsInitial).to X)
    (Functor.isInitialConst J initialIsInitial), cofibration_iff_source r Fc Ff]
  exact forall_congr' (fun j ↦ by
    simp only [cofibration_iff]
    exact ((cofibrations C).arrow_mk_iso_iff (initialLatchingArrowIso r X j)).symm)

/-- Actual Reedy fibrancy is exactly source fibrancy of every whole original matching map. -/
theorem isFibrant_iff_matching (X : J ⥤ C) :
    letI := modelCategory r Fc Ff
    IsFibrant X ↔ ∀ j : J, Fibration (CategoryTheory.ReedyStructure.matchingMap r X j) := by
  let _ := modelCategory r Fc Ff
  rw [isFibrant_iff_of_isTerminal ((Functor.isTerminalConst J terminalIsTerminal).from X)
    (Functor.isTerminalConst J terminalIsTerminal), fibration_iff_source r Fc Ff]
  exact forall_congr' (fun j ↦ by
    simp only [fibration_iff]
    exact (fibrations C).arrow_mk_iso_iff (terminalMatchingArrowIso r X j))

end Model

end HomotopicalAlgebra.ReedyModel.Shape

end
end
end

section



/-!
# Original constant simplicial maps and their actual Reedy corners

Positive-degree constant latching maps are original isomorphisms. The
degree-zero boundary is empty, and its corner retains the complete original
coefficient arrow. Thus every source property containing and respecting
isomorphisms is retained by the actual constant-map latching class.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uC vC

open CategoryTheory Limits MorphismProperty Simplicial

namespace HomotopicalAlgebra.FramingEndpoints

variable {C : Type uC} [Category.{vC} C] [HasFiniteColimits C]

/-- Both actual positive constant boundaries make the complete original corner an isomorphism. -/
theorem constantSimplicialCorner_isIso_positive {X Y : C} (f : X ⟶ Y)
    (j : SimplexCategoryᵒᵖ) (hj : 0 < j.unop.len) :
    IsIso (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp
      ((SimplicialObject.const C).map f) j) := by
  let _ := constantSimplicialLatchingMap_isIso X j hj
  let _ := constantSimplicialLatchingMap_isIso Y j hj
  let i := pushout.inr
    (CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedyOp ((SimplicialObject.const
      C).obj X) j)
    (colimMap (SimplexCategory.reedyOp.latchingTransformation ((SimplicialObject.const C).map f) j))
  let _ : IsIso i := by dsimp only [i]; infer_instance
  exact IsIso.of_isIso_fac_left
    (CategoryTheory.ReedyStructure.latchingCorner_inr SimplexCategory.reedyOp
      ((SimplicialObject.const C).map f) j)

/-- The original zero constant latching boundary is genuinely initial. -/
def constantSimplicialZeroLatchingIsInitial (X : C) :
    IsInitial (colimit (SimplexCategory.reedyOp.latchingDiagram
      ((SimplicialObject.const C).obj X) (Opposite.op ⦋0⦌))) :=
  isColimitEquivIsInitialOfIsEmpty C (colimit.cocone _) (colimit.isColimit _)

/-- The actual original comparison between the two zero constant boundaries is an isomorphism. -/
theorem constantSimplicialZeroComparison_isIso {X Y : C} (f : X ⟶ Y) :
    IsIso (colimMap (SimplexCategory.reedyOp.latchingTransformation
      ((SimplicialObject.const C).map f) (Opposite.op ⦋0⦌))) :=
  isIso_of_isInitial (constantSimplicialZeroLatchingIsInitial X)
    (constantSimplicialZeroLatchingIsInitial Y) _

/-- The original zero-degree constant corner retains the unchanged complete coefficient Arrow. -/
def constantSimplicialZeroCornerArrowIso {X Y : C} (f : X ⟶ Y) :
    Arrow.mk f ≅ Arrow.mk (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp
      ((SimplicialObject.const C).map f) (Opposite.op ⦋0⦌)) := by
  let _ := constantSimplicialZeroComparison_isIso f
  let i := pushout.inl
    (CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedyOp
      ((SimplicialObject.const C).obj X) (Opposite.op ⦋0⦌))
    (colimMap (SimplexCategory.reedyOp.latchingTransformation
      ((SimplicialObject.const C).map f) (Opposite.op ⦋0⦌)))
  let _ : IsIso i := by dsimp only [i]; infer_instance
  exact Arrow.isoMk (asIso i) (Iso.refl _) (by
    change i ≫ CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp
      ((SimplicialObject.const C).map f) (Opposite.op ⦋0⦌) = f ≫ 𝟙 _
    rw [Category.comp_id]
    exact CategoryTheory.ReedyStructure.latchingCorner_inl SimplexCategory.reedyOp
      ((SimplicialObject.const C).map f) (Opposite.op ⦋0⦌))

/-- Every original constant corner retains any source property containing and respecting
isomorphisms. -/
theorem constantSimplicialCorner_mem (P : MorphismProperty C) [P.ContainsIdentities] [P.RespectsIso]
    {X Y : C} (f : X ⟶ Y) (hf : P f) (j : SimplexCategoryᵒᵖ) :
    P (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp
      ((SimplicialObject.const C).map f) j) := by
  by_cases hj : j.unop.len = 0
  · have he : j = Opposite.op ⦋0⦌ := Opposite.unop_injective (SimplexCategory.ext hj)
    subst j
    exact (P.arrow_mk_iso_iff (constantSimplicialZeroCornerArrowIso f)).mp hf
  · let _ := constantSimplicialCorner_isIso_positive f j (Nat.pos_of_ne_zero hj)
    exact P.of_isIso _

/-- The actual original constant-map latching class retains the original source property. -/
theorem constantSimplicial_latchingClass (P : MorphismProperty C)
    [P.ContainsIdentities] [P.RespectsIso] {X Y : C} (f : X ⟶ Y) (hf : P f) :
    CategoryTheory.ReedyStructure.latchingClass SimplexCategory.reedyOp P ((SimplicialObject.const
      C).map f) :=
  constantSimplicialCorner_mem P f hf

end HomotopicalAlgebra.FramingEndpoints

end
end
end

section



/-!
# Degree-one boundaries of arbitrary simplicial diagrams

The actual simplex latching category at degree one contains precisely the
original cofaces δ₀ and δ₁, in that order. The opposite matching category
contains their original opposites. Their complete universal boundaries are
therefore the binary coproduct and product of the original degree-zero object.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uC vC

open CategoryTheory Limits Simplicial
open CategoryTheory.ReedyStructure

namespace HomotopicalAlgebra.FramingDegreeOneBoundaries

/-- The original coface is an object of the actual degree-one latching category. -/
abbrev latchingOneVertex (i : Fin 2) : SimplexCategory.reedy.Latching ⦋1⦌ :=
  ⟨Over.mk ⟨SimplexCategory.δ i, (SimplexCategory.reedy_direct _).2 inferInstance⟩,
    Nat.zero_lt_succ 0⟩

/-- The original opposite coface is an object of the actual degree-one matching category. -/
abbrev matchingOneVertex (i : Fin 2) :
    SimplexCategory.reedyOp.Matching (Opposite.op ⦋1⦌) :=
  ⟨Under.mk ⟨(SimplexCategory.δ i).op, (SimplexCategory.reedyOp_inverse _).2 inferInstance⟩,
    Nat.zero_lt_succ 0⟩

/-- Every complete original degree-one latching object is one of the two original cofaces. -/
theorem latchingOne_cases (a : SimplexCategory.reedy.Latching ⦋1⦌) :
    ∃ i : Fin 2, a = latchingOneVertex i := by
  change ∃ i : Fin 2,
    SimplexCategory.reedy.latchingOfCode ⦋1⦌
      (SimplexCategory.reedy.latchingCode ⦋1⦌ a) = latchingOneVertex i
  generalize SimplexCategory.reedy.latchingCode ⦋1⦌ a = c
  rcases c with ⟨⟨k, hk⟩, f, hf⟩
  have hk0 : k = ⦋0⦌ := SimplexCategory.ext (Nat.lt_one_iff.mp hk)
  subst k
  let _ : Mono f := hf
  obtain ⟨i, hi⟩ := SimplexCategory.eq_δ_of_mono f
  subst f
  exact ⟨i, rfl⟩

/-- Every complete original degree-one matching object is one of the two original opposite cofaces.
-/
theorem matchingOne_cases (a : SimplexCategory.reedyOp.Matching (Opposite.op ⦋1⦌)) :
    ∃ i : Fin 2, a = matchingOneVertex i := by
  change ∃ i : Fin 2,
    SimplexCategory.reedyOp.matchingOfCode (Opposite.op ⦋1⦌)
      (SimplexCategory.reedyOp.matchingCode (Opposite.op ⦋1⦌) a) = matchingOneVertex i
  generalize SimplexCategory.reedyOp.matchingCode (Opposite.op ⦋1⦌) a = c
  rcases c with ⟨⟨k, hk⟩, f, hf⟩
  have hk0 : k = Opposite.op ⦋0⦌ :=
    Opposite.unop_injective (SimplexCategory.ext (Nat.lt_one_iff.mp hk))
  subst k
  let _ : Mono f.unop := hf
  obtain ⟨i, hi⟩ := SimplexCategory.eq_δ_of_mono f.unop
  have hfo : f = (SimplexCategory.δ i).op := Quiver.Hom.unop_inj hi
  subst f
  exact ⟨i, rfl⟩

/-- Each original latching comparison between the two vertices is the original zero identity. -/
theorem latchingOne_comparison {i j : Fin 2}
    (f : latchingOneVertex i ⟶ latchingOneVertex j) :
    SimplexCategory.reedy.latchingComparison f = 𝟙 ⦋0⦌ :=
  SimplexCategory.hom_zero_zero _

/-- Each original matching comparison between the two vertices is the original opposite zero
identity. -/
theorem matchingOne_comparison {i j : Fin 2}
    (f : matchingOneVertex i ⟶ matchingOneVertex j) :
    SimplexCategory.reedyOp.matchingComparison f = 𝟙 (Opposite.op ⦋0⦌) :=
  Quiver.Hom.unop_inj (SimplexCategory.hom_zero_zero _)

/-- An original latching comparison can only join equal original cofaces. -/
theorem latchingOne_comparison_index {i j : Fin 2}
    (f : latchingOneVertex i ⟶ latchingOneVertex j) : i = j := by
  have h := SimplexCategory.reedy.latchingComparison_arrow f
  change SimplexCategory.reedy.latchingComparison f ≫ SimplexCategory.δ j =
    SimplexCategory.δ i at h
  rw [latchingOne_comparison] at h
  change 𝟙 ⦋0⦌ ≫ SimplexCategory.δ j = SimplexCategory.δ i at h
  rw [Category.id_comp] at h
  exact SimplexCategory.δ_injective h.symm

/-- An original matching comparison can only join equal original opposite cofaces. -/
theorem matchingOne_comparison_index {i j : Fin 2}
    (f : matchingOneVertex i ⟶ matchingOneVertex j) : i = j := by
  have h := SimplexCategory.reedyOp.matchingArrow_comparison f
  change (SimplexCategory.δ i).op ≫ SimplexCategory.reedyOp.matchingComparison f =
    (SimplexCategory.δ j).op at h
  rw [matchingOne_comparison] at h
  change (SimplexCategory.δ i).op ≫ 𝟙 (Opposite.op ⦋0⦌) = (SimplexCategory.δ j).op at h
  rw [Category.comp_id] at h
  exact SimplexCategory.δ_injective (Quiver.Hom.op_inj h)

/-- The two actual latching vertices are distinct. -/
theorem latchingOneVertex_injective : Function.Injective latchingOneVertex :=
  fun _ _ h => latchingOne_comparison_index (eqToHom h)

/-- The two actual matching vertices are distinct. -/
theorem matchingOneVertex_injective : Function.Injective matchingOneVertex :=
  fun _ _ h => matchingOne_comparison_index (eqToHom h)

/-- The coface index of each complete actual degree-one latching object. -/
def latchingOneIndex (a : SimplexCategory.reedy.Latching ⦋1⦌) : Fin 2 :=
  Classical.choose (latchingOne_cases a)

/-- Classification retains the complete actual latching object. -/
theorem latchingOne_eq (a : SimplexCategory.reedy.Latching ⦋1⦌) :
    a = latchingOneVertex (latchingOneIndex a) :=
  Classical.choose_spec (latchingOne_cases a)

/-- Indexing retains the original coface label. -/
@[simp]
theorem latchingOneIndex_vertex (i : Fin 2) :
    latchingOneIndex (latchingOneVertex i) = i :=
  (latchingOneVertex_injective (latchingOne_eq (latchingOneVertex i))).symm

/-- The coface index of each complete actual degree-one matching object. -/
def matchingOneIndex (a : SimplexCategory.reedyOp.Matching (Opposite.op ⦋1⦌)) : Fin 2 :=
  Classical.choose (matchingOne_cases a)

/-- Classification retains the complete actual matching object. -/
theorem matchingOne_eq (a : SimplexCategory.reedyOp.Matching (Opposite.op ⦋1⦌)) :
    a = matchingOneVertex (matchingOneIndex a) :=
  Classical.choose_spec (matchingOne_cases a)

/-- Indexing retains the original opposite coface label. -/
@[simp]
theorem matchingOneIndex_vertex (i : Fin 2) :
    matchingOneIndex (matchingOneVertex i) = i :=
  (matchingOneVertex_injective (matchingOne_eq (matchingOneVertex i))).symm

variable {C : Type uC} [Category.{vC} C]

section Latching

variable [HasFiniteColimits C]

/-- The actual coproduct injection attached to each original latching object. -/
def latchingOneInjection (A : CosimplicialObject C)
    (a : SimplexCategory.reedy.Latching ⦋1⦌) :
    (SimplexCategory.reedy.latchingDiagram A ⦋1⦌).obj a ⟶ A ^⦋0⦌ ⨿ A ^⦋0⦌ :=
  eqToHom (congrArg (fun b => (SimplexCategory.reedy.latchingDiagram A ⦋1⦌).obj b)
    (latchingOne_eq a)) ≫
      if latchingOneIndex a = 0 then coprod.inl else coprod.inr

/-- The first original coface receives the first original coproduct injection. -/
@[simp]
theorem latchingOneInjection_zero (A : CosimplicialObject C) :
    latchingOneInjection A (latchingOneVertex 0) =
      (coprod.inl : A ^⦋0⦌ ⟶ A ^⦋0⦌ ⨿ A ^⦋0⦌) := by
  simp only [latchingOneInjection, latchingOneIndex_vertex]
  exact Category.id_comp _

/-- The second original coface receives the second original coproduct injection. -/
@[simp]
theorem latchingOneInjection_one (A : CosimplicialObject C) :
    latchingOneInjection A (latchingOneVertex 1) =
      (coprod.inr : A ^⦋0⦌ ⟶ A ^⦋0⦌ ⨿ A ^⦋0⦌) := by
  simp only [latchingOneInjection, latchingOneIndex_vertex]
  exact Category.id_comp _

/-- Every original latching comparison gives the original coproduct cocone triangle. -/
@[reassoc]
theorem latchingOneInjection_naturality (A : CosimplicialObject C)
    {a b : SimplexCategory.reedy.Latching ⦋1⦌} (f : a ⟶ b) :
    (SimplexCategory.reedy.latchingDiagram A ⦋1⦌).map f ≫ latchingOneInjection A b =
      latchingOneInjection A a := by
  obtain ⟨i, rfl⟩ := latchingOne_cases a
  obtain ⟨j, rfl⟩ := latchingOne_cases b
  have hij := latchingOne_comparison_index f
  subst j
  change A.map (SimplexCategory.reedy.latchingComparison f) ≫ _ = _
  rw [latchingOne_comparison]
  change A.map (𝟙 ⦋0⦌) ≫ _ = _
  rw [A.map_id]
  exact Category.id_comp _

/-- The full actual latching coproduct cocone, with all original comparison triangles. -/
def latchingOneCocone (A : CosimplicialObject C) :
    Cocone (SimplexCategory.reedy.latchingDiagram A ⦋1⦌) where
  pt := A ^⦋0⦌ ⨿ A ^⦋0⦌
  ι.app := latchingOneInjection A
  ι.naturality _ _ f :=
    (latchingOneInjection_naturality A f).trans (Category.comp_id _).symm

/-- The complete degree-one latching coproduct cocone is a colimit. -/
def latchingOneIsColimit (A : CosimplicialObject C) : IsColimit (latchingOneCocone A) where
  desc s := coprod.desc (s.ι.app (latchingOneVertex 0)) (s.ι.app (latchingOneVertex 1))
  fac s a := by
    obtain ⟨i, rfl⟩ := latchingOne_cases a
    fin_cases i
    · change latchingOneInjection A (latchingOneVertex 0) ≫ _ = _
      rw [latchingOneInjection_zero]
      exact coprod.inl_desc _ _
    · change latchingOneInjection A (latchingOneVertex 1) ≫ _ = _
      rw [latchingOneInjection_one]
      exact coprod.inr_desc _ _
  uniq s m hm := by
    apply coprod.hom_ext
    · have h0 : coprod.inl ≫ m = s.ι.app (latchingOneVertex 0) := by
        simpa only [latchingOneCocone, latchingOneInjection_zero] using hm (latchingOneVertex 0)
      exact h0.trans (coprod.inl_desc _ _).symm
    · have h1 : coprod.inr ≫ m = s.ι.app (latchingOneVertex 1) := by
        simpa only [latchingOneCocone, latchingOneInjection_one] using hm (latchingOneVertex 1)
      exact h1.trans (coprod.inr_desc _ _).symm

/-- The actual degree-one cosimplicial latching colimit is the original binary coproduct. -/
def cosimplicialLatchingOneIso (A : CosimplicialObject C) :
    colimit (SimplexCategory.reedy.latchingDiagram A ⦋1⦌) ≅ A ^⦋0⦌ ⨿ A ^⦋0⦌ :=
  (colimit.isColimit _).coconePointUniqueUpToIso (latchingOneIsColimit A)

/-- The boundary isomorphism retains every original latching injection. -/
@[reassoc]
theorem cosimplicialLatchingOneIso_ι (A : CosimplicialObject C)
    (a : SimplexCategory.reedy.Latching ⦋1⦌) :
    colimit.ι (SimplexCategory.reedy.latchingDiagram A ⦋1⦌) a ≫
        (cosimplicialLatchingOneIso A).hom = latchingOneInjection A a :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ a

/-- The inverse boundary isomorphism retains every original latching injection. -/
@[reassoc]
theorem cosimplicialLatchingOneIso_inv_ι (A : CosimplicialObject C)
    (a : SimplexCategory.reedy.Latching ⦋1⦌) :
    latchingOneInjection A a ≫ (cosimplicialLatchingOneIso A).inv =
      colimit.ι (SimplexCategory.reedy.latchingDiagram A ⦋1⦌) a :=
  IsColimit.comp_coconePointUniqueUpToIso_inv (colimit.isColimit _) (latchingOneIsColimit A) a

/-- The first original latching injection is exactly the first coproduct injection. -/
@[reassoc]
theorem cosimplicialLatchingOneIso_ι_zero (A : CosimplicialObject C) :
    colimit.ι (SimplexCategory.reedy.latchingDiagram A ⦋1⦌) (latchingOneVertex 0) ≫
        (cosimplicialLatchingOneIso A).hom =
      (coprod.inl : A ^⦋0⦌ ⟶ A ^⦋0⦌ ⨿ A ^⦋0⦌) :=
  (cosimplicialLatchingOneIso_ι A (latchingOneVertex 0)).trans (latchingOneInjection_zero A)

/-- The second original latching injection is exactly the second coproduct injection. -/
@[reassoc]
theorem cosimplicialLatchingOneIso_ι_one (A : CosimplicialObject C) :
    colimit.ι (SimplexCategory.reedy.latchingDiagram A ⦋1⦌) (latchingOneVertex 1) ≫
        (cosimplicialLatchingOneIso A).hom =
      (coprod.inr : A ^⦋0⦌ ⟶ A ^⦋0⦌ ⨿ A ^⦋0⦌) :=
  (cosimplicialLatchingOneIso_ι A (latchingOneVertex 1)).trans (latchingOneInjection_one A)

/-- The first coproduct injection returns the first original latching injection. -/
@[reassoc]
theorem cosimplicialLatchingOneIso_inl_inv (A : CosimplicialObject C) :
    coprod.inl ≫ (cosimplicialLatchingOneIso A).inv =
      colimit.ι (SimplexCategory.reedy.latchingDiagram A ⦋1⦌) (latchingOneVertex 0) := by
  simpa only [latchingOneInjection_zero] using cosimplicialLatchingOneIso_inv_ι A
    (latchingOneVertex 0)

/-- The second coproduct injection returns the second original latching injection. -/
@[reassoc]
theorem cosimplicialLatchingOneIso_inr_inv (A : CosimplicialObject C) :
    coprod.inr ≫ (cosimplicialLatchingOneIso A).inv =
      colimit.ι (SimplexCategory.reedy.latchingDiagram A ⦋1⦌) (latchingOneVertex 1) := by
  simpa only [latchingOneInjection_one] using cosimplicialLatchingOneIso_inv_ι A
    (latchingOneVertex 1)

/-- The actual degree-one latching map is the original ordered coface copairing. -/
@[reassoc]
theorem cosimplicialLatchingOneIso_inv_map (A : CosimplicialObject C) :
    (cosimplicialLatchingOneIso A).inv ≫ SimplexCategory.reedy.latchingMap A ⦋1⦌ =
      coprod.desc (A.δ 0) (A.δ 1) := by
  apply coprod.hom_ext
  · rw [← Category.assoc, cosimplicialLatchingOneIso_inl_inv, SimplexCategory.reedy.latchingMap_ι]
    exact (coprod.inl_desc _ _).symm
  · rw [← Category.assoc, cosimplicialLatchingOneIso_inr_inv, SimplexCategory.reedy.latchingMap_ι]
    exact (coprod.inr_desc _ _).symm

/-- Every original coefficient map commutes with every original latching injection. -/
@[reassoc]
theorem latchingOneInjection_coefficient {A A' : CosimplicialObject C} (f : A ⟶ A')
    (a : SimplexCategory.reedy.Latching ⦋1⦌) :
    f.app (SimplexCategory.reedy.latchingSource a) ≫ latchingOneInjection A' a =
      latchingOneInjection A a ≫ coprod.map (f.app ⦋0⦌) (f.app ⦋0⦌) := by
  obtain ⟨i, rfl⟩ := latchingOne_cases a
  fin_cases i
  · change f.app ⦋0⦌ ≫ latchingOneInjection A' (latchingOneVertex 0) =
      latchingOneInjection A (latchingOneVertex 0) ≫ _
    rw [latchingOneInjection_zero, latchingOneInjection_zero]
    exact (coprod.inl_map _ _).symm
  · change f.app ⦋0⦌ ≫ latchingOneInjection A' (latchingOneVertex 1) =
      latchingOneInjection A (latchingOneVertex 1) ≫ _
    rw [latchingOneInjection_one, latchingOneInjection_one]
    exact (coprod.inr_map _ _).symm

/-- The whole degree-one latching isomorphism is natural in every original cosimplicial map. -/
@[reassoc]
theorem cosimplicialLatchingOneIso_naturality {A A' : CosimplicialObject C} (f : A ⟶ A') :
    colimMap (SimplexCategory.reedy.latchingTransformation f ⦋1⦌) ≫
        (cosimplicialLatchingOneIso A').hom =
      (cosimplicialLatchingOneIso A).hom ≫ coprod.map (f.app ⦋0⦌) (f.app ⦋0⦌) := by
  apply colimit.hom_ext
  intro a
  rw [← Category.assoc, ι_colimMap, Category.assoc, cosimplicialLatchingOneIso_ι,
    ← Category.assoc, cosimplicialLatchingOneIso_ι]
  exact latchingOneInjection_coefficient f a

/-- The actual degree-one latching boundary functor. -/
abbrev cosimplicialLatchingOneFunctor : CosimplicialObject C ⥤ C :=
  (Functor.whiskeringLeft (SimplexCategory.reedy.Latching ⦋1⦌) SimplexCategory C).obj
    (SimplexCategory.reedy.latchingInclusion ⦋1⦌) ⋙ colim

/-- The original ordered binary coproduct of the degree-zero coefficient, as a functor. -/
def cosimplicialZeroCoprodFunctor : CosimplicialObject C ⥤ C where
  obj A := A ^⦋0⦌ ⨿ A ^⦋0⦌
  map f := coprod.map (f.app ⦋0⦌) (f.app ⦋0⦌)
  map_id A := by
    change coprod.map (𝟙 (A ^⦋0⦌)) (𝟙 (A ^⦋0⦌)) = 𝟙 _
    exact coprod.map_id_id
  map_comp f g := (coprod.map_map _ _ _ _).symm

/-- A genuine natural isomorphism of the complete actual degree-one boundary functors. -/
def cosimplicialLatchingOneNatIso :
    cosimplicialLatchingOneFunctor (C := C) ≅ cosimplicialZeroCoprodFunctor (C := C) :=
  NatIso.ofComponents cosimplicialLatchingOneIso (fun f => cosimplicialLatchingOneIso_naturality f)

/-- The inverse degree-one boundary comparison is natural in every original cosimplicial map. -/
@[reassoc]
theorem cosimplicialLatchingOneIso_inv_naturality {A A' : CosimplicialObject C} (f : A ⟶ A') :
    coprod.map (f.app ⦋0⦌) (f.app ⦋0⦌) ≫ (cosimplicialLatchingOneIso A').inv =
      (cosimplicialLatchingOneIso A).inv ≫
        colimMap (SimplexCategory.reedy.latchingTransformation f ⦋1⦌) :=
  cosimplicialLatchingOneNatIso.inv.naturality f

end Latching

section Matching

variable [HasFiniteLimits C]

/-- The actual product projection attached to each original matching object. -/
def matchingOneProjection (B : SimplicialObject C)
    (a : SimplexCategory.reedyOp.Matching (Opposite.op ⦋1⦌)) :
    B _⦋0⦌ ⨯ B _⦋0⦌ ⟶
      (SimplexCategory.reedyOp.matchingDiagram B (Opposite.op ⦋1⦌)).obj a :=
  (if matchingOneIndex a = 0 then prod.fst else prod.snd) ≫
    eqToHom (congrArg (fun b =>
      (SimplexCategory.reedyOp.matchingDiagram B (Opposite.op ⦋1⦌)).obj b)
      (matchingOne_eq a).symm)

/-- The first original opposite coface receives the first original product projection. -/
@[simp]
theorem matchingOneProjection_zero (B : SimplicialObject C) :
    matchingOneProjection B (matchingOneVertex 0) =
      (prod.fst : B _⦋0⦌ ⨯ B _⦋0⦌ ⟶ B _⦋0⦌) := by
  simp [matchingOneProjection, matchingOneVertex]

/-- The second original opposite coface receives the second original product projection. -/
@[simp]
theorem matchingOneProjection_one (B : SimplicialObject C) :
    matchingOneProjection B (matchingOneVertex 1) =
      (prod.snd : B _⦋0⦌ ⨯ B _⦋0⦌ ⟶ B _⦋0⦌) := by
  simp [matchingOneProjection, matchingOneVertex]

/-- Every original matching comparison gives the original product cone triangle. -/
@[reassoc]
theorem matchingOneProjection_naturality (B : SimplicialObject C)
    {a b : SimplexCategory.reedyOp.Matching (Opposite.op ⦋1⦌)} (f : a ⟶ b) :
    matchingOneProjection B a ≫
        (SimplexCategory.reedyOp.matchingDiagram B (Opposite.op ⦋1⦌)).map f =
      matchingOneProjection B b := by
  obtain ⟨i, rfl⟩ := matchingOne_cases a
  obtain ⟨j, rfl⟩ := matchingOne_cases b
  have hij := matchingOne_comparison_index f
  subst j
  change _ ≫ B.map (SimplexCategory.reedyOp.matchingComparison f) = _
  rw [matchingOne_comparison]
  change _ ≫ B.map (𝟙 (Opposite.op ⦋0⦌)) = _
  rw [B.map_id]
  exact Category.comp_id _

/-- The full actual matching product cone, with all original comparison triangles. -/
def matchingOneCone (B : SimplicialObject C) :
    Cone (SimplexCategory.reedyOp.matchingDiagram B (Opposite.op ⦋1⦌)) where
  pt := B _⦋0⦌ ⨯ B _⦋0⦌
  π.app := matchingOneProjection B
  π.naturality _ _ f :=
    (Category.id_comp _).trans (matchingOneProjection_naturality B f).symm

/-- The complete degree-one matching product cone is a limit. -/
def matchingOneIsLimit (B : SimplicialObject C) : IsLimit (matchingOneCone B) where
  lift s := prod.lift (s.π.app (matchingOneVertex 0)) (s.π.app (matchingOneVertex 1))
  fac s a := by
    obtain ⟨i, rfl⟩ := matchingOne_cases a
    fin_cases i
    · change _ ≫ matchingOneProjection B (matchingOneVertex 0) = _
      rw [matchingOneProjection_zero]
      exact prod.lift_fst _ _
    · change _ ≫ matchingOneProjection B (matchingOneVertex 1) = _
      rw [matchingOneProjection_one]
      exact prod.lift_snd _ _
  uniq s m hm := by
    apply prod.hom_ext
    · have h0 : m ≫ prod.fst = s.π.app (matchingOneVertex 0) := by
        simpa only [matchingOneCone, matchingOneProjection_zero] using hm (matchingOneVertex 0)
      exact h0.trans (prod.lift_fst _ _).symm
    · have h1 : m ≫ prod.snd = s.π.app (matchingOneVertex 1) := by
        simpa only [matchingOneCone, matchingOneProjection_one] using hm (matchingOneVertex 1)
      exact h1.trans (prod.lift_snd _ _).symm

/-- The actual degree-one simplicial matching limit is the original binary product. -/
def simplicialMatchingOneIso (B : SimplicialObject C) :
    limit (SimplexCategory.reedyOp.matchingDiagram B (Opposite.op ⦋1⦌)) ≅ B _⦋0⦌ ⨯ B _⦋0⦌ :=
  (limit.isLimit _).conePointUniqueUpToIso (matchingOneIsLimit B)

/-- The boundary isomorphism retains every original matching projection. -/
@[reassoc]
theorem simplicialMatchingOneIso_π (B : SimplicialObject C)
    (a : SimplexCategory.reedyOp.Matching (Opposite.op ⦋1⦌)) :
    (simplicialMatchingOneIso B).hom ≫ matchingOneProjection B a =
      limit.π (SimplexCategory.reedyOp.matchingDiagram B (Opposite.op ⦋1⦌)) a :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ a

/-- The inverse boundary isomorphism retains every original matching projection. -/
@[reassoc]
theorem simplicialMatchingOneIso_inv_π (B : SimplicialObject C)
    (a : SimplexCategory.reedyOp.Matching (Opposite.op ⦋1⦌)) :
    (simplicialMatchingOneIso B).inv ≫
        limit.π (SimplexCategory.reedyOp.matchingDiagram B (Opposite.op ⦋1⦌)) a =
      matchingOneProjection B a :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ a

/-- The first product projection is exactly the first original matching projection. -/
@[reassoc]
theorem simplicialMatchingOneIso_hom_fst (B : SimplicialObject C) :
    (simplicialMatchingOneIso B).hom ≫ prod.fst =
      limit.π (SimplexCategory.reedyOp.matchingDiagram B (Opposite.op ⦋1⦌)) (matchingOneVertex
        0) := by
  simpa only [matchingOneProjection_zero] using simplicialMatchingOneIso_π B (matchingOneVertex 0)

/-- The second product projection is exactly the second original matching projection. -/
@[reassoc]
theorem simplicialMatchingOneIso_hom_snd (B : SimplicialObject C) :
    (simplicialMatchingOneIso B).hom ≫ prod.snd =
      limit.π (SimplexCategory.reedyOp.matchingDiagram B (Opposite.op ⦋1⦌)) (matchingOneVertex
        1) := by
  simpa only [matchingOneProjection_one] using simplicialMatchingOneIso_π B (matchingOneVertex 1)

/-- The first original matching projection returns the first product projection. -/
@[reassoc]
theorem simplicialMatchingOneIso_inv_π_zero (B : SimplicialObject C) :
    (simplicialMatchingOneIso B).inv ≫
        limit.π (SimplexCategory.reedyOp.matchingDiagram B (Opposite.op ⦋1⦌)) (matchingOneVertex
          0) =
      prod.fst := by
  simpa only [matchingOneProjection_zero] using simplicialMatchingOneIso_inv_π B
    (matchingOneVertex 0)

/-- The second original matching projection returns the second product projection. -/
@[reassoc]
theorem simplicialMatchingOneIso_inv_π_one (B : SimplicialObject C) :
    (simplicialMatchingOneIso B).inv ≫
        limit.π (SimplexCategory.reedyOp.matchingDiagram B (Opposite.op ⦋1⦌)) (matchingOneVertex
          1) =
      prod.snd := by
  simpa only [matchingOneProjection_one] using simplicialMatchingOneIso_inv_π B
    (matchingOneVertex 1)

/-- The actual degree-one matching map is the original ordered face pairing. -/
@[reassoc]
theorem simplicialMatchingOneIso_map_hom (B : SimplicialObject C) :
    SimplexCategory.reedyOp.matchingMap B (Opposite.op ⦋1⦌) ≫ (simplicialMatchingOneIso B).hom =
      prod.lift (B.δ 0) (B.δ 1) := by
  apply prod.hom_ext
  · rw [Category.assoc, simplicialMatchingOneIso_hom_fst, SimplexCategory.reedyOp.matchingMap_π]
    exact (prod.lift_fst _ _).symm
  · rw [Category.assoc, simplicialMatchingOneIso_hom_snd, SimplexCategory.reedyOp.matchingMap_π]
    exact (prod.lift_snd _ _).symm

/-- Every original coefficient map commutes with every original matching projection. -/
@[reassoc]
theorem matchingOneProjection_coefficient {B B' : SimplicialObject C} (f : B ⟶ B')
    (a : SimplexCategory.reedyOp.Matching (Opposite.op ⦋1⦌)) :
    matchingOneProjection B a ≫ f.app (SimplexCategory.reedyOp.matchingTarget a) =
      prod.map (f.app (Opposite.op ⦋0⦌)) (f.app (Opposite.op ⦋0⦌)) ≫ matchingOneProjection B'
        a := by
  obtain ⟨i, rfl⟩ := matchingOne_cases a
  fin_cases i
  · change matchingOneProjection B (matchingOneVertex 0) ≫ f.app (Opposite.op ⦋0⦌) =
      _ ≫ matchingOneProjection B' (matchingOneVertex 0)
    rw [matchingOneProjection_zero, matchingOneProjection_zero]
    exact (prod.map_fst _ _).symm
  · change matchingOneProjection B (matchingOneVertex 1) ≫ f.app (Opposite.op ⦋0⦌) =
      _ ≫ matchingOneProjection B' (matchingOneVertex 1)
    rw [matchingOneProjection_one, matchingOneProjection_one]
    exact (prod.map_snd _ _).symm

/-- The whole degree-one matching isomorphism is natural in every original simplicial map. -/
@[reassoc]
theorem simplicialMatchingOneIso_naturality {B B' : SimplicialObject C} (f : B ⟶ B') :
    limMap (SimplexCategory.reedyOp.matchingTransformation f (Opposite.op ⦋1⦌)) ≫
        (simplicialMatchingOneIso B').hom =
      (simplicialMatchingOneIso B).hom ≫
        prod.map (f.app (Opposite.op ⦋0⦌)) (f.app (Opposite.op ⦋0⦌)) := by
  apply prod.hom_ext
  · rw [Category.assoc, simplicialMatchingOneIso_hom_fst, limMap_π,
      Category.assoc, prod.map_fst, ← Category.assoc, simplicialMatchingOneIso_hom_fst]
    rfl
  · rw [Category.assoc, simplicialMatchingOneIso_hom_snd, limMap_π,
      Category.assoc, prod.map_snd, ← Category.assoc, simplicialMatchingOneIso_hom_snd]
    rfl

/-- The actual degree-one matching boundary functor. -/
abbrev simplicialMatchingOneFunctor : SimplicialObject C ⥤ C :=
  (Functor.whiskeringLeft (SimplexCategory.reedyOp.Matching (Opposite.op ⦋1⦌)) SimplexCategoryᵒᵖ
    C).obj
    (SimplexCategory.reedyOp.matchingInclusion (Opposite.op ⦋1⦌)) ⋙ lim

/-- The original ordered binary product of the degree-zero coefficient, as a functor. -/
def simplicialZeroProdFunctor : SimplicialObject C ⥤ C where
  obj B := B _⦋0⦌ ⨯ B _⦋0⦌
  map f := prod.map (f.app (Opposite.op ⦋0⦌)) (f.app (Opposite.op ⦋0⦌))
  map_id B := by
    change prod.map (𝟙 (B _⦋0⦌)) (𝟙 (B _⦋0⦌)) = 𝟙 _
    exact prod.map_id_id
  map_comp f g := (prod.map_map _ _ _ _).symm

/-- A genuine natural isomorphism of the complete actual degree-one boundary functors. -/
def simplicialMatchingOneNatIso :
    simplicialMatchingOneFunctor (C := C) ≅ simplicialZeroProdFunctor (C := C) :=
  NatIso.ofComponents simplicialMatchingOneIso (fun f => simplicialMatchingOneIso_naturality f)

/-- The inverse degree-one boundary comparison is natural in every original simplicial map. -/
@[reassoc]
theorem simplicialMatchingOneIso_inv_naturality {B B' : SimplicialObject C} (f : B ⟶ B') :
    prod.map (f.app (Opposite.op ⦋0⦌)) (f.app (Opposite.op ⦋0⦌)) ≫
        (simplicialMatchingOneIso B').inv =
      (simplicialMatchingOneIso B).inv ≫
        limMap (SimplexCategory.reedyOp.matchingTransformation f (Opposite.op ⦋1⦌)) :=
  simplicialMatchingOneNatIso.inv.naturality f

end Matching

end HomotopicalAlgebra.FramingDegreeOneBoundaries

end
end
end


section

/-
Copyright (c) 2026 Toskua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Toskua
-/


/-!
# Components of left resolution Hom complexes

The degree-zero identification and the actual degree-one cosimplicial maps construct a
precylinder. The endpoint inclusions here are respectively the cofaces `δ 0` and `δ 1`.
Consequently, an edge from `f` to `g` in the left Hom complex is a homotopy through this
same precylinder from `e.hom ≫ g` to `e.hom ≫ f`. This orientation is kept explicitly.

When the original cylinder retraction is weak and the original coproduct inclusion is a
cofibration, the model-category homotopy theorem identifies this same edge relation with
left homotopy. Connected components are then identified with the original localization Hom
sets for a cofibrant source and fibrant target. No component equivalence is an input.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v v' u u'

open CategoryTheory Limits Opposite
open scoped Simplicial

namespace HomotopicalAlgebra.ResolutionHomComplex.LeftPiZero

variable {C : Type u} [Category.{v} C]

/-- Each face in the left complex is the corresponding original cosimplicial coface. -/
@[simp]
theorem left_face_apply (A : CosimplicialObject C) (Y : C) {n : ℕ}
    (i : Fin (n + 2)) (h : A.obj ⦋n + 1⦌ ⟶ Y) :
    (left A Y).δ i h = A.δ i ≫ h :=
  left_map_apply A Y (SimplexCategory.δ i).op h

/-- The actual first two cosimplicial degrees construct a precylinder on the given source. -/
def precylinder (A : CosimplicialObject C) {X : C} (e : X ≅ A.obj ⦋0⦌) :
    Precylinder X where
  I := A.obj ⦋1⦌
  i₀ := e.hom ≫ A.δ (0 : Fin 2)
  i₁ := e.hom ≫ A.δ (1 : Fin 2)
  π := A.σ (0 : Fin 1) ≫ e.inv
  i₀_π := by
    calc
      (e.hom ≫ A.δ (0 : Fin 2)) ≫ (A.σ (0 : Fin 1) ≫ e.inv) =
          e.hom ≫ (A.δ (0 : Fin 2) ≫ A.σ (0 : Fin 1)) ≫ e.inv := by
        simp only [Category.assoc]
      _ = e.hom ≫ 𝟙 (A.obj ⦋0⦌) ≫ e.inv :=
        congrArg (fun k ↦ e.hom ≫ k ≫ e.inv) (A.δ_comp_σ_self (i := 0))
      _ = 𝟙 X := by simp
  i₁_π := by
    calc
      (e.hom ≫ A.δ (1 : Fin 2)) ≫ (A.σ (0 : Fin 1) ≫ e.inv) =
          e.hom ≫ (A.δ (1 : Fin 2) ≫ A.σ (0 : Fin 1)) ≫ e.inv := by
        simp only [Category.assoc]
      _ = e.hom ≫ 𝟙 (A.obj ⦋0⦌) ≫ e.inv :=
        congrArg (fun k ↦ e.hom ≫ k ≫ e.inv) (A.δ_comp_σ_succ (i := 0))
      _ = 𝟙 X := by simp

/-- The cylinder carrier is the actual first cosimplicial degree. -/
theorem precylinder_I (A : CosimplicialObject C) {X : C} (e : X ≅ A.obj ⦋0⦌) :
    (precylinder A e).I = A.obj ⦋1⦌ := rfl

/-- The first inclusion is the original degree-zero identification followed by coface zero. -/
theorem precylinder_i₀ (A : CosimplicialObject C) {X : C} (e : X ≅ A.obj ⦋0⦌) :
    (precylinder A e).i₀ = e.hom ≫ A.δ (0 : Fin 2) := rfl

/-- The second inclusion is the original degree-zero identification followed by coface one. -/
theorem precylinder_i₁ (A : CosimplicialObject C) {X : C} (e : X ≅ A.obj ⦋0⦌) :
    (precylinder A e).i₁ = e.hom ≫ A.δ (1 : Fin 2) := rfl

/-- The retraction is the original codegeneracy followed by the inverse identification. -/
theorem precylinder_π (A : CosimplicialObject C) {X : C} (e : X ≅ A.obj ⦋0⦌) :
    (precylinder A e).π = A.σ (0 : Fin 1) ≫ e.inv := rfl

/-- An actual edge gives a homotopy through the same cylinder, with its endpoint order retained. -/
def edgeToLeftHomotopy (A : CosimplicialObject C) {X : C} (e : X ≅ A.obj ⦋0⦌)
    {Y : C} {f g : A.obj ⦋0⦌ ⟶ Y} (d : (left A Y).Edge f g) :
    (precylinder A e).LeftHomotopy (e.hom ≫ g) (e.hom ≫ f) where
  h := d.edge
  h₀ := by
    have ht : A.δ (0 : Fin 2) ≫ (d.edge : A.obj ⦋1⦌ ⟶ Y) = g := by
      exact (left_face_apply A Y (0 : Fin 2) d.edge).symm.trans d.tgt_eq
    change (e.hom ≫ A.δ (0 : Fin 2)) ≫ d.edge = e.hom ≫ g
    exact (Category.assoc _ _ _).trans (congrArg (fun k ↦ e.hom ≫ k) ht)
  h₁ := by
    have hs : A.δ (1 : Fin 2) ≫ (d.edge : A.obj ⦋1⦌ ⟶ Y) = f := by
      exact (left_face_apply A Y (1 : Fin 2) d.edge).symm.trans d.src_eq
    change (e.hom ≫ A.δ (1 : Fin 2)) ≫ d.edge = e.hom ≫ f
    exact (Category.assoc _ _ _).trans (congrArg (fun k ↦ e.hom ≫ k) hs)

/-- A homotopy through the original degree-one cylinder gives its actual simplicial edge. -/
def leftHomotopyToEdge (A : CosimplicialObject C) {X : C} (e : X ≅ A.obj ⦋0⦌)
    {Y : C} {f g : X ⟶ Y} (h : (precylinder A e).LeftHomotopy f g) :
    (left A Y).Edge (e.inv ≫ g) (e.inv ≫ f) :=
  SSet.Edge.mk h.h
    (by
      refine (left_face_apply A Y (1 : Fin 2) h.h).trans ?_
      apply (cancel_epi e.hom).1
      calc
        e.hom ≫ (A.δ (1 : Fin 2) ≫ h.h) = (e.hom ≫ A.δ (1 : Fin 2)) ≫ h.h :=
          (Category.assoc _ _ _).symm
        _ = g := h.h₁
        _ = e.hom ≫ (e.inv ≫ g) := (e.hom_inv_id_assoc g).symm)
    (by
      refine (left_face_apply A Y (0 : Fin 2) h.h).trans ?_
      apply (cancel_epi e.hom).1
      calc
        e.hom ≫ (A.δ (0 : Fin 2) ≫ h.h) = (e.hom ≫ A.δ (0 : Fin 2)) ≫ h.h :=
          (Category.assoc _ _ _).symm
        _ = f := h.h₀
        _ = e.hom ≫ (e.inv ≫ f) := (e.hom_inv_id_assoc f).symm)

/-- The conversion from edges retains the entire original degree-one map. -/
theorem edgeToLeftHomotopy_h (A : CosimplicialObject C) {X : C}
    (e : X ≅ A.obj ⦋0⦌) {Y : C} {f g : A.obj ⦋0⦌ ⟶ Y} (d : (left A Y).Edge f g) :
    (edgeToLeftHomotopy A e d).h = d.edge := rfl

/-- The conversion to edges retains the entire original cylinder homotopy map. -/
theorem leftHomotopyToEdge_edge (A : CosimplicialObject C) {X : C}
    (e : X ≅ A.obj ⦋0⦌) {Y : C} {f g : X ⟶ Y}
    (h : (precylinder A e).LeftHomotopy f g) :
    (leftHomotopyToEdge A e h).edge = h.h := rfl

/-- The actual edge relation is exactly homotopy through the same degree-one precylinder. -/
theorem edge_iff_leftHomotopy (A : CosimplicialObject C) {X : C}
    (e : X ≅ A.obj ⦋0⦌) {Y : C} (f g : A.obj ⦋0⦌ ⟶ Y) :
    Nonempty ((left A Y).Edge f g) ↔
      Nonempty ((precylinder A e).LeftHomotopy (e.hom ≫ g) (e.hom ≫ f)) := by
  constructor
  · rintro ⟨d⟩
    exact ⟨edgeToLeftHomotopy A e d⟩
  · rintro ⟨h⟩
    exact ⟨(leftHomotopyToEdge A e h).ofEq
      (e.inv_hom_id_assoc f) (e.inv_hom_id_assoc g)⟩

section WithWeakEquivalences

variable [CategoryWithWeakEquivalences C]

/-- The original weak codegeneracy retraction makes the degree-one precylinder a cylinder. -/
def cylinder (A : CosimplicialObject C) {X : C} (e : X ≅ A.obj ⦋0⦌)
    [WeakEquivalence (A.σ (0 : Fin 1) ≫ e.inv)] : Cylinder X where
  __ := precylinder A e
  weakEquivalence_π := by
    change WeakEquivalence (A.σ (0 : Fin 1) ≫ e.inv)
    infer_instance

/-- The cylinder keeps the original precylinder and all its actual maps. -/
theorem cylinder_toPrecylinder (A : CosimplicialObject C) {X : C}
    (e : X ≅ A.obj ⦋0⦌) [WeakEquivalence (A.σ (0 : Fin 1) ≫ e.inv)] :
    (cylinder A e).toPrecylinder = precylinder A e := rfl

/-- The original coproduct inclusion proves goodness of this same cylinder. -/
instance cylinder_isGood [CategoryWithCofibrations C] (A : CosimplicialObject C) {X : C}
    [HasBinaryCoproduct X X] (e : X ≅ A.obj ⦋0⦌)
    [WeakEquivalence (A.σ (0 : Fin 1) ≫ e.inv)]
    [Cofibration (coprod.desc (e.hom ≫ A.δ (0 : Fin 2)) (e.hom ≫ A.δ (1 : Fin 2)))] :
    (cylinder A e).IsGood where
  cofibration_i := by
    change Cofibration
      (coprod.desc (e.hom ≫ A.δ (0 : Fin 2)) (e.hom ≫ A.δ (1 : Fin 2)))
    infer_instance

/-- The original edge gives the original model-category left homotopy relation. -/
theorem edge_leftHomotopyRel (A : CosimplicialObject C) {X : C} (e : X ≅ A.obj ⦋0⦌)
    [WeakEquivalence (A.σ (0 : Fin 1) ≫ e.inv)] {Y : C} {f g : A.obj ⦋0⦌ ⟶ Y}
    (d : (left A Y).Edge f g) : LeftHomotopyRel (e.hom ≫ f) (e.hom ≫ g) := by
  let h : (cylinder A e).LeftHomotopy (e.hom ≫ g) (e.hom ≫ f) :=
    edgeToLeftHomotopy A e d
  exact h.leftHomotopyRel.symm

/-- Components of the actual left complex map to original left homotopy classes. -/
def piZeroToClass (A : CosimplicialObject C) {X : C} (e : X ≅ A.obj ⦋0⦌)
    [WeakEquivalence (A.σ (0 : Fin 1) ≫ e.inv)] (Y : C) :
    SSet.π₀ (left A Y) → LeftHomotopyClass X Y :=
  SSet.π₀.lift (fun f ↦ LeftHomotopyClass.mk (e.hom ≫ f))
    (fun _ _ d ↦ LeftHomotopyClass.sound (edge_leftHomotopyRel A e d))

/-- The component-to-class function retains the given degree-zero identification. -/
@[simp]
theorem piZeroToClass_mk (A : CosimplicialObject C) {X : C} (e : X ≅ A.obj ⦋0⦌)
    [WeakEquivalence (A.σ (0 : Fin 1) ≫ e.inv)] (Y : C) (f : A.obj ⦋0⦌ ⟶ Y) :
    piZeroToClass A e Y (SSet.π₀.mk f) = LeftHomotopyClass.mk (e.hom ≫ f) := rfl

end WithWeakEquivalences

section ModelCategory

variable [ModelCategory C] (A : CosimplicialObject C) {X : C} (e : X ≅ A.obj ⦋0⦌)
  [WeakEquivalence (A.σ (0 : Fin 1) ≫ e.inv)]
  [Cofibration (coprod.desc (e.hom ≫ A.δ (0 : Fin 2)) (e.hom ≫ A.δ (1 : Fin 2)))]
  [IsCofibrant X]

/-- Model-category homotopies are exactly the actual edges of this resolution complex. -/
theorem edge_iff_leftHomotopyRel (Y : C) [IsFibrant Y] (f g : A.obj ⦋0⦌ ⟶ Y) :
    SSet.π₀Rel (X := left A Y) f g ↔ LeftHomotopyRel (e.hom ≫ f) (e.hom ≫ g) := by
  constructor
  · rintro ⟨d⟩
    exact edge_leftHomotopyRel A e d
  · intro h
    apply (edge_iff_leftHomotopy A e f g).2
    exact ⟨h.symm.leftHomotopy (cylinder A e)⟩

/-- The inverse component function uses the original good cylinder for every homotopy. -/
def classToPiZero (Y : C) [IsFibrant Y] :
    LeftHomotopyClass X Y → SSet.π₀ (left A Y) :=
  Quot.lift (fun f ↦ SSet.π₀.mk (e.inv ≫ f)) (fun f g h ↦ by
    let H : (precylinder A e).LeftHomotopy f g := h.leftHomotopy (cylinder A e)
    exact (SSet.π₀.sound (leftHomotopyToEdge A e H)).symm)

/-- The inverse component function uses the inverse of the original identification. -/
@[simp]
theorem classToPiZero_mk (Y : C) [IsFibrant Y] (f : X ⟶ Y) :
    classToPiZero A e Y (LeftHomotopyClass.mk f) = SSet.π₀.mk (e.inv ≫ f) := rfl

/-- Components of the actual left complex are the original full left homotopy quotient. -/
def classEquiv (Y : C) [IsFibrant Y] :
    SSet.π₀ (left A Y) ≃ LeftHomotopyClass X Y where
  toFun := piZeroToClass A e Y
  invFun := classToPiZero A e Y
  left_inv q := by
    obtain ⟨f, rfl⟩ := SSet.π₀.mk_surjective q
    change A.obj ⦋0⦌ ⟶ Y at f
    change SSet.π₀.mk (X := left A Y) (e.inv ≫ (e.hom ≫ f)) = SSet.π₀.mk f
    exact congrArg (SSet.π₀.mk (X := left A Y)) (e.inv_hom_id_assoc f)
  right_inv q := by
    obtain ⟨f, rfl⟩ := LeftHomotopyClass.mk_surjective q
    change LeftHomotopyClass.mk (e.hom ≫ (e.inv ≫ f)) = LeftHomotopyClass.mk f
    exact congrArg LeftHomotopyClass.mk (e.hom_inv_id_assoc f)

/-- The full component equivalence keeps the original represented-map function. -/
@[simp]
theorem classEquiv_mk (Y : C) [IsFibrant Y] (f : A.obj ⦋0⦌ ⟶ Y) :
    classEquiv A e Y (SSet.π₀.mk f) = LeftHomotopyClass.mk (e.hom ≫ f) := rfl

/-- The full inverse equivalence keeps the original inverse represented-map function. -/
@[simp]
theorem classEquiv_symm_mk (Y : C) [IsFibrant Y] (f : X ⟶ Y) :
    (classEquiv A e Y).symm (LeftHomotopyClass.mk f) = SSet.π₀.mk (e.inv ≫ f) := rfl

/-- Equality of components is precisely original left homotopy on the identified source. -/
theorem piZero_mk_eq_mk_iff (Y : C) [IsFibrant Y] (f g : A.obj ⦋0⦌ ⟶ Y) :
    SSet.π₀.mk (X := left A Y) f = SSet.π₀.mk g ↔
      LeftHomotopyRel (e.hom ≫ f) (e.hom ≫ g) := by
  constructor
  · intro h
    apply (LeftHomotopyClass.mk_eq_mk_iff _ _).1
    exact congrArg (classEquiv A e Y) h
  · intro h
    apply (classEquiv A e Y).injective
    exact LeftHomotopyClass.sound h

variable {H : Type u'} [Category.{v'} H] (L : C ⥤ H)
  [L.IsLocalization (weakEquivalences C)]

/-- The fundamental lemma identifies the components with the original localization Hom sets. -/
def piZeroEquiv (Y : C) [IsFibrant Y] :
    SSet.π₀ (left A Y) ≃ (L.obj X ⟶ L.obj Y) :=
  (classEquiv A e Y).trans
    (Equiv.ofBijective (leftHomotopyClassToHom L)
      (bijective_leftHomotopyClassToHom L X Y))

/-- The component equivalence sends a represented map to its unchanged localization image. -/
@[simp]
theorem piZeroEquiv_mk (Y : C) [IsFibrant Y] (f : A.obj ⦋0⦌ ⟶ Y) :
    piZeroEquiv A e L Y (SSet.π₀.mk f) = L.map (e.hom ≫ f) :=
  leftHomotopyClassToHom_mk L (e.hom ≫ f)

/-- The inverse Hom function uses the inverse of the same degree-zero identification. -/
@[simp]
theorem piZeroEquiv_symm_map (Y : C) [IsFibrant Y] (f : X ⟶ Y) :
    (piZeroEquiv A e L Y).symm (L.map f) = SSet.π₀.mk (e.inv ≫ f) := by
  apply (piZeroEquiv A e L Y).injective
  rw [Equiv.apply_symm_apply, piZeroEquiv_mk, e.hom_inv_id_assoc]

/-- The entire component Hom function is natural in every original fibrant-target map. -/
theorem piZeroEquiv_naturality_target {Y Y' : C} [IsFibrant Y] [IsFibrant Y']
    (g : Y ⟶ Y') (q : SSet.π₀ (left A Y)) :
    piZeroEquiv A e L Y'
        (SSet.mapπ₀ (postcomp A ((SimplicialObject.const C).map g)) q) =
      piZeroEquiv A e L Y q ≫ L.map g := by
  obtain ⟨f, rfl⟩ := SSet.π₀.mk_surjective q
  let h : A.obj ⦋0⦌ ⟶ Y := f
  calc
    piZeroEquiv A e L Y'
        (SSet.mapπ₀ (postcomp A ((SimplicialObject.const C).map g)) (SSet.π₀.mk f)) =
        piZeroEquiv A e L Y' (SSet.π₀.mk (h ≫ g)) :=
      congrArg (piZeroEquiv A e L Y')
        (SSet.mapπ₀_mk (postcomp A ((SimplicialObject.const C).map g)) f)
    _ = L.map (e.hom ≫ (h ≫ g)) := piZeroEquiv_mk A e L Y' (h ≫ g)
    _ = L.map ((e.hom ≫ h) ≫ g) := L.congr_map (Category.assoc _ _ _).symm
    _ = L.map (e.hom ≫ h) ≫ L.map g := L.map_comp _ _
    _ = piZeroEquiv A e L Y (SSet.π₀.mk f) ≫ L.map g :=
      congrArg (fun k ↦ k ≫ L.map g) (piZeroEquiv_mk A e L Y h).symm

/-- The entire inverse component Hom function retains every original fibrant-target map. -/
theorem piZeroEquiv_symm_naturality_target {Y Y' : C} [IsFibrant Y] [IsFibrant Y']
    (g : Y ⟶ Y') (q : L.obj X ⟶ L.obj Y) :
    (piZeroEquiv A e L Y').symm (q ≫ L.map g) =
      SSet.mapπ₀ (postcomp A ((SimplicialObject.const C).map g))
        ((piZeroEquiv A e L Y).symm q) := by
  apply (piZeroEquiv A e L Y').injective
  rw [Equiv.apply_symm_apply, piZeroEquiv_naturality_target, Equiv.apply_symm_apply]

/-- Every original cosimplicial map preserving the given degree-zero square retains source
naturality of the whole component Hom function. -/
theorem piZeroEquiv_naturality_source {A' : CosimplicialObject C} {X' : C}
    (e' : X' ≅ A'.obj ⦋0⦌)
    [WeakEquivalence (A'.σ (0 : Fin 1) ≫ e'.inv)]
    [Cofibration (coprod.desc (e'.hom ≫ A'.δ (0 : Fin 2)) (e'.hom ≫ A'.δ (1 : Fin 2)))]
    [IsCofibrant X'] (a : A ⟶ A') (p : X ⟶ X')
    (he : e.hom ≫ a.app ⦋0⦌ = p ≫ e'.hom) (Y : C) [IsFibrant Y]
    (q : SSet.π₀ (left A' Y)) :
    piZeroEquiv A e L Y
        (SSet.mapπ₀ (precomp a ((SimplicialObject.const C).obj Y)) q) =
      L.map p ≫ piZeroEquiv A' e' L Y q := by
  obtain ⟨f, rfl⟩ := SSet.π₀.mk_surjective q
  let h : A'.obj ⦋0⦌ ⟶ Y := f
  calc
    piZeroEquiv A e L Y
        (SSet.mapπ₀ (precomp a ((SimplicialObject.const C).obj Y)) (SSet.π₀.mk f)) =
        piZeroEquiv A e L Y (SSet.π₀.mk (a.app ⦋0⦌ ≫ h)) :=
      congrArg (piZeroEquiv A e L Y)
        (SSet.mapπ₀_mk (precomp a ((SimplicialObject.const C).obj Y)) f)
    _ = L.map (e.hom ≫ (a.app ⦋0⦌ ≫ h)) := piZeroEquiv_mk A e L Y _
    _ = L.map (p ≫ (e'.hom ≫ h)) := L.congr_map (by
      calc
        e.hom ≫ (a.app ⦋0⦌ ≫ h) = (e.hom ≫ a.app ⦋0⦌) ≫ h :=
          (Category.assoc _ _ _).symm
        _ = (p ≫ e'.hom) ≫ h := congrArg (fun k ↦ k ≫ h) he
        _ = p ≫ (e'.hom ≫ h) := Category.assoc _ _ _)
    _ = L.map p ≫ L.map (e'.hom ≫ h) := L.map_comp _ _
    _ = L.map p ≫ piZeroEquiv A' e' L Y (SSet.π₀.mk f) :=
      congrArg (fun k ↦ L.map p ≫ k) (piZeroEquiv_mk A' e' L Y h).symm

/-- The entire inverse Hom function retains the same original source and cosimplicial maps. -/
theorem piZeroEquiv_symm_naturality_source {A' : CosimplicialObject C} {X' : C}
    (e' : X' ≅ A'.obj ⦋0⦌)
    [WeakEquivalence (A'.σ (0 : Fin 1) ≫ e'.inv)]
    [Cofibration (coprod.desc (e'.hom ≫ A'.δ (0 : Fin 2)) (e'.hom ≫ A'.δ (1 : Fin 2)))]
    [IsCofibrant X'] (a : A ⟶ A') (p : X ⟶ X')
    (he : e.hom ≫ a.app ⦋0⦌ = p ≫ e'.hom) (Y : C) [IsFibrant Y]
    (q : L.obj X' ⟶ L.obj Y) :
    (piZeroEquiv A e L Y).symm (L.map p ≫ q) =
      SSet.mapπ₀ (precomp a ((SimplicialObject.const C).obj Y))
        ((piZeroEquiv A' e' L Y).symm q) := by
  apply (piZeroEquiv A e L Y).injective
  rw [Equiv.apply_symm_apply, piZeroEquiv_naturality_source A e L e' a p he,
    Equiv.apply_symm_apply]

/-- The two-variable component function retains both original maps and the degree-zero square. -/
theorem piZeroEquiv_naturality {A' : CosimplicialObject C} {X' : C}
    (e' : X' ≅ A'.obj ⦋0⦌)
    [WeakEquivalence (A'.σ (0 : Fin 1) ≫ e'.inv)]
    [Cofibration (coprod.desc (e'.hom ≫ A'.δ (0 : Fin 2)) (e'.hom ≫ A'.δ (1 : Fin 2)))]
    [IsCofibrant X'] (a : A ⟶ A') (p : X ⟶ X')
    (he : e.hom ≫ a.app ⦋0⦌ = p ≫ e'.hom)
    {Y Y' : C} [IsFibrant Y] [IsFibrant Y'] (g : Y ⟶ Y')
    (q : SSet.π₀ (left A' Y)) :
    piZeroEquiv A e L Y'
        (SSet.mapπ₀ (precomp a ((SimplicialObject.const C).obj Y) ≫
          postcomp A ((SimplicialObject.const C).map g)) q) =
      L.map p ≫ piZeroEquiv A' e' L Y q ≫ L.map g := by
  rw [SSet.mapπ₀_comp_apply, piZeroEquiv_naturality_target,
    piZeroEquiv_naturality_source A e L e' a p he]
  exact Category.assoc _ _ _

/-- The complete inverse retains the same two original maps and component naturality square. -/
theorem piZeroEquiv_symm_naturality {A' : CosimplicialObject C} {X' : C}
    (e' : X' ≅ A'.obj ⦋0⦌)
    [WeakEquivalence (A'.σ (0 : Fin 1) ≫ e'.inv)]
    [Cofibration (coprod.desc (e'.hom ≫ A'.δ (0 : Fin 2)) (e'.hom ≫ A'.δ (1 : Fin 2)))]
    [IsCofibrant X'] (a : A ⟶ A') (p : X ⟶ X')
    (he : e.hom ≫ a.app ⦋0⦌ = p ≫ e'.hom)
    {Y Y' : C} [IsFibrant Y] [IsFibrant Y'] (g : Y ⟶ Y')
    (q : L.obj X' ⟶ L.obj Y) :
    (piZeroEquiv A e L Y').symm (L.map p ≫ q ≫ L.map g) =
      SSet.mapπ₀ (precomp a ((SimplicialObject.const C).obj Y) ≫
        postcomp A ((SimplicialObject.const C).map g))
        ((piZeroEquiv A' e' L Y).symm q) := by
  apply (piZeroEquiv A e L Y').injective
  rw [Equiv.apply_symm_apply, piZeroEquiv_naturality A e L e' a p he,
    Equiv.apply_symm_apply]

/-- The same component function for the original canonical homotopy-category localization. -/
def canonicalPiZeroEquiv (Y : C) [IsFibrant Y] :
    SSet.π₀ (left A Y) ≃
      (((weakEquivalences C).Q).obj X ⟶ ((weakEquivalences C).Q).obj Y) :=
  piZeroEquiv A e ((weakEquivalences C).Q) Y

/-- The canonical function keeps the original localization map of each represented morphism. -/
@[simp]
theorem canonicalPiZeroEquiv_mk (Y : C) [IsFibrant Y] (f : A.obj ⦋0⦌ ⟶ Y) :
    canonicalPiZeroEquiv A e Y (SSet.π₀.mk f) = ((weakEquivalences C).Q).map (e.hom ≫ f) :=
  piZeroEquiv_mk A e ((weakEquivalences C).Q) Y f

/-- The canonical inverse retains the actual original representative on the source. -/
@[simp]
theorem canonicalPiZeroEquiv_symm_map (Y : C) [IsFibrant Y] (f : X ⟶ Y) :
    (canonicalPiZeroEquiv A e Y).symm (((weakEquivalences C).Q).map f) =
      SSet.π₀.mk (e.inv ≫ f) := piZeroEquiv_symm_map A e ((weakEquivalences C).Q) Y f

/-- The canonical Hom function is natural in all original fibrant-target morphisms. -/
theorem canonicalPiZeroEquiv_naturality_target {Y Y' : C} [IsFibrant Y] [IsFibrant Y']
    (g : Y ⟶ Y') (q : SSet.π₀ (left A Y)) :
    canonicalPiZeroEquiv A e Y'
        (SSet.mapπ₀ (postcomp A ((SimplicialObject.const C).map g)) q) =
      canonicalPiZeroEquiv A e Y q ≫ ((weakEquivalences C).Q).map g :=
  piZeroEquiv_naturality_target A e ((weakEquivalences C).Q) g q

/-- The canonical Hom function retains every actual degree-zero source square. -/
theorem canonicalPiZeroEquiv_naturality_source {A' : CosimplicialObject C} {X' : C}
    (e' : X' ≅ A'.obj ⦋0⦌)
    [WeakEquivalence (A'.σ (0 : Fin 1) ≫ e'.inv)]
    [Cofibration (coprod.desc (e'.hom ≫ A'.δ (0 : Fin 2)) (e'.hom ≫ A'.δ (1 : Fin 2)))]
    [IsCofibrant X'] (a : A ⟶ A') (p : X ⟶ X')
    (he : e.hom ≫ a.app ⦋0⦌ = p ≫ e'.hom) (Y : C) [IsFibrant Y]
    (q : SSet.π₀ (left A' Y)) :
    canonicalPiZeroEquiv A e Y
        (SSet.mapπ₀ (precomp a ((SimplicialObject.const C).obj Y)) q) =
      ((weakEquivalences C).Q).map p ≫ canonicalPiZeroEquiv A' e' Y q :=
  piZeroEquiv_naturality_source A e ((weakEquivalences C).Q) e' a p he Y q

end ModelCategory

end HomotopicalAlgebra.ResolutionHomComplex.LeftPiZero

end
end
end

section



/-!
# Components of right resolution Hom complexes

The actual first two simplicial degrees form a path object at the same
identified target. Its weak section and its original product fibration
identify the actual edge relation with right homotopy. The resulting
component equivalence uses the original localization map on every
represented morphism. No component equivalence is supplied as input.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uC vC uH vH

open CategoryTheory Limits
open scoped Simplicial

namespace HomotopicalAlgebra.ResolutionHomComplex.RightPiZero

variable {C : Type uC} [Category.{vC} C]

/-- Every right-complex face is postcomposition by the actual original simplicial face. -/
@[simp]
theorem right_face_apply (X : C) (B : SimplicialObject C) {n : ℕ}
    (i : Fin (n + 2)) (h : X ⟶ B.obj (.op ⦋n + 1⦌)) :
    (right X B).δ i h = h ≫ B.δ i := right_map_apply X B (SimplexCategory.δ i).op h

/-- The actual first two simplicial degrees construct a prepath object on the given target. -/
def prepath (B : SimplicialObject C) {Y : C} (e : Y ≅ B.obj (.op ⦋0⦌)) :
    PrepathObject Y where
  P := B.obj (.op ⦋1⦌)
  p₀ := B.δ (0 : Fin 2) ≫ e.inv
  p₁ := B.δ (1 : Fin 2) ≫ e.inv
  ι := e.hom ≫ B.σ (0 : Fin 1)
  ι_p₀ := by
    have h : B.σ (0 : Fin 1) ≫ B.δ (0 : Fin 2) = 𝟙 (B.obj (.op ⦋0⦌)) :=
      B.δ_comp_σ_self (i := 0)
    calc
      (e.hom ≫ B.σ (0 : Fin 1)) ≫ (B.δ (0 : Fin 2) ≫ e.inv) =
          e.hom ≫ (B.σ (0 : Fin 1) ≫ B.δ (0 : Fin 2)) ≫ e.inv := by
        simp only [Category.assoc]
      _ = e.hom ≫ 𝟙 (B.obj (.op ⦋0⦌)) ≫ e.inv := congrArg (fun k => e.hom ≫ k ≫ e.inv) h
      _ = 𝟙 Y := by simp
  ι_p₁ := by
    have h : B.σ (0 : Fin 1) ≫ B.δ (1 : Fin 2) = 𝟙 (B.obj (.op ⦋0⦌)) :=
      B.δ_comp_σ_succ (i := 0)
    calc
      (e.hom ≫ B.σ (0 : Fin 1)) ≫ (B.δ (1 : Fin 2) ≫ e.inv) =
          e.hom ≫ (B.σ (0 : Fin 1) ≫ B.δ (1 : Fin 2)) ≫ e.inv := by
        simp only [Category.assoc]
      _ = e.hom ≫ 𝟙 (B.obj (.op ⦋0⦌)) ≫ e.inv := congrArg (fun k => e.hom ≫ k ≫ e.inv) h
      _ = 𝟙 Y := by simp

/-- The prepath keeps the actual original first-degree object. -/
theorem prepath_P (B : SimplicialObject C) {Y : C} (e : Y ≅ B.obj (.op ⦋0⦌)) :
    (prepath B e).P = B.obj (.op ⦋1⦌) := rfl

/-- The first projection retains the same original face and target identification. -/
theorem prepath_p₀ (B : SimplicialObject C) {Y : C} (e : Y ≅ B.obj (.op ⦋0⦌)) :
    (prepath B e).p₀ = B.δ (0 : Fin 2) ≫ e.inv := rfl

/-- The second projection retains the same original face and target identification. -/
theorem prepath_p₁ (B : SimplicialObject C) {Y : C} (e : Y ≅ B.obj (.op ⦋0⦌)) :
    (prepath B e).p₁ = B.δ (1 : Fin 2) ≫ e.inv := rfl

/-- The section retains the same original identification and degeneracy. -/
theorem prepath_ι (B : SimplicialObject C) {Y : C} (e : Y ≅ B.obj (.op ⦋0⦌)) :
    (prepath B e).ι = e.hom ≫ B.σ (0 : Fin 1) := rfl

/-- Every actual edge gives a right homotopy through this same prepath object. -/
def edgeToRightHomotopy (B : SimplicialObject C) {Y : C}
    (e : Y ≅ B.obj (.op ⦋0⦌)) {X : C} {f g : X ⟶ B.obj (.op ⦋0⦌)}
    (d : (right X B).Edge f g) : (prepath B e).RightHomotopy (g ≫ e.inv) (f ≫ e.inv) where
  h := d.edge
  h₀ := by
    have ht : (d.edge : X ⟶ B.obj (.op ⦋1⦌)) ≫ B.δ (0 : Fin 2) = g :=
      (right_face_apply X B (0 : Fin 2) d.edge).symm.trans d.tgt_eq
    change d.edge ≫ (B.δ (0 : Fin 2) ≫ e.inv) = g ≫ e.inv
    exact (Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ e.inv) ht)
  h₁ := by
    have hs : (d.edge : X ⟶ B.obj (.op ⦋1⦌)) ≫ B.δ (1 : Fin 2) = f :=
      (right_face_apply X B (1 : Fin 2) d.edge).symm.trans d.src_eq
    change d.edge ≫ (B.δ (1 : Fin 2) ≫ e.inv) = f ≫ e.inv
    exact (Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ e.inv) hs)

/-- Every right homotopy through the actual prepath object gives its original edge. -/
def rightHomotopyToEdge (B : SimplicialObject C) {Y : C}
    (e : Y ≅ B.obj (.op ⦋0⦌)) {X : C} {f g : X ⟶ Y}
    (h : (prepath B e).RightHomotopy f g) : (right X B).Edge (g ≫ e.hom) (f ≫ e.hom) :=
  SSet.Edge.mk h.h
    (by
      refine (right_face_apply X B (1 : Fin 2) h.h).trans ?_
      apply (cancel_mono e.inv).1
      calc
        (h.h ≫ B.δ (1 : Fin 2)) ≫ e.inv = h.h ≫ (B.δ (1 : Fin 2) ≫ e.inv) :=
          Category.assoc _ _ _
        _ = g := h.h₁
        _ = (g ≫ e.hom) ≫ e.inv := by simp)
    (by
      refine (right_face_apply X B (0 : Fin 2) h.h).trans ?_
      apply (cancel_mono e.inv).1
      calc
        (h.h ≫ B.δ (0 : Fin 2)) ≫ e.inv = h.h ≫ (B.δ (0 : Fin 2) ≫ e.inv) :=
          Category.assoc _ _ _
        _ = f := h.h₀
        _ = (f ≫ e.hom) ≫ e.inv := by simp)

/-- The edge conversion retains the entire original first-degree map. -/
theorem edgeToRightHomotopy_h (B : SimplicialObject C) {Y : C}
    (e : Y ≅ B.obj (.op ⦋0⦌)) {X : C} {f g : X ⟶ B.obj (.op ⦋0⦌)}
    (d : (right X B).Edge f g) : (edgeToRightHomotopy B e d).h = d.edge := rfl

/-- The homotopy conversion retains the entire original path homotopy map. -/
theorem rightHomotopyToEdge_edge (B : SimplicialObject C) {Y : C}
    (e : Y ≅ B.obj (.op ⦋0⦌)) {X : C} {f g : X ⟶ Y}
    (h : (prepath B e).RightHomotopy f g) : (rightHomotopyToEdge B e h).edge = h.h := rfl

section Weak

variable [CategoryWithWeakEquivalences C] (B : SimplicialObject C) {Y : C}
  (e : Y ≅ B.obj (.op ⦋0⦌)) [WeakEquivalence (e.hom ≫ B.σ (0 : Fin 1))]

/-- The same original weak section makes the actual first-degree prepath a path object. -/
def path : PathObject Y where
  __ := prepath B e
  weakEquivalence_ι := by
    change WeakEquivalence (e.hom ≫ B.σ (0 : Fin 1))
    infer_instance

/-- Edges retain the original right-homotopy relation at the identified target. -/
theorem edge_rightHomotopyRel {X : C} {f g : X ⟶ B.obj (.op ⦋0⦌)}
    (d : (right X B).Edge f g) : RightHomotopyRel (f ≫ e.inv) (g ≫ e.inv) := by
  let h : (path B e).RightHomotopy (g ≫ e.inv) (f ≫ e.inv) := edgeToRightHomotopy B e d
  exact h.rightHomotopyRel.symm

end Weak

section Model

variable [ModelCategory C] (B : SimplicialObject C) {Y : C} (e : Y ≅ B.obj (.op ⦋0⦌))
  [WeakEquivalence (e.hom ≫ B.σ (0 : Fin 1))]
  [Fibration (prod.lift (B.δ (0 : Fin 2) ≫ e.inv) (B.δ (1 : Fin 2) ≫ e.inv))]
  [IsFibrant Y]

/-- The original product fibration makes this same path object good. -/
instance path_isGood : (path B e).IsGood where
  fibration_p := by
    change Fibration (prod.lift (B.δ (0 : Fin 2) ≫ e.inv) (B.δ (1 : Fin 2) ≫ e.inv))
    infer_instance

variable (X : C) [IsCofibrant X]
  {H : Type uH} [Category.{vH} H] (L : C ⥤ H) [L.IsLocalization (weakEquivalences C)]

omit [Fibration (prod.lift (B.δ (0 : Fin 2) ≫ e.inv) (B.δ (1 : Fin 2) ≫ e.inv))] in
/-- The full component function is the original localization image of the original target
identification. -/
def piZeroToHom : SSet.π₀ (right X B) → (L.obj X ⟶ L.obj Y) :=
  SSet.π₀.lift (fun f => L.map (f ≫ e.inv)) (fun _ _ d =>
    (RightHomotopyRel.iff_map_eq L X Y).1 (edge_rightHomotopyRel B e d))

omit [Fibration (prod.lift (B.δ (0 : Fin 2) ≫ e.inv) (B.δ (1 : Fin 2) ≫ e.inv))] in
/-- The component function keeps every original represented morphism. -/
@[simp]
theorem piZeroToHom_mk (f : X ⟶ B.obj (.op ⦋0⦌)) :
    piZeroToHom B e X L (SSet.π₀.mk f) = L.map (f ≫ e.inv) := rfl

/-- Equality of localized original maps gives equality of actual right-complex components. -/
theorem piZero_mk_eq_of_map_eq (f g : X ⟶ B.obj (.op ⦋0⦌))
    (h : L.map (f ≫ e.inv) = L.map (g ≫ e.inv)) :
    SSet.π₀.mk (X := right X B) f = SSet.π₀.mk g := by
  have hr : RightHomotopyRel (f ≫ e.inv) (g ≫ e.inv) := (RightHomotopyRel.iff_map_eq L X Y).2 h
  let hp : (path B e).RightHomotopy (g ≫ e.inv) (f ≫ e.inv) := hr.symm.rightHomotopy (path B e)
  have hd := rightHomotopyToEdge B e hp
  have hs : (f ≫ e.inv) ≫ e.hom = f := by simp
  have ht : (g ≫ e.inv) ≫ e.hom = g := by simp
  exact SSet.π₀.sound (hd.ofEq hs ht)

/-- The actual component function is injective by the original good path object. -/
theorem piZeroToHom_injective : Function.Injective (piZeroToHom B e X L) := by
  intro p q h
  obtain ⟨f, rfl⟩ := SSet.π₀.mk_surjective p
  obtain ⟨g, rfl⟩ := SSet.π₀.mk_surjective q
  exact piZero_mk_eq_of_map_eq B e X L f g h

omit [Fibration (prod.lift (B.δ (0 : Fin 2) ≫ e.inv) (B.δ (1 : Fin 2) ≫ e.inv))] in
/-- The actual component function is surjective by the original localization's represented maps. -/
theorem piZeroToHom_surjective : Function.Surjective (piZeroToHom B e X L) := by
  intro p
  obtain ⟨f, hf⟩ := map_surjective_of_isLocalization L X Y p
  refine ⟨SSet.π₀.mk (f ≫ e.hom), ?_⟩
  change L.map ((f ≫ e.hom) ≫ e.inv) = p
  simpa using hf

/-- The complete right-complex component equivalence with the original localization Hom set. -/
def piZeroEquiv : SSet.π₀ (right X B) ≃ (L.obj X ⟶ L.obj Y) :=
  Equiv.ofBijective (piZeroToHom B e X L)
    ⟨piZeroToHom_injective B e X L, piZeroToHom_surjective B e X L⟩

/-- The forward equivalence is exactly the original represented localization map. -/
@[simp]
theorem piZeroEquiv_mk (f : X ⟶ B.obj (.op ⦋0⦌)) :
    piZeroEquiv B e X L (SSet.π₀.mk f) = L.map (f ≫ e.inv) := rfl

/-- The inverse Hom function keeps the original forward degree-zero target identification. -/
@[simp]
theorem piZeroEquiv_symm_map (f : X ⟶ Y) :
    (piZeroEquiv B e X L).symm (L.map f) = SSet.π₀.mk (f ≫ e.hom) := by
  apply (piZeroEquiv B e X L).injective
  simp

/-- The complete component Hom function preserves every original cofibrant-source map. -/
theorem piZeroEquiv_naturality_source {X' : C} [IsCofibrant X'] (p : X' ⟶ X)
    (q : SSet.π₀ (right X B)) :
    piZeroEquiv B e X' L
        (SSet.mapπ₀ (precomp ((CosimplicialObject.const C).map p) B) q) =
      L.map p ≫ piZeroEquiv B e X L q := by
  obtain ⟨f, rfl⟩ := SSet.π₀.mk_surjective q
  let h : X ⟶ B.obj (.op ⦋0⦌) := f
  calc
    piZeroEquiv B e X' L
        (SSet.mapπ₀ (precomp ((CosimplicialObject.const C).map p) B) (SSet.π₀.mk f)) =
        piZeroEquiv B e X' L (SSet.π₀.mk (p ≫ h)) :=
      congrArg (piZeroEquiv B e X' L)
        (SSet.mapπ₀_mk (precomp ((CosimplicialObject.const C).map p) B) f)
    _ = L.map ((p ≫ h) ≫ e.inv) := piZeroEquiv_mk B e X' L _
    _ = L.map p ≫ L.map (h ≫ e.inv) := by rw [Category.assoc, L.map_comp]
    _ = L.map p ≫ piZeroEquiv B e X L (SSet.π₀.mk f) :=
      congrArg (fun k => L.map p ≫ k) (piZeroEquiv_mk B e X L h).symm

/-- The entire inverse Hom function preserves the same original cofibrant-source map. -/
theorem piZeroEquiv_symm_naturality_source {X' : C} [IsCofibrant X'] (p : X' ⟶ X)
    (q : L.obj X ⟶ L.obj Y) :
    (piZeroEquiv B e X' L).symm (L.map p ≫ q) =
      SSet.mapπ₀ (precomp ((CosimplicialObject.const C).map p) B)
        ((piZeroEquiv B e X L).symm q) := by
  apply (piZeroEquiv B e X' L).injective
  rw [Equiv.apply_symm_apply, piZeroEquiv_naturality_source B e X L p,
    Equiv.apply_symm_apply]

/-- Every actual simplicial target map and original degree-zero square preserve the full Hom
function. -/
theorem piZeroEquiv_naturality_target {B' : SimplicialObject C} {Y' : C}
    (e' : Y' ≅ B'.obj (.op ⦋0⦌)) [WeakEquivalence (e'.hom ≫ B'.σ (0 : Fin 1))]
    [Fibration (prod.lift (B'.δ (0 : Fin 2) ≫ e'.inv) (B'.δ (1 : Fin 2) ≫ e'.inv))]
    [IsFibrant Y'] (b : B ⟶ B') (g : Y ⟶ Y')
    (he : e.hom ≫ b.app (.op ⦋0⦌) = g ≫ e'.hom) (q : SSet.π₀ (right X B)) :
    piZeroEquiv B' e' X L
        (SSet.mapπ₀ (postcomp ((CosimplicialObject.const C).obj X) b) q) =
      piZeroEquiv B e X L q ≫ L.map g := by
  have hb : b.app (.op ⦋0⦌) ≫ e'.inv = e.inv ≫ g := by
    apply (cancel_epi e.hom).1
    calc
      e.hom ≫ (b.app (.op ⦋0⦌) ≫ e'.inv) = (e.hom ≫ b.app (.op ⦋0⦌)) ≫ e'.inv :=
        (Category.assoc _ _ _).symm
      _ = (g ≫ e'.hom) ≫ e'.inv := congrArg (fun k => k ≫ e'.inv) he
      _ = g := by simp
      _ = e.hom ≫ (e.inv ≫ g) := (e.hom_inv_id_assoc g).symm
  obtain ⟨f, rfl⟩ := SSet.π₀.mk_surjective q
  let h : X ⟶ B.obj (.op ⦋0⦌) := f
  calc
    piZeroEquiv B' e' X L
        (SSet.mapπ₀ (postcomp ((CosimplicialObject.const C).obj X) b) (SSet.π₀.mk f)) =
        piZeroEquiv B' e' X L (SSet.π₀.mk (h ≫ b.app (.op ⦋0⦌))) :=
      congrArg (piZeroEquiv B' e' X L)
        (SSet.mapπ₀_mk (postcomp ((CosimplicialObject.const C).obj X) b) f)
    _ = L.map ((h ≫ b.app (.op ⦋0⦌)) ≫ e'.inv) := piZeroEquiv_mk B' e' X L _
    _ = L.map ((h ≫ e.inv) ≫ g) := L.congr_map (by rw [Category.assoc, hb, Category.assoc])
    _ = L.map (h ≫ e.inv) ≫ L.map g := L.map_comp _ _
    _ = piZeroEquiv B e X L (SSet.π₀.mk f) ≫ L.map g :=
      congrArg (fun k => k ≫ L.map g) (piZeroEquiv_mk B e X L h).symm

/-- The entire inverse target Hom function keeps the same original simplicial map and square. -/
theorem piZeroEquiv_symm_naturality_target {B' : SimplicialObject C} {Y' : C}
    (e' : Y' ≅ B'.obj (.op ⦋0⦌)) [WeakEquivalence (e'.hom ≫ B'.σ (0 : Fin 1))]
    [Fibration (prod.lift (B'.δ (0 : Fin 2) ≫ e'.inv) (B'.δ (1 : Fin 2) ≫ e'.inv))]
    [IsFibrant Y'] (b : B ⟶ B') (g : Y ⟶ Y')
    (he : e.hom ≫ b.app (.op ⦋0⦌) = g ≫ e'.hom) (q : L.obj X ⟶ L.obj Y) :
    (piZeroEquiv B' e' X L).symm (q ≫ L.map g) =
      SSet.mapπ₀ (postcomp ((CosimplicialObject.const C).obj X) b)
        ((piZeroEquiv B e X L).symm q) := by
  apply (piZeroEquiv B' e' X L).injective
  rw [Equiv.apply_symm_apply, piZeroEquiv_naturality_target B e X L e' b g he,
    Equiv.apply_symm_apply]

/-- The two-variable component Hom function retains both original input maps. -/
theorem piZeroEquiv_naturality {X' : C} [IsCofibrant X'] (p : X' ⟶ X)
    {B' : SimplicialObject C} {Y' : C} (e' : Y' ≅ B'.obj (.op ⦋0⦌))
    [WeakEquivalence (e'.hom ≫ B'.σ (0 : Fin 1))]
    [Fibration (prod.lift (B'.δ (0 : Fin 2) ≫ e'.inv) (B'.δ (1 : Fin 2) ≫ e'.inv))]
    [IsFibrant Y'] (b : B ⟶ B') (g : Y ⟶ Y')
    (he : e.hom ≫ b.app (.op ⦋0⦌) = g ≫ e'.hom) (q : SSet.π₀ (right X B)) :
    piZeroEquiv B' e' X' L
        (SSet.mapπ₀ (precomp ((CosimplicialObject.const C).map p) B ≫
          postcomp ((CosimplicialObject.const C).obj X') b) q) =
      L.map p ≫ piZeroEquiv B e X L q ≫ L.map g := by
  rw [SSet.mapπ₀_comp_apply, piZeroEquiv_naturality_target B e X' L e' b g he,
    piZeroEquiv_naturality_source B e X L p]
  exact Category.assoc _ _ _

/-- Both inverse functions retain the same original two-variable diagram. -/
theorem piZeroEquiv_symm_naturality {X' : C} [IsCofibrant X'] (p : X' ⟶ X)
    {B' : SimplicialObject C} {Y' : C} (e' : Y' ≅ B'.obj (.op ⦋0⦌))
    [WeakEquivalence (e'.hom ≫ B'.σ (0 : Fin 1))]
    [Fibration (prod.lift (B'.δ (0 : Fin 2) ≫ e'.inv) (B'.δ (1 : Fin 2) ≫ e'.inv))]
    [IsFibrant Y'] (b : B ⟶ B') (g : Y ⟶ Y')
    (he : e.hom ≫ b.app (.op ⦋0⦌) = g ≫ e'.hom) (q : L.obj X ⟶ L.obj Y) :
    (piZeroEquiv B' e' X' L).symm (L.map p ≫ q ≫ L.map g) =
      SSet.mapπ₀ (precomp ((CosimplicialObject.const C).map p) B ≫
        postcomp ((CosimplicialObject.const C).obj X') b)
        ((piZeroEquiv B e X L).symm q) := by
  apply (piZeroEquiv B' e' X' L).injective
  rw [Equiv.apply_symm_apply, piZeroEquiv_naturality B e X L p e' b g he,
    Equiv.apply_symm_apply]

/-- The same full component equivalence for the actual original canonical homotopy category. -/
def canonicalPiZeroEquiv :
    SSet.π₀ (right X B) ≃ (((weakEquivalences C).Q).obj X ⟶ ((weakEquivalences C).Q).obj Y) :=
  piZeroEquiv B e X ((weakEquivalences C).Q)

/-- The canonical specialization keeps the unchanged original localization map. -/
@[simp]
theorem canonicalPiZeroEquiv_mk (f : X ⟶ B.obj (.op ⦋0⦌)) :
    canonicalPiZeroEquiv B e X (SSet.π₀.mk f) = ((weakEquivalences C).Q).map (f ≫ e.inv) :=
  piZeroEquiv_mk B e X ((weakEquivalences C).Q) f

/-- The canonical inverse keeps the unchanged original degree-zero target identification. -/
@[simp]
theorem canonicalPiZeroEquiv_symm_map (f : X ⟶ Y) :
    (canonicalPiZeroEquiv B e X).symm (((weakEquivalences C).Q).map f) = SSet.π₀.mk (f ≫ e.hom) :=
  piZeroEquiv_symm_map B e X ((weakEquivalences C).Q) f

end Model

end HomotopicalAlgebra.ResolutionHomComplex.RightPiZero

end
end
end
