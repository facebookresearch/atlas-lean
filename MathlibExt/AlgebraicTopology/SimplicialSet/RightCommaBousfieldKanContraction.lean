/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKanSource
public import MathlibExt.CategoryTheory.CategoryBar.CommaRightPointNaturality
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products

/-!
# Common-universe fixed-degree right-comma contraction

The Elements category of the right-comma nerve diagram in each degree
projects to the original source chains. Its canonical section lies over
the final image object, and the final comma arrows give a natural
contraction from section-after-projection to the identity.

The original projection, section and retyping proofs are retained for
arbitrary object and morphism universes. This file proves no global
simplicial homotopy, source quasi-isomorphism or weak-equivalence theorem.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace SSet

universe uC h uD

variable {C : Type uC} {D : Type uD} [Category.{h} C] [Category.{h} D]

/-- The right-comma nerve diagram evaluated in inner simplicial degree `n`. -/
abbrev rightCommaDegreeCoefficient (F : C ⥤ D) (n : ℕ) : D ⥤ Type (max uC h) :=
  rightCommaNerveDiagram.{uC, h, uD} F ⋙
    (evaluation SimplexCategoryᵒᵖ (Type (max uC h))).obj (op ⦋n⦌)

/-- Projection from the fixed-degree Elements category to the underlying
source chain. -/
noncomputable def rightCommaDegreePi (F : C ⥤ D) (n : ℕ) :
    (rightCommaDegreeCoefficient F n).Elements ⥤
      Discrete (ComposableArrows C n) where
  obj e := Discrete.mk
    (e.val ⋙ CostructuredArrow.proj F e.obj)
  map {e e'} f := Discrete.eqToHom (by
    rw [← f.map_val]
    rfl)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

@[simp]
theorem rightCommaDegreePi_obj_as (F : C ⥤ D) (n : ℕ)
    (e : (rightCommaDegreeCoefficient F n).Elements) :
    ((rightCommaDegreePi F n).obj e).as =
      e.val ⋙ CostructuredArrow.proj F e.obj :=
  rfl

/-- Canonical Elements object over a source chain: its base is the image of
the final vertex and its final comma arrow is the identity. -/
noncomputable def rightCommaDegreeSigmaObj (F : C ⥤ D) (n : ℕ)
    (X : ComposableArrows C n) :
    (rightCommaDegreeCoefficient F n).Elements where
  obj := F.obj X.right
  val := CategoryBar.barRightCommaEquiv F (F.obj X.right) n
    ⟨X, ULift.up PUnit.unit, 𝟙 (F.obj X.right)⟩

/-- Canonical section of the fixed-degree projection. -/
noncomputable def rightCommaDegreeSigma (F : C ⥤ D) (n : ℕ) :
    Discrete (ComposableArrows C n) ⥤
      (rightCommaDegreeCoefficient F n).Elements :=
  Discrete.functor (rightCommaDegreeSigmaObj F n)

/-- The base object of the canonical section is the image of the final
vertex. -/
theorem rightCommaDegreeSigma_obj_obj (F : C ⥤ D) (n : ℕ)
    (X : Discrete (ComposableArrows C n)) :
    ((rightCommaDegreeSigma F n).obj X).obj = F.obj X.as.right :=
  rfl

/-- The canonical section followed by the underlying-chain projection is
strictly the identity. -/
@[simp]
theorem rightCommaDegreeSigma_comp_pi (F : C ⥤ D) (n : ℕ) :
    rightCommaDegreeSigma F n ⋙ rightCommaDegreePi F n =
      𝟭 (Discrete (ComposableArrows C n)) := by
  apply Discrete.functor_ext
  intro X
  apply Discrete.ext
  rfl

/-- The base morphism of the contraction is the final comma arrow. -/
def rightCommaDegreeLastArrow (F : C ⥤ D) (n : ℕ)
    (e : (rightCommaDegreeCoefficient F n).Elements) :
    F.obj ((rightCommaDegreePi F n).obj e).as.right ⟶ e.obj :=
  CostructuredArrow.hom (e.val.obj (Fin.last n))

/-- Mapping the canonical section along the final comma arrow recovers the
original comma chain. -/
theorem rightCommaDegreeSigmaObj_map_last (F : C ⥤ D) (n : ℕ)
    (e : (rightCommaDegreeCoefficient F n).Elements) :
    (rightCommaDegreeCoefficient F n).map
        (rightCommaDegreeLastArrow F n e)
        (rightCommaDegreeSigmaObj F n
          ((rightCommaDegreePi F n).obj e).as).val =
      e.val := by
  let Y : ComposableArrows (CostructuredArrow F e.obj) n := by
    change ((rightCommaNerveDiagram.{uC, h, uD} F).obj e.obj).obj (op ⦋n⦌)
    exact e.val
  let G : ComposableArrows C n :=
    Y ⋙ CostructuredArrow.proj F e.obj
  let h : F.obj G.right ⟶ e.obj :=
    CostructuredArrow.hom (Y.obj (Fin.last n))
  let x : CategoryBar.barObj C
      (CategoryBar.commaCoeffR F (F.obj G.right))
      (CategoryBar.unitCoeffL C) n :=
    ⟨G, ULift.up PUnit.unit, 𝟙 (F.obj G.right)⟩
  have hNat := CategoryBar.barRightComma_naturality_d F h
  have hEval := ConcreteCategory.congr_hom
    (NatTrans.congr_app hNat (op ⦋n⦌)) x
  have hx : CategoryBar.barCoeffMap
      (CategoryBar.commaCoeffRMap F h)
      (𝟙 (CategoryBar.unitCoeffL C)) x =
        (CategoryBar.barRightCommaEquiv F e.obj n).symm Y := by
    rw [CategoryBar.barRightCommaEquiv_symm_apply]
    refine Sigma.ext rfl (heq_of_eq ?_)
    apply Prod.ext
    · rfl
    · exact Category.id_comp h
  change ((rightCommaNerveDiagram.{uC, h, uD} F).map h).app (op ⦋n⦌)
      (CategoryBar.barRightCommaEquiv F (F.obj G.right) n x) = Y
  change CategoryBar.barRightCommaEquiv F e.obj n
      (CategoryBar.barCoeffMap
        (CategoryBar.commaCoeffRMap F h)
        (𝟙 (CategoryBar.unitCoeffL C)) x) =
    ((rightCommaNerveDiagram.{uC, h, uD} F).map h).app (op ⦋n⦌)
      (CategoryBar.barRightCommaEquiv F (F.obj G.right) n x) at hEval
  rw [← hEval, hx, Equiv.apply_symm_apply]

/-- Component of the contraction from section-after-projection to the
identity Elements functor. -/
noncomputable def rightCommaDegreeSigmaPiToIdApp (F : C ⥤ D) (n : ℕ)
    (e : (rightCommaDegreeCoefficient F n).Elements) :
    (rightCommaDegreePi F n ⋙ rightCommaDegreeSigma F n).obj e ⟶ e :=
  Functor.Elements.homMk (rightCommaDegreeLastArrow F n e)
    (rightCommaDegreeSigmaObj_map_last F n e)

@[simp]
theorem rightCommaDegreeSigmaPiToIdApp_hom (F : C ⥤ D) (n : ℕ)
    (e : (rightCommaDegreeCoefficient F n).Elements) :
    (rightCommaDegreeSigmaPiToIdApp F n e).hom =
      rightCommaDegreeLastArrow F n e :=
  rfl

private theorem rightCommaDegreeSigma_map_hom_eq_id
    (F : C ⥤ D) (n : ℕ)
    (X : Discrete (ComposableArrows C n)) (f : X ⟶ X) :
    ((rightCommaDegreeSigma F n).map f).hom =
      𝟙 ((rightCommaDegreeSigma F n).obj X).obj := by
  have hf : f = 𝟙 X := Subsingleton.elim _ _
  subst f
  rfl

private def rightCommaDegreeSigmaRetype
    (F : C ⥤ D) (n : ℕ)
    {X Y : Discrete (ComposableArrows C n)} (h : X = Y)
    {d : D} (g : ((rightCommaDegreeSigma F n).obj Y).obj ⟶ d) :
    ((rightCommaDegreeSigma F n).obj X).obj ⟶ d :=
  F.map (eqToHom (congrArg
      (fun Z : Discrete (ComposableArrows C n) => Z.as.right) h)) ≫ g

private theorem rightCommaDegreeSigma_map_hom_comp
    (F : C ⥤ D) (n : ℕ)
    {X Y : Discrete (ComposableArrows C n)} (f : X ⟶ Y)
    {d : D} (g : ((rightCommaDegreeSigma F n).obj Y).obj ⟶ d) :
    ((rightCommaDegreeSigma F n).map f).hom ≫ g =
      rightCommaDegreeSigmaRetype F n (Discrete.ext f.eq) g := by
  have hXY : X = Y := Discrete.ext f.eq
  subst Y
  have hf : f = 𝟙 X := Subsingleton.elim _ _
  subst f
  unfold rightCommaDegreeSigmaRetype
  rw [rightCommaDegreeSigma_map_hom_eq_id, Category.id_comp,
    eqToHom_refl, F.map_id]
  change g = (𝟙 ((rightCommaDegreeSigma F n).obj X).obj) ≫ g
  exact (Category.id_comp g).symm

/-- The final comma arrows form a natural contraction from
section-after-projection to the identity. -/
noncomputable def rightCommaDegreeSigmaPiToId (F : C ⥤ D) (n : ℕ) :
    rightCommaDegreePi F n ⋙ rightCommaDegreeSigma F n ⟶
      𝟭 (rightCommaDegreeCoefficient F n).Elements where
  app e := rightCommaDegreeSigmaPiToIdApp F n e
  naturality {e e'} f := by
    apply Functor.Elements.hom_ext
    let Y : ComposableArrows (CostructuredArrow F e.obj) n := by
      change ((rightCommaNerveDiagram.{uC, h, uD} F).obj e.obj).obj (op ⦋n⦌)
      exact e.val
    let Y' : ComposableArrows (CostructuredArrow F e'.obj) n := by
      change ((rightCommaNerveDiagram.{uC, h, uD} F).obj e'.obj).obj (op ⦋n⦌)
      exact e'.val
    have hMap := f.map_val
    change Y ⋙ CostructuredArrow.map f.hom = Y' at hMap
    have hLastObj :
        (Y ⋙ CostructuredArrow.map f.hom).obj (Fin.last n) =
          Y'.obj (Fin.last n) :=
      congrArg (fun Z => Z.obj (Fin.last n)) hMap
    have hW := CostructuredArrow.w (eqToHom hLastObj)
    rw [CostructuredArrow.eqToHom_left] at hW
    have hLast :
        rightCommaDegreeSigmaRetype F n
            (Discrete.ext ((rightCommaDegreePi F n).map f).eq)
            (rightCommaDegreeLastArrow F n e') =
          rightCommaDegreeLastArrow F n e ≫ f.hom := by
      change F.map (eqToHom (congrArg CostructuredArrow.left hLastObj)) ≫
          CostructuredArrow.hom (Y'.obj (Fin.last n)) =
        CostructuredArrow.hom (Y.obj (Fin.last n)) ≫ f.hom at hW
      exact hW
    exact (rightCommaDegreeSigma_map_hom_comp F n
      ((rightCommaDegreePi F n).map f)
      (rightCommaDegreeSigmaPiToIdApp F n e').hom).trans hLast

end SSet

end
