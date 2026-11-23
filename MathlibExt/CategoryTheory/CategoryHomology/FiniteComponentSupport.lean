/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.Grp.FiniteColimitSupport
public import Mathlib.CategoryTheory.ConnectedComponents
public import MathlibExt.CategoryTheory.CategoryHomology.Basic
public import MathlibExt.AlgebraicTopology.SimplicialSet.Homology.Coproducts
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Finite categorical-component support of nerve homology

Every actual chain lies in the categorical component of its first object.
The original component inclusions are jointly surjective, injective and
pairwise disjoint, so the stock pointwise Types criterion proves their
nerve cofan a colimit. Homology preserves its discrete coproduct; the
finite additive-cofan support theorem retains the ORIGINAL inclusions.
No Ring, free-isoclass, connectedness or comparison-map hypothesis enters.
-/

noncomputable section

open CategoryTheory Limits Opposite

universe u v w

public section

namespace CategoryTheory

noncomputable local instance finiteComponentHomologyCoproducts :
    HasCoproducts.{w} AddCommGrpCat.{w} :=
  fun (I : Type w) => by
    let : Small.{w} (Discrete I) := small_self (Discrete I)
    exact AddCommGrpCat.hasColimitsOfShape.{w, w, w} (J := Discrete I)

private theorem componentNerve_jointlySurjective
    {J : Type u} [Category.{v} J] (n : SimplexCategoryᵒᵖ)
    (F : (nerve J).obj n) :
    ∃ (c : ConnectedComponents J) (X : (nerve c.Component).obj n),
      (nerveMap c.ι).app n X = F := by
  let c : ConnectedComponents J := ConnectedComponents.mk (F.obj (0 : Fin (n.unop.len + 1)))
  have hTag : ∀ j, c.objectProperty (F.obj j) := by
    intro j
    change ConnectedComponents.mk (F.obj j) =
      ConnectedComponents.mk (F.obj (0 : Fin (n.unop.len + 1)))
    exact Quotient.sound' (Zigzag.of_inv (F.map (homOfLE (Fin.zero_le j))))
  let L := ObjectProperty.lift c.objectProperty F hTag
  refine ⟨c, L, ?_⟩
  change L ⋙ c.ι = F
  rfl

private theorem componentNerve_inclusion_injective
    {J : Type u} [Category.{v} J] (c : ConnectedComponents J)
    (n : SimplexCategoryᵒᵖ) : Function.Injective ((nerveMap c.ι).app n) := by
  intro X Y h
  let H : c.Component ⥤ J := c.ι
  change X ⋙ H = Y ⋙ H at h
  have hObj : ∀ j, X.obj j = Y.obj j := fun j =>
    ObjectProperty.FullSubcategory.ext (Functor.congr_obj h j)
  have hom_heq {P Q P' Q' : c.Component} (hP : P = P') (hQ : Q = Q')
      (a : P ⟶ Q) (b : P' ⟶ Q') (hab : HEq a.hom b.hom) : HEq a b := by
    cases hP
    cases hQ
    apply heq_of_eq
    apply InducedCategory.hom_ext
    exact eq_of_heq hab
  refine Functor.hext hObj ?_
  intro j k f
  have hMap := Functor.hcongr_hom h f
  change HEq (X.map f).hom (Y.map f).hom at hMap
  exact hom_heq (hObj j) (hObj k) (X.map f) (Y.map f) hMap

private theorem componentNerve_inclusion_eq_index
    {J : Type u} [Category.{v} J] (n : SimplexCategoryᵒᵖ)
    {c d : ConnectedComponents J}
    (X : (nerve c.Component).obj n) (Y : (nerve d.Component).obj n)
    (h : (nerveMap c.ι).app n X = (nerveMap d.ι).app n Y) : c = d := by
  change X ⋙ c.ι = Y ⋙ d.ι at h
  let i : Fin (n.unop.len + 1) := 0
  have hObj : (X.obj i).obj = (Y.obj i).obj := Functor.congr_obj h i
  exact (X.obj i).property.symm.trans
    ((congrArg ConnectedComponents.mk hObj).trans (Y.obj i).property)

/-- Every original nerve homology class has FINITE support in the actual
categorical components, in every degree and independent object/Hom universes. -/
theorem categoryHomology_exists_finite_component_sum
    (J : Type u) [Category.{v} J] (A : AddCommGrpCat.{max u v}) (q : ℕ)
    (y : (nerve J).homology (C := AddCommGrpCat.{max u v}) A q) :
    ∃ (s : Finset (ConnectedComponents J))
      (x : ∀ c : ConnectedComponents J, (nerve c.Component).homology (C := AddCommGrpCat.{max u v})
          A q),
      y = ∑ c ∈ s, SSet.homologyMap (nerveMap c.ι) A q (x c) := by
  let I := ULift.{max u v} (ConnectedComponents J)
  let N : I → SSet.{max u v} := fun c => nerve c.down.Component
  let cN : Cofan N := Cofan.mk (nerve J) (fun c => nerveMap c.down.ι)
  have hN : IsColimit cN := by
    apply evaluationJointlyReflectsColimits
    intro n
    let c : Cofan (fun c : I => (nerve c.down.Component).obj n) :=
      Cofan.mk ((nerve J).obj n) (fun c => (nerveMap c.down.ι).app n)
    have hc : c.cofanTypes.IsColimit := CofanTypes.isColimit_mk _
      (fun F => by
        obtain ⟨d, X, hX⟩ := componentNerve_jointlySurjective n F
        exact ⟨⟨d⟩, X, hX⟩)
      (fun c => componentNerve_inclusion_injective c.down n)
      (fun c d X Y h => by
        cases c with
        | up c =>
            cases d with
            | up d =>
                exact congrArg (fun e : ConnectedComponents J => (ULift.up e : I))
                  (componentNerve_inclusion_eq_index n X Y h))
    exact (isColimitMapCoconeCofanMkEquiv
      ((evaluation SimplexCategoryᵒᵖ (Type (max u v))).obj n)
      N (fun c => nerveMap c.down.ι)).symm
        (Classical.choice ((Cofan.isColimit_cofanTypes_iff c).mp hc))
  let H : Cofan (fun c : I => (nerve c.down.Component).homology
      (C := AddCommGrpCat.{max u v}) A q) :=
    Cofan.mk ((nerve J).homology (C := AddCommGrpCat.{max u v}) A q)
      (fun c => SSet.homologyMap (nerveMap c.down.ι) A q)
  have hH : IsColimit H :=
    isColimitCofanMkObjOfIsColimit (SSet.homologyFunctor (C := AddCommGrpCat.{max u v}) A q) N
      (fun c => nerveMap c.down.ι) hN
  obtain ⟨s, x, hy⟩ := IsColimit.exists_finite_sum.{max u v, 0} hH y
  let e : I ↪ ConnectedComponents J :=
    ⟨ULift.down, fun a b h => by
      cases a
      cases b
      cases h
      rfl⟩
  refine ⟨s.map e, fun c => x (ULift.up c), ?_⟩
  have hSum :
      (∑ c ∈ s.map e, SSet.homologyMap (nerveMap c.ι) A q (x (ULift.up c))) =
        ∑ c ∈ s, SSet.homologyMap (nerveMap c.down.ι) A q (x c) := by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro c _
    cases c
    rfl
  exact hy.trans hSum.symm

end CategoryTheory

end
