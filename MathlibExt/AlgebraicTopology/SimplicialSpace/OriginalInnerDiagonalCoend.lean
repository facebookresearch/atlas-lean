/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalInnerDiagonalFrame

/-!
# The inner diagonal as a weighted coend

The standard-simplex weighted coend of a simplicial diagram of simplicial spaces is naturally
isomorphic to its coefficient-inner diagonal. Explicit inclusions and identity-simplex descent
maps establish the coend universal property and identify the raw diagonal coaugmentation with
its transported coend map.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SimplicialSpace.Inner SSet.modelCategoryQuillen

namespace SimplicialSpace.OriginalInnerRealization

/-- The actual inner simplex represented by an original ordinal identity. -/
def identitySimplex (n : SimplexCategoryᵒᵖ) :
    (SSet.stdSimplex.{u}.obj n.unop).obj n :=
  SSet.stdSimplex.objEquiv.symm (𝟙 n.unop)

/-- The complete inner coend inclusion applies the original coefficient operator represented by
a. -/
def diagonalCowedgeInclusion (X : SimplicialObject SimplicialSpace.{u}) (m : SimplexCategory) :
    (innerTensor (SSet.stdSimplex.obj m)).obj (X.obj (op m)) ⟶ innerDiagonalFunctor.obj X :=
  InducedCategory.homMk
    { app := fun k =>
        { app := fun n => ↾fun p =>
            (((X.map (SSet.stdSimplex.objEquiv p.2).op).hom.app k).app n) p.1
          naturality := by
            intro n l f
            ext p
            rcases p with ⟨x, a⟩
            let alpha := SSet.stdSimplex.objEquiv a
            have h := types_congr_hom (((X.map alpha.op).hom.app k).naturality f) x
            have moved : SSet.stdSimplex.objEquiv ((SSet.stdSimplex.obj m).map f a) =
                f.unop ≫ alpha := rfl
            change
                (((X.map (SSet.stdSimplex.objEquiv
                  ((SSet.stdSimplex.obj m).map f a)).op).hom.app k).app l)
                (((X.obj (op m)).diagram.obj k).map f x) = _
            rw [moved, op_comp, X.map_comp]
            exact congrArg (fun y => ((X.map f).hom.app k).app l y) h }
      naturality := by
        intro k l f
        apply NatTrans.ext
        funext n
        apply ConcreteCategory.hom_ext
        intro p
        rcases p with ⟨x, a⟩
        exact types_congr_hom
          (congrArg (fun t => t.app n)
              ((X.map (SSet.stdSimplex.objEquiv a).op).hom.naturality f)) x }

/-- Every coefficient and original outer/inner degree is retained in the inclusion formula. -/
theorem diagonalCowedgeInclusion_bidegree (X : SimplicialObject SimplicialSpace.{u})
    (m : SimplexCategory) (k n : SimplexCategoryᵒᵖ)
    (x : ((X.obj (op m)).diagram.obj k).obj n)
    (a : (SSet.stdSimplex.{u}.obj m).obj n) :
    ((diagonalCowedgeInclusion X m).hom.app k).app n (x, a) =
      (((X.map (SSet.stdSimplex.objEquiv a).op).hom.app k).app n) x := rfl

/-- The actual coend relation is exactly composition of the original coefficient operators. -/
theorem diagonalCowedgeInclusion_condition (X : SimplicialObject SimplicialSpace.{u})
    {i j : SimplexCategory} (f : i ⟶ j) :
    ((innerRealizationBifunctor X).map f.op).app i ≫ diagonalCowedgeInclusion X i =
      ((innerRealizationBifunctor X).obj (op j)).map f ≫ diagonalCowedgeInclusion X j := by
  apply InducedCategory.hom_ext
  apply NatTrans.ext
  funext k
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro p
  rcases p with ⟨x, a⟩
  have moved : SSet.stdSimplex.objEquiv ((SSet.stdSimplex.map f).app n a) =
      SSet.stdSimplex.objEquiv a ≫ f := rfl
  change (((X.map (SSet.stdSimplex.objEquiv a).op).hom.app k).app n)
      (((X.map f.op).hom.app k).app n x) =
    (((X.map (SSet.stdSimplex.objEquiv ((SSet.stdSimplex.map f).app n a)).op).hom.app k).app n) x
  rw [moved, op_comp, X.map_comp]
  rfl

/-- The actual coefficient/inner diagonal is a complete native cowedge. -/
def diagonalCowedge (X : SimplicialObject SimplicialSpace.{u}) :
    Cowedge (innerRealizationBifunctor X) :=
  Cowedge.mk (innerDiagonalFunctor.obj X) (diagonalCowedgeInclusion X)
    (fun {_ _} f => diagonalCowedgeInclusion_condition X f)

/-- Descending a cowedge evaluates its actual n-th inclusion at the original identity n-simplex. -/
def diagonalCowedgeDesc (X : SimplicialObject SimplicialSpace.{u})
    (c : Cowedge (innerRealizationBifunctor X)) : innerDiagonalFunctor.obj X ⟶ c.pt :=
  InducedCategory.homMk
    { app := fun k =>
        { app := fun n => ↾fun x => ((c.π n.unop).hom.app k).app n (x, identitySimplex n)
          naturality := by
            intro n l f
            ext x
            let moved := ((X.obj n).diagram.obj k).map f x
            have cow := congrArg (fun t => ((t.hom.app k).app l)
              (moved, identitySimplex l)) (c.condition f.unop)
            have nat := types_congr_hom (((c.π n.unop).hom.app k).naturality f)
              (x, identitySimplex n)
            have idmap : (SSet.stdSimplex.map f.unop).app l (identitySimplex l) =
                (SSet.stdSimplex.obj n.unop).map f (identitySimplex n) := by
              apply SSet.stdSimplex.objEquiv.injective
              change (𝟙 l.unop) ≫ f.unop = f.unop ≫ (𝟙 n.unop)
              simp only [Category.id_comp, Category.comp_id]
            change ((c.π l.unop).hom.app k).app l
                (((X.map f).hom.app k).app l moved, identitySimplex l) = _
            change ((c.π l.unop).hom.app k).app l
                (((X.map f).hom.app k).app l moved, identitySimplex l) =
              ((c.π n.unop).hom.app k).app l
                (moved, (SSet.stdSimplex.map f.unop).app l (identitySimplex l)) at cow
            rw [cow, idmap]
            exact nat }
      naturality := by
        intro k l f
        apply NatTrans.ext
        funext n
        apply ConcreteCategory.hom_ext
        intro x
        exact types_congr_hom
          (congrArg (fun t => t.app n) ((c.π n.unop).hom.naturality f))
          (x, identitySimplex n) }

/-- The complete identity-simplex formula for the universal descent. -/
theorem diagonalCowedgeDesc_bidegree (X : SimplicialObject SimplicialSpace.{u})
    (c : Cowedge (innerRealizationBifunctor X)) (k n : SimplexCategoryᵒᵖ)
    (x : ((X.obj n).diagram.obj k).obj n) :
    ((diagonalCowedgeDesc X c).hom.app k).app n x =
      ((c.π n.unop).hom.app k).app n (x, identitySimplex n) := rfl

/-- Every original coefficient inclusion is recovered by the descent, using its full coend
relation. -/
theorem diagonalCowedgeDesc_fac (X : SimplicialObject SimplicialSpace.{u})
    (c : Cowedge (innerRealizationBifunctor X)) (m : SimplexCategory) :
    diagonalCowedgeInclusion X m ≫ diagonalCowedgeDesc X c = c.π m := by
  apply InducedCategory.hom_ext
  apply NatTrans.ext
  funext k
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro p
  rcases p with ⟨x, a⟩
  have h := congrArg (fun t => ((t.hom.app k).app n) (x, identitySimplex n))
    (c.condition (SSet.stdSimplex.objEquiv a))
  have e : (SSet.stdSimplex.map (SSet.stdSimplex.objEquiv a)).app n (identitySimplex n) = a := by
    apply SSet.stdSimplex.objEquiv.injective
    change (𝟙 n.unop) ≫ SSet.stdSimplex.objEquiv a = SSet.stdSimplex.objEquiv a
    exact Category.id_comp _
  change ((c.π n.unop).hom.app k).app n
      ((((X.map (SSet.stdSimplex.objEquiv a).op).hom.app k).app n) x, identitySimplex n) =
    ((c.π m).hom.app k).app n ((x, (SSet.stdSimplex.map (SSet.stdSimplex.objEquiv a)).app n
      (identitySimplex n))) at h
  change ((c.π n.unop).hom.app k).app n
      ((((X.map (SSet.stdSimplex.objEquiv a).op).hom.app k).app n) x, identitySimplex n) =
    ((c.π m).hom.app k).app n (x, a)
  rw [e] at h
  exact h

/-- The original identity inclusion gives uniqueness at every actual outer/inner degree. -/
theorem diagonalCowedgeDesc_unique (X : SimplicialObject SimplicialSpace.{u})
    (c : Cowedge (innerRealizationBifunctor X))
    (f : innerDiagonalFunctor.obj X ⟶ c.pt)
    (h : ∀ m, diagonalCowedgeInclusion X m ≫ f = c.π m) : f = diagonalCowedgeDesc X c := by
  apply InducedCategory.hom_ext
  apply NatTrans.ext
  funext k
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  change ((X.obj n).diagram.obj k).obj n at x
  have eq := congrArg (fun t => ((t.hom.app k).app n) (x, identitySimplex n)) (h n.unop)
  have identity : ((diagonalCowedgeInclusion X n.unop).hom.app k).app n
      (x, identitySimplex n) = x := by
    have hi := diagonalCowedgeInclusion_bidegree X n.unop k n x (identitySimplex n)
    refine hi.trans ?_
    simp only [identitySimplex, Equiv.apply_symm_apply, op_id, X.map_id]
    rfl
  change ((f.hom.app k).app n)
      (((diagonalCowedgeInclusion X n.unop).hom.app k).app n (x, identitySimplex n)) =
    ((c.π n.unop).hom.app k).app n (x, identitySimplex n) at eq
  rw [identity] at eq
  change ((f.hom.app k).app n) x = ((c.π n.unop).hom.app k).app n (x, identitySimplex n)
  exact eq

/-- The whole original coefficient/INNER diagonal satisfies the native coend universal property. -/
def diagonalCowedgeIsColimit (X : SimplicialObject SimplicialSpace.{u}) :
    IsColimit (diagonalCowedge X) :=
  Multicofork.IsColimit.mk _ (diagonalCowedgeDesc X)
    (diagonalCowedgeDesc_fac X) (diagonalCowedgeDesc_unique X)

/-- The actual inner representable weighted coend is the literal original inner diagonal. -/
def innerRealizationDiagonalIso (X : SimplicialObject SimplicialSpace.{u}) :
    innerRealization X ≅ innerDiagonalFunctor.obj X :=
  (colimit.isColimit
      ((multispanIndexCoend (innerRealizationBifunctor X)).multispan)).coconePointUniqueUpToIso
    (diagonalCowedgeIsColimit X)

/-- Every forward coend inclusion is the original coefficient evaluation, not merely a vertex
map. -/
theorem innerRealizationDiagonalIso_hom_inclusion
    (X : SimplicialObject SimplicialSpace.{u}) (m : SimplexCategory) :
    coend.ι (innerRealizationBifunctor X) m ≫ (innerRealizationDiagonalIso X).hom =
      diagonalCowedgeInclusion X m :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit ((multispanIndexCoend (innerRealizationBifunctor X)).multispan))
    (diagonalCowedgeIsColimit X) (WalkingMultispan.right m)

/-- The inverse Iso recovers every same actual coefficient inclusion. -/
theorem innerRealizationDiagonalIso_inv_inclusion
    (X : SimplicialObject SimplicialSpace.{u}) (m : SimplexCategory) :
    diagonalCowedgeInclusion X m ≫ (innerRealizationDiagonalIso X).inv =
      coend.ι (innerRealizationBifunctor X) m :=
  IsColimit.comp_coconePointUniqueUpToIso_inv
    (colimit.isColimit ((multispanIndexCoend (innerRealizationBifunctor X)).multispan))
    (diagonalCowedgeIsColimit X) (WalkingMultispan.right m)

/-- A full map of coefficient diagrams gives the actual map of weighted coend bifunctors. -/
def innerRealizationBifunctorMap {X Y : SimplicialObject SimplicialSpace.{u}} (f : X ⟶ Y) :
    innerRealizationBifunctor X ⟶ innerRealizationBifunctor Y :=
  Functor.whiskerRight f (innerTensorBifunctor ⋙
    (Functor.whiskeringLeft SimplexCategory SSet.{u} SimplicialSpace.{u}).obj SSet.stdSimplex)

/-- All original coefficient and outer/inner maps commute with the universal inclusion. -/
theorem diagonalCowedgeInclusion_naturality {X Y : SimplicialObject SimplicialSpace.{u}}
    (f : X ⟶ Y) (m : SimplexCategory) :
    ((innerRealizationBifunctorMap f).app (op m)).app m ≫ diagonalCowedgeInclusion Y m =
      diagonalCowedgeInclusion X m ≫ innerDiagonalFunctor.map f := by
  apply InducedCategory.hom_ext
  apply NatTrans.ext
  funext k
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro p
  rcases p with ⟨x, a⟩
  exact congrArg (fun t => ((t.hom.app k).app n) x)
    (f.naturality (SSet.stdSimplex.objEquiv a).op).symm

/-- The whole coend/diagonal Iso is natural at the original complete diagram map. -/
theorem innerRealizationDiagonalIso_naturality {X Y : SimplicialObject SimplicialSpace.{u}}
    (f : X ⟶ Y) :
    coend.map (innerRealizationBifunctorMap f) ≫ (innerRealizationDiagonalIso Y).hom =
      (innerRealizationDiagonalIso X).hom ≫ innerDiagonalFunctor.map f := by
  let eX : coend (innerRealizationBifunctor X) ≅ innerDiagonalFunctor.obj X :=
    innerRealizationDiagonalIso X
  let eY : coend (innerRealizationBifunctor Y) ≅ innerDiagonalFunctor.obj Y :=
    innerRealizationDiagonalIso Y
  change coend.map (innerRealizationBifunctorMap f) ≫ eY.hom =
    eX.hom ≫ innerDiagonalFunctor.map f
  apply coend.hom_ext
  intro m
  have hX : coend.ι (innerRealizationBifunctor X) m ≫ eX.hom =
      diagonalCowedgeInclusion X m := innerRealizationDiagonalIso_hom_inclusion X m
  have hY : coend.ι (innerRealizationBifunctor Y) m ≫ eY.hom =
      diagonalCowedgeInclusion Y m := innerRealizationDiagonalIso_hom_inclusion Y m
  have h1 : coend.ι (innerRealizationBifunctor X) m ≫
        (coend.map (innerRealizationBifunctorMap f) ≫ eY.hom) =
      ((innerRealizationBifunctorMap f).app (op m)).app m ≫
        (coend.ι (innerRealizationBifunctor Y) m ≫ eY.hom) := by
    simpa only [Category.assoc] using
      congrArg (fun q => q ≫ eY.hom) (coend.ι_map (innerRealizationBifunctorMap f) m)
  have h2 : ((innerRealizationBifunctorMap f).app (op m)).app m ≫
        (coend.ι (innerRealizationBifunctor Y) m ≫ eY.hom) =
      ((innerRealizationBifunctorMap f).app (op m)).app m ≫ diagonalCowedgeInclusion Y m :=
    congrArg (fun q => ((innerRealizationBifunctorMap f).app (op m)).app m ≫ q) hY
  have h3 : ((innerRealizationBifunctorMap f).app (op m)).app m ≫
        diagonalCowedgeInclusion Y m =
      diagonalCowedgeInclusion X m ≫ innerDiagonalFunctor.map f :=
    diagonalCowedgeInclusion_naturality f m
  have h4 : coend.ι (innerRealizationBifunctor X) m ≫
        (eX.hom ≫ innerDiagonalFunctor.map f) =
      diagonalCowedgeInclusion X m ≫ innerDiagonalFunctor.map f := by
    exact (Category.assoc (coend.ι (innerRealizationBifunctor X) m)
      eX.hom (innerDiagonalFunctor.map f)).symm.trans
      (congrArg (fun q : ((innerRealizationBifunctor X).obj (op m)).obj m ⟶
          innerDiagonalFunctor.obj X => q ≫ innerDiagonalFunctor.map f) hX)
  exact h1.trans (h2.trans (h3.trans h4.symm))

/-- The original Raw20 Unit is exactly its INNER weighted-coend map surrounded by genuine Isos. -/
theorem innerRealization_original_raw_unit (W : SimplicialSpace.{u}) :
    (innerDiagonalConstIso W).inv ≫
        (innerRealizationDiagonalIso ((SimplicialObject.const SimplicialSpace.{u}).obj W)).inv ≫
        coend.map (innerRealizationBifunctorMap (RezkCompletionRaw.constantPowerSection W)) ≫
        (innerRealizationDiagonalIso (RezkCompletionRaw.powerDiagram W)).hom =
      RezkCompletionRaw.rawCompletionUnit W := by
  let A := (SimplicialObject.const SimplicialSpace.{u}).obj W
  let B := RezkCompletionRaw.powerDiagram W
  let eA : coend (innerRealizationBifunctor A) ≅ innerDiagonalFunctor.obj A :=
    innerRealizationDiagonalIso A
  let eB : coend (innerRealizationBifunctor B) ≅ innerDiagonalFunctor.obj B :=
    innerRealizationDiagonalIso B
  let e0 : innerDiagonalFunctor.obj A ≅ W := innerDiagonalConstIso W
  have h : coend.map (innerRealizationBifunctorMap (RezkCompletionRaw.constantPowerSection W)) ≫
      eB.hom = eA.hom ≫ innerDiagonalFunctor.map (RezkCompletionRaw.constantPowerSection W) :=
    innerRealizationDiagonalIso_naturality (RezkCompletionRaw.constantPowerSection W)
  change e0.inv ≫ eA.inv ≫
    coend.map (innerRealizationBifunctorMap (RezkCompletionRaw.constantPowerSection W)) ≫
      eB.hom = RezkCompletionRaw.rawCompletionUnit W
  rw [h, Iso.inv_hom_id_assoc]
  exact innerDiagonalFunctor_original_unit W

end SimplicialSpace.OriginalInnerRealization
