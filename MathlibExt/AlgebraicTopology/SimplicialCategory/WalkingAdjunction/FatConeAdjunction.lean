/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.FatConeFunctoriality

/-!
# The native structured fat-cone adjunction

The actual fat-cone pushout and the existing fixed-target internal
path slice form an adjunction. Its Hom equivalence keeps the whole
original cylinder and apex maps; both naturality equations use the
literal original source and ambient maps. The native adjunction
therefore preserves colimits of every shape for which they exist,
without introducing a smallness hypothesis or fibrancy certificate.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open scoped Simplicial

namespace SSet.WalkingAdjunction.FatCone

/-- The actual path-slice map induced by a morphism of the original structured targets. -/
def pathMap {P Q : Under (Δ[0] : SSet.{u})} (q : P ⟶ Q) : pathSliceOver P.hom ⟶ pathSliceOver Q.hom :=
  pathSliceOver.lift Q.hom (pathSliceOver.fst P.hom ≫ (ihom (Δ[1] : SSet.{u})).map q.right) (by
    rw [Category.assoc, pathSpace_map_eval₁, ← Category.assoc, pathSliceOver.condition,
      Category.assoc, q.w, pathSliceOver.snd_eq])

/-- The entire underlying path map is the original ambient internal-Hom map. -/
theorem pathMap_fst {P Q : Under (Δ[0] : SSet.{u})} (q : P ⟶ Q) :
    pathMap q ≫ pathSliceOver.fst Q.hom =
      pathSliceOver.fst P.hom ≫ (ihom (Δ[1] : SSet.{u})).map q.right := pathSliceOver.lift_fst _ _ _

/-- The existing path slices as an actual functor on the original structured targets. -/
def pathFunctor : Under (Δ[0] : SSet.{u}) ⥤ SSet.{u} where
  obj P := pathSliceOver P.hom
  map q := pathMap q
  map_id P := by
    apply pathSliceOver.hom_ext P.hom
    rw [pathMap_fst, Under.id_right, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  map_comp q r := by
    apply pathSliceOver.hom_ext _
    rw [pathMap_fst, Under.comp_right, CategoryTheory.Functor.map_comp]
    rw [Category.assoc (pathMap q) (pathMap r), pathMap_fst r,
      ← Category.assoc (pathMap q), pathMap_fst q, Category.assoc]

/-- The native full-map Hom equivalence of the original fat cone and original fixed-target path slice. -/
def homEquiv (X : SSet.{u}) (P : Under (Δ[0] : SSet.{u})) :
    (underFunctor.obj X ⟶ P) ≃ (X ⟶ pathFunctor.obj P) :=
  ({ toFun q := ⟨q.right, q.w⟩
     invFun q := Under.homMk q.1 q.2
     left_inv _q := StructuredArrow.hom_ext _ _ rfl
     right_inv _q := Subtype.ext rfl } :
      (underFunctor.obj X ⟶ P) ≃ {q : obj X ⟶ P.right // apex X ≫ q = P.hom}).trans
    ((pathEquiv X P.right P.hom).trans (pathSliceOver.homEquiv P.hom X).symm)

/-- The Hom equivalence reads the identical whole original internal path of the fat-cone map. -/
theorem homEquiv_fst (X : SSet.{u}) (P : Under (Δ[0] : SSet.{u})) (q : underFunctor.obj X ⟶ P) :
    homEquiv X P q ≫ pathSliceOver.fst P.hom = toPath q.right := pathSliceOver.lift_fst _ _ _

/-- The inverse Hom equivalence retains the entire supplied path as the original cylinder map. -/
theorem homEquiv_symm_cylinder (X : SSet.{u}) (P : Under (Δ[0] : SSet.{u})) (p : X ⟶ pathFunctor.obj P) :
    cylinder X ≫ ((homEquiv X P).symm p).right =
      (β_ X (Δ[1] : SSet.{u})).hom ≫ MonoidalClosed.uncurry (p ≫ pathSliceOver.fst P.hom) :=
  cylinder_desc _ _ _

/-- The inverse Hom equivalence fixes the identical original structured apex. -/
theorem homEquiv_symm_apex (X : SSet.{u}) (P : Under (Δ[0] : SSet.{u})) (p : X ⟶ pathFunctor.obj P) :
    apex X ≫ ((homEquiv X P).symm p).right = P.hom := ((homEquiv X P).symm p).w

/-- The Hom equivalence commutes with the entire original source map. -/
theorem homEquiv_naturality_left {X Y : SSet.{u}} (f : X ⟶ Y) (P : Under (Δ[0] : SSet.{u}))
    (q : underFunctor.obj Y ⟶ P) :
    homEquiv X P (underFunctor.map f ≫ q) = f ≫ homEquiv Y P q := by
  have hl := homEquiv_fst X P (underFunctor.map f ≫ q)
  have hr := homEquiv_fst Y P q
  have ht : toPath (underFunctor.map f ≫ q).right = f ≫ toPath q.right := toPath_precomp f q.right
  exact pathSliceOver.hom_ext P.hom
    (hl.trans (ht.trans ((congrArg (fun p => f ≫ p) hr.symm).trans (Category.assoc _ _ _).symm)))

/-- The inverse Hom equivalence commutes with the identical original source map. -/
theorem homEquiv_naturality_left_symm {X Y : SSet.{u}} (f : X ⟶ Y) (P : Under (Δ[0] : SSet.{u}))
    (p : Y ⟶ pathFunctor.obj P) :
    (homEquiv X P).symm (f ≫ p) = underFunctor.map f ≫ (homEquiv Y P).symm p := by
  apply (homEquiv X P).injective
  rw [Equiv.apply_symm_apply, homEquiv_naturality_left, Equiv.apply_symm_apply]

/-- The Hom equivalence commutes with the entire original map of structured targets. -/
theorem homEquiv_naturality_right (X : SSet.{u}) {P Q : Under (Δ[0] : SSet.{u})}
    (p : underFunctor.obj X ⟶ P) (q : P ⟶ Q) :
    homEquiv X Q (p ≫ q) = homEquiv X P p ≫ pathFunctor.map q := by
  have hl := homEquiv_fst X Q (p ≫ q)
  have hr := homEquiv_fst X P p
  have ht : toPath (p ≫ q).right = toPath p.right ≫ (ihom (Δ[1] : SSet.{u})).map q.right :=
    toPath_postcomp p.right q.right
  have hm := pathMap_fst q
  exact pathSliceOver.hom_ext Q.hom
    (hl.trans (ht.trans ((congrArg (fun r => r ≫ (ihom (Δ[1] : SSet.{u})).map q.right) hr.symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun r => homEquiv X P p ≫ r) hm.symm).trans (Category.assoc _ _ _).symm)))))

/-- The genuine native adjunction of the original fat-cone and path-slice functors. -/
def adjunction : underFunctor.{u} ⊣ pathFunctor :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv
      homEquiv_naturality_left_symm := fun f p => homEquiv_naturality_left_symm f _ p
      homEquiv_naturality_right := fun p q => homEquiv_naturality_right _ p q }

/-- The actual adjunction supplies colimit preservation at every original diagram shape. -/
theorem preservesColimitsOfShape (J : Type v) [Category.{w} J] : PreservesColimitsOfShape J underFunctor.{u} :=
  adjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape

end SSet.WalkingAdjunction.FatCone
