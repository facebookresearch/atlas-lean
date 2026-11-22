/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.FibrantUnderObjects
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown
import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.ConeQuillenAdjunctions

/-!
# Weak functoriality of the actual original join slice

The proved point-join adjunction is Quillen in the unchanged named
Joyal model. Brown's lemma applies to the actual weak morphism of
fibrant Under objects. Naturality of the existing Under equivalence
unit returns the original whole join-division map, and hence the
literal original slice map at its specified point.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped Simplicial

namespace SSet.WalkingAdjunction

attribute [local instance] JoyalSSet.modelCategory

/-- The actual right join-division functor preserves weak maps between
original structured quasicategory targets, keeping the fixed point. -/
theorem joinRightDivision_map_categoricalEquivalence
    {Q P : Under (Δ[0] : SSet.{u})}
    [Quasicategory Q.right] [Quasicategory P.right] (q : Q ⟶ P)
    (hq : categoricalEquivalences q.right) :
    categoricalEquivalences ((joinRightDivision (Δ[0] : SSet.{u})).map q) := by
  let E := ConeQuillenAdjunctions.pointEquivalence.{u}
  let U := E.functor.obj Q
  let V := E.functor.obj P
  let g : U ⟶ V := E.functor.map q
  let _ : IsFibrant U.right := by
    change IsFibrant (JoyalSSet.ofSSet.obj Q.right)
    exact (JoyalSSet.isFibrant_iff_quasicategory _).mpr
      (show Quasicategory Q.right from inferInstance)
  let _ : IsFibrant V.right := by
    change IsFibrant (JoyalSSet.ofSSet.obj P.right)
    exact (JoyalSSet.isFibrant_iff_quasicategory _).mpr
      (show Quasicategory P.right from inferInstance)
  let _ : IsFibrant U := (isFibrant_under_iff _ U).mpr inferInstance
  let _ : IsFibrant V := (isFibrant_under_iff _ V).mpr inferInstance
  let _ : WeakEquivalence g := (weakEquivalences_under_iff _ g).mpr
    ((weakEquivalence_iff g.right).mpr (by
      change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences
        (JoyalSSet.ofSSet.map q.right)
      rw [JoyalSSet.modelCategory_weakEquivalences]
      exact hq))
  let _ : ConeQuillenAdjunctions.joinAdjunction.{u}.IsQuillenAdjunction :=
    ConeQuillenAdjunctions.join_isQuillenAdjunction
  have hnamed : WeakEquivalence (ConeQuillenAdjunctions.joinRight.map g) :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant
      (adj := ConeQuillenAdjunctions.joinAdjunction) g
  have hback : categoricalEquivalences
      ((joinRightDivision (Δ[0] : SSet.{u})).map (E.inverse.map g)) := by
    have h := (weakEquivalence_iff _).mp hnamed
    change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences _ at h
    rw [JoyalSSet.modelCategory_weakEquivalences] at h
    exact h
  let eQ : Q ≅ E.inverse.obj U := E.unitIso.app Q
  let eP : P ≅ E.inverse.obj V := E.unitIso.app P
  have hn : eQ.hom ≫ E.inverse.map g = q ≫ eP.hom :=
    (E.unitIso.hom.naturality q).symm
  have hnat : (joinRightDivision (Δ[0] : SSet.{u})).map eQ.hom ≫
      (joinRightDivision (Δ[0] : SSet.{u})).map (E.inverse.map g) =
      (joinRightDivision (Δ[0] : SSet.{u})).map q ≫
        (joinRightDivision (Δ[0] : SSet.{u})).map eP.hom := by
    simpa only [Functor.map_comp] using
      congrArg (fun k => (joinRightDivision (Δ[0] : SSet.{u})).map k) hn
  have hs : categoricalEquivalences
      ((joinRightDivision (Δ[0] : SSet.{u})).map eQ.hom ≫
        (joinRightDivision (Δ[0] : SSet.{u})).map (E.inverse.map g)) :=
    (categoricalEquivalences.precomp_iff _ _ (categoricalEquivalences.of_isIso _)).mpr hback
  exact (categoricalEquivalences.postcomp_iff _ _
    (categoricalEquivalences.of_isIso _)).mp (hnat ▸ hs)

/-- The original join slice map of a categorical equivalence between
quasicategories is categorical weak at the actual image of its fixed point. -/
theorem sliceOver_map_categoricalEquivalence {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y]
    (t : (Δ[0] : SSet.{u}) ⟶ X) (p : X ⟶ Y) (hp : categoricalEquivalences p) :
    categoricalEquivalences (sliceOver.map X t p) := by
  let q : Under.mk t ⟶ Under.mk (t ≫ p) := Under.homMk p rfl
  let _ : Quasicategory (Under.mk t).right := by
    change Quasicategory X
    infer_instance
  let _ : Quasicategory (Under.mk (t ≫ p)).right := by
    change Quasicategory Y
    infer_instance
  have h := joinRightDivision_map_categoricalEquivalence q hp
  have heq : (joinRightDivision (Δ[0] : SSet.{u})).map q = sliceOver.map X t p := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    rfl
  exact heq ▸ h

end SSet.WalkingAdjunction
