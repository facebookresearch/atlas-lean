/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceIhomComponents
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivWeakHomotopy

/-!
# Original internal-Hom inverse components give realization weakness

An actual inverse pair of original simplicial maps, whose two composites
lie in the original identity components of their full internal Homs,
realizes to a genuine topological homotopy equivalence. The native
realization homotopies and original weak class retain every map and
coefficient universe. No Kan condition or weak-map outcome is a premise.
This supplies the scalar inverse step needed for actual component-object
transport in the varying-object enriched Dwyer–Kan weak class.
-/

noncomputable section
universe u
open CategoryTheory MonoidalClosed
open scoped Simplicial

namespace SSet

/-- Original full internal-Hom component equality realizes to an actual homotopy of the SAME original maps. -/
theorem realizationHomotopy_nonempty_of_ihom_component_eq {X Y : SSet.{u}} {f g : X ⟶ Y}
    (h : π₀.mk (ihomVertexEquiv X Y f) = π₀.mk (ihomVertexEquiv X Y g)) :
    Nonempty (TopCat.Homotopy (SSet.toTop.map f) (SSet.toTop.map g)) := by
  let V := ihomVertexEquiv X Y
  have transport (x y : ((ihom X).obj Y) _⦋0⦌)
      (hxy : Relation.EqvGen (π₀Rel (X := (ihom X).obj Y)) x y) :
      Nonempty (TopCat.Homotopy (SSet.toTop.map (V.symm x)) (SSet.toTop.map (V.symm y))) := by
    induction hxy with
    | rel x y hxy =>
      obtain ⟨e⟩ := hxy
      have e' : ((ihom X).obj Y).Edge (V (V.symm x)) (V (V.symm y)) := by
        simpa only [Equiv.apply_symm_apply] using e
      exact ⟨SSet.realizeHomotopy X Y (V.symm x) (V.symm y) (Homotopy.ofIhomEdge e')⟩
    | refl x => exact ⟨ContinuousMap.Homotopy.refl _⟩
    | symm x y _ ih => exact ⟨ih.some.symm⟩
    | trans x y z _ _ ihxy ihyz => exact ⟨ihxy.some.trans ihyz.some⟩
  have chain : Relation.EqvGen (π₀Rel (X := (ihom X).obj Y)) (V f) (V g) :=
    (π₀.mk_eq_mk_iff (V f) (V g)).mp h
  simpa only [Equiv.symm_apply_apply] using transport (V f) (V g) chain

/-- A literal original internal-Hom inverse pair gives a realized homotopy equivalence with the SAME forward and
inverse maps. -/
def realizedIhomInverseEquivalence {X Y : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hX : π₀.mk (ihomVertexEquiv X X (f ≫ g)) = π₀.mk (ihomVertexEquiv X X (𝟙 X)))
    (hY : π₀.mk (ihomVertexEquiv Y Y (g ≫ f)) = π₀.mk (ihomVertexEquiv Y Y (𝟙 Y))) :
    ContinuousMap.HomotopyEquiv (SSet.toTop.obj X) (SSet.toTop.obj Y) where
  toFun := (SSet.toTop.map f).hom
  invFun := (SSet.toTop.map g).hom
  left_inv := by
    change Nonempty (TopCat.Homotopy (SSet.toTop.map f ≫ SSet.toTop.map g) (𝟙 (SSet.toTop.obj X)))
    rw [← SSet.toTop.map_comp f g, ← SSet.toTop.map_id X]
    exact realizationHomotopy_nonempty_of_ihom_component_eq hX
  right_inv := by
    change Nonempty (TopCat.Homotopy (SSet.toTop.map g ≫ SSet.toTop.map f) (𝟙 (SSet.toTop.obj Y)))
    rw [← SSet.toTop.map_comp g f, ← SSet.toTop.map_id Y]
    exact realizationHomotopy_nonempty_of_ihom_component_eq hY

/-- The actual original forward map, with both full inverse component equations, is realization weak in EVERY
original coefficient universe. -/
theorem realizationWeakEquivalences_of_ihom_inverse {X Y : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hX : π₀.mk (ihomVertexEquiv X X (f ≫ g)) = π₀.mk (ihomVertexEquiv X X (𝟙 X)))
    (hY : π₀.mk (ihomVertexEquiv Y Y (g ≫ f)) = π₀.mk (ihomVertexEquiv Y Y (𝟙 Y))) :
    realizationWeakEquivalences f := by
  change TopCat.weakHomotopyEquivalences (SSet.toTop.map f)
  exact TopCat.homotopyEquiv_toFun_mem (realizedIhomInverseEquivalence f g hX hY)

/-- Both SAME original maps are realization weak; no Kan replacement or weak outcome has been assumed. -/
theorem realizationWeakEquivalences_both_of_ihom_inverse {X Y : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hX : π₀.mk (ihomVertexEquiv X X (f ≫ g)) = π₀.mk (ihomVertexEquiv X X (𝟙 X)))
    (hY : π₀.mk (ihomVertexEquiv Y Y (g ≫ f)) = π₀.mk (ihomVertexEquiv Y Y (𝟙 Y))) :
    realizationWeakEquivalences f ∧ realizationWeakEquivalences g :=
  ⟨realizationWeakEquivalences_of_ihom_inverse f g hX hY,
    realizationWeakEquivalences_of_ihom_inverse g f hY hX⟩

end SSet
