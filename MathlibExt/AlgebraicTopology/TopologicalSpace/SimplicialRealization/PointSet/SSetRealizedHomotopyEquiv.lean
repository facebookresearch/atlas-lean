/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopy
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Realized equivalence from simplicial homotopy inverse maps

Suppose `f : X → Y` and `g : Y → X` have simplicial homotopies from their two
composites to the respective identities. Their realizations form a topological
homotopy equivalence with forward map `|f|` and inverse map `|g|`.
The two supplied composite-to-identity homotopies realize with those same
orientations, in every simplicial-set universe.
-/

@[expose] public section

universe u

open CategoryTheory

namespace SSet

/--
Maps `f` and `g` with simplicial homotopies `f ≫ g ~ id_X` and
`g ≫ f ~ id_Y` determine a homotopy equivalence between `|X|` and `|Y|`.
-/
noncomputable def realizedHomotopyEquiv (X Y : SSet.{u}) (f : X ⟶ Y) (g : Y ⟶ X)
    (Hleft : SSet.Homotopy (f ≫ g) (𝟙 X))
    (Hright : SSet.Homotopy (g ≫ f) (𝟙 Y)) :
    ContinuousMap.HomotopyEquiv (SSet.toTop.obj X) (SSet.toTop.obj Y) where
  toFun := (SSet.toTop.map f).hom
  invFun := (SSet.toTop.map g).hom
  left_inv := by
    have hL := SSet.realizeHomotopy X X (f ≫ g) (𝟙 X) Hleft
    have hL' : ContinuousMap.Homotopy
        ((SSet.toTop.map g).hom.comp (SSet.toTop.map f).hom)
        (ContinuousMap.id _) := by
      simpa [Functor.map_comp, TopCat.hom_comp, Functor.map_id, TopCat.hom_id] using hL
    exact ⟨hL'⟩
  right_inv := by
    have hR := SSet.realizeHomotopy Y Y (g ≫ f) (𝟙 Y) Hright
    have hR' : ContinuousMap.Homotopy
        ((SSet.toTop.map f).hom.comp (SSet.toTop.map g).hom)
        (ContinuousMap.id _) := by
      simpa [Functor.map_comp, TopCat.hom_comp, Functor.map_id, TopCat.hom_id] using hR
    exact ⟨hR'⟩

/--
The underlying forward function of the realized homotopy equivalence is the
realization of `f`.
-/
@[simp]
theorem coe_realizedHomotopyEquiv (X Y : SSet.{u}) (f : X ⟶ Y) (g : Y ⟶ X)
    (Hleft : SSet.Homotopy (f ≫ g) (𝟙 X))
    (Hright : SSet.Homotopy (g ≫ f) (𝟙 Y)) :
    ⇑(realizedHomotopyEquiv X Y f g Hleft Hright) = ⇑(SSet.toTop.map f).hom :=
  rfl

/--
The underlying forward function of the symmetric realized homotopy equivalence
is the realization of `g`.
-/
@[simp]
theorem coe_symm_realizedHomotopyEquiv (X Y : SSet.{u}) (f : X ⟶ Y) (g : Y ⟶ X)
    (Hleft : SSet.Homotopy (f ≫ g) (𝟙 X))
    (Hright : SSet.Homotopy (g ≫ f) (𝟙 Y)) :
    ⇑((realizedHomotopyEquiv X Y f g Hleft Hright).symm) = ⇑(SSet.toTop.map g).hom :=
  rfl

end SSet
