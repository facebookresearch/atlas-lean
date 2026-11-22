/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.CoproductWeakEquivalences
import MathlibExt.AlgebraicTopology.ModelCategory.Under
import MathlibExt.AlgebraicTopology.SimplicialSet.JoyalModelCategory
import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.FatConeAdjunction
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Categorical coproduct gluing under the original cone point

The named Joyal model and its existing Under model create the original
categorical weak maps. Every object under the original terminal point
is cofibrant: its structure map is monic. Brown's actual coproduct
theorem therefore applies to the structured cone coproducts.
The two existing cone adjunctions preserve those coproducts, and the
whole original comparison is retained on every original injection.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped Simplicial

namespace SSet.WalkingAdjunction

attribute [local instance] JoyalSSet.modelCategory

private theorem pointed_cofibrant
    (X : Under (JoyalSSet.ofSSet.obj (Δ[0] : SSet.{u}))) : IsCofibrant X := by
  let S := JoyalSSet.ofSSet.obj (Δ[0] : SSet.{u})
  have terminalPoint : IsTerminal S :=
    SSet.stdSimplex.isTerminalObj₀.isTerminalObj JoyalSSet.ofSSet (Δ[0] : SSet.{u})
  let _ : Mono X.hom := terminalPoint.mono_from X.hom
  have hcof : Cofibration X.hom := by
    rw [cofibration_iff]
    change JoyalSSet.modelCategory.categoryWithCofibrations.cofibrations X.hom
    rw [JoyalSSet.modelCategory_cofibrations]
    exact inferInstance
  let i : Under.mk (𝟙 S) ⟶ X := Under.homMk X.hom
  have hinit : IsInitial (Under.mk (𝟙 S)) :=
    StructuredArrow.mkIdInitial (T := 𝟭 JoyalSSet.{u}) (Y := S)
  exact (isCofibrant_iff_of_isInitial i hinit).mpr
    ((cofibrations_under_iff S i).mpr hcof)

private theorem pointed_weak_iff
    {X Y : Under (Δ[0] : SSet.{u})} (f : X ⟶ Y) :
    WeakEquivalence ((Under.post JoyalSSet.ofSSet).map f) ↔ categoricalEquivalences f.right := by
  rw [weakEquivalences_under_iff, weakEquivalence_iff]
  change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences
    (JoyalSSet.ofSSet.map f.right) ↔ categoricalEquivalences f.right
  rw [JoyalSSet.modelCategory_weakEquivalences]
  rfl

/-- An original categorical weak family under the same point is categorical on its supplied whole coproduct map. -/
theorem categoricalEquivalences_of_pointed_coproducts
    {J : Type u} {X Y : J → Under (Δ[0] : SSet.{u})}
    {cX : Cofan X} {cY : Cofan Y} (hX : IsColimit cX) (hY : IsColimit cY)
    (f : ∀ j, X j ⟶ Y j) (d : cX.pt ⟶ cY.pt)
    (hd : ∀ j, cX.inj j ≫ d = f j ≫ cY.inj j)
    (hf : ∀ j, categoricalEquivalences (f j).right) : categoricalEquivalences d.right := by
  let P := Under.post (X := (Δ[0] : SSet.{u})) JoyalSSet.ofSSet
  let _ : P.IsEquivalence :=
    (Under.postEquiv (X := (Δ[0] : SSet.{u})) JoyalSSet.equivalenceSSet.symm).isEquivalence_functor
  let _ : ∀ j, IsCofibrant (P.obj (X j)) := fun j => pointed_cofibrant _
  let _ : ∀ j, IsCofibrant (P.obj (Y j)) := fun j => pointed_cofibrant _
  let _ : ∀ j, WeakEquivalence (P.map (f j)) := fun j => (pointed_weak_iff _).mpr (hf j)
  have hcX : IsColimit (Cofan.mk (P.obj cX.pt) (fun j => P.map (cX.inj j))) :=
    isColimitCofanMkObjOfIsColimit P X (fun j => cX.inj j) hX
  have hcY : IsColimit (Cofan.mk (P.obj cY.pt) (fun j => P.map (cY.inj j))) :=
    isColimitCofanMkObjOfIsColimit P Y (fun j => cY.inj j) hY
  have hw : WeakEquivalence (P.map d) :=
    weakEquivalence_of_cofibrantCoproductCocones (fun j => P.map (f j)) hcX hcY (P.map d)
      (fun j => by
        change P.map (cX.inj j) ≫ P.map d = P.map (f j) ≫ P.map (cY.inj j)
        simpa only [Functor.map_comp] using congrArg P.map (hd j))
  exact (pointed_weak_iff d).mp hw

namespace FatCone

/-- The full fat/join comparison on an arbitrary original coproduct follows from the comparisons on its summands, with their common apex fixed. -/
theorem toJoin_of_coproduct {J : Type u} (X : J → SSet.{u})
    (hX : ∀ j, categoricalEquivalences (toJoin (X j))) :
    categoricalEquivalences (toJoin (∐ X)) := by
  let _ : PreservesColimitsOfShape (Discrete J) underFunctor.{u} :=
    preservesColimitsOfShape (Discrete J)
  let _ : PreservesColimitsOfShape (Discrete J) (joinOver (Δ[0] : SSet.{u})) :=
    (joinOverAdjunction (Δ[0] : SSet.{u})).leftAdjoint_preservesColimits.preservesColimitsOfShape
  have hF : IsColimit (Cofan.mk (underFunctor.obj (∐ X))
      (fun j => underFunctor.map (Limits.Sigma.ι X j))) :=
    isColimitCofanMkObjOfIsColimit underFunctor X (Limits.Sigma.ι X)
      (colimit.isColimit (Discrete.functor X))
  have hG : IsColimit (Cofan.mk ((joinOver (Δ[0] : SSet.{u})).obj (∐ X))
      (fun j => (joinOver (Δ[0] : SSet.{u})).map (Limits.Sigma.ι X j))) :=
    isColimitCofanMkObjOfIsColimit (joinOver (Δ[0] : SSet.{u})) X (Limits.Sigma.ι X)
      (colimit.isColimit (Discrete.functor X))
  exact categoricalEquivalences_of_pointed_coproducts hF hG
    (fun j => joinComparison.app (X j)) (joinComparison.app (∐ X))
    (fun j => joinComparison.naturality (Limits.Sigma.ι X j)) hX

end FatCone

end SSet.WalkingAdjunction
