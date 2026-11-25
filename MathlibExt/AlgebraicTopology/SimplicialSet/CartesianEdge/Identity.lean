/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.Comparison

/-!
# The actual relative edge classes over identity and isomorphism bases

The canonical join-slice lifting equivalence turns an isomorphism of
structured base diagrams into lifts against every boundary. Thus every
actual edge over an isomorphism base map is Cartesian and cocartesian.
This includes the identity fibration at every value universe.
-/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet

/-- Every actual edge over a base isomorphism is p-cartesian. -/
theorem CartesianEdge.isPCartesian_of_isIso {X B : SSet.{u}} (p : X ⟶ B) [IsIso p]
    (e : (Δ[1] : SSet.{u}) ⟶ X) : CartesianEdge.IsPCartesian p e := by
  apply (CartesianEdge.isPCartesian_iff_joinLifting p e).mpr
  intro n
  let _ : IsIso (Under.homMk p rfl : Under.mk e ⟶ Under.mk (e ≫ p)) := by
    let z : Under.mk e ≅ Under.mk (e ≫ p) := Under.isoMk (asIso p) rfl
    exact z.isIso_hom
  infer_instance

/-- Every actual edge over a base isomorphism is p-cocartesian. -/
theorem CocartesianEdge.isPCocartesian_of_isIso {X B : SSet.{u}} (p : X ⟶ B) [IsIso p]
    (e : (Δ[1] : SSet.{u}) ⟶ X) : CocartesianEdge.IsPCocartesian p e := by
  apply (CocartesianEdge.isPCocartesian_iff_joinLifting p e).mpr
  intro n
  let _ : IsIso (Under.homMk p rfl : Under.mk e ⟶ Under.mk (e ≫ p)) := by
    let z : Under.mk e ≅ Under.mk (e ≫ p) := Under.isoMk (asIso p) rfl
    exact z.isIso_hom
  infer_instance

/-- The identity fibration retains every actual edge as a Cartesian edge. -/
theorem CartesianEdge.isPCartesian_id (X : SSet.{u}) (e : (Δ[1] : SSet.{u}) ⟶ X) :
    CartesianEdge.IsPCartesian (𝟙 X) e := CartesianEdge.isPCartesian_of_isIso (𝟙 X) e

/-- The identity fibration retains every actual edge as a cocartesian edge. -/
theorem CocartesianEdge.isPCocartesian_id (X : SSet.{u}) (e : (Δ[1] : SSet.{u}) ⟶ X) :
    CocartesianEdge.IsPCocartesian (𝟙 X) e := CocartesianEdge.isPCocartesian_of_isIso (𝟙 X) e

end SSet
