/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.Comparison
import MathlibExt.AlgebraicTopology.SimplicialSet.RelativeJoinIntervalExtension

/-!
# Equivalence edges satisfy the actual Cartesian slice condition

The existing strict relative join-interval extension fills the original
structured boundary-join square. Its critical interval is precisely the
supplied edge by the source condition. The native join-slice correspondence
therefore proves the Cartesian boundary-lifting condition, retaining every
prescribed base simplex. The quasicategory-base hypothesis is genuine.
-/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet.CartesianEdge

/-- Every actual equivalence edge of an inner fibration over a quasicategory is p-cartesian. -/
theorem isPCartesian_of_isEquivalence {X B : SSet.{u}} (p : X ⟶ B)
    [InnerFibration p] [Quasicategory B] (e : (Δ[1] : SSet.{u}) ⟶ X)
    (he : (Edge.mk' (yonedaEquiv e)).IsEquivalence) : IsPCartesian p e := by
  apply (isPCartesian_iff_joinLifting p e).mpr
  intro n
  refine ⟨fun {u v} sq => ?_⟩
  let J := joinUnderPushoutObjObj (boundary.{u} n).ι (stdSimplex.δ (0 : Fin 2))
  have hsq : u.right ≫ p = J.ι ≫ v.right := congrArg Under.Hom.right sq.w
  have hc : joinInr (boundary.{u} n : SSet.{u}) (Δ[1] : SSet.{u}) ≫ J.inr ≫ u.right = e :=
    u.w
  have he' : (Edge.mk' (yonedaEquiv
      (joinInr (boundary.{u} n : SSet.{u}) (Δ[1] : SSet.{u}) ≫ J.inr ≫ u.right))).IsEquivalence :=
    hc.symm ▸ he
  obtain ⟨l, hl, hp⟩ := exists_fill_relativeJoinInterval_target_of_isEquivalence
    (boundary.{u} n).ι p u.right v.right hsq he'
  have hw : joinInr (Δ[n] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ l = e := by
    rw [← joinInr_comp_map (boundary.{u} n).ι (Δ[1] : SSet.{u}), ← J.inr_ι]
    simp only [Category.assoc]
    rw [hl]
    exact hc
  refine ⟨Under.homMk l hw, ?_, ?_⟩
  · apply StructuredArrow.hom_ext
    exact hl
  · apply StructuredArrow.hom_ext
    exact hp

end SSet.CartesianEdge
