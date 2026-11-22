/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CartesianCriticalCells

/-!
# Exact Cartesian edge detection by the native marked critical cells

The original marked projection over the maximally marked base has the
right lifting property against these critical cells exactly when every
supplied marked edge has the actual relative Cartesian slice condition.
Each filler retains the whole original horn and the full original base
simplex. This criterion imposes no quasicategory or marked-model premise.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- Native marked critical-cell lifting is exactly the actual Cartesian condition on supplied marked edges. -/
theorem cartesianCriticalCell_rlp_iff {Y : Marked.{u}} {B : SSet.{u}} (p : Y ⟶ max B) :
    (∀ n : ℕ, HasLiftingProperty (cartesianCriticalCell.{u} n) p) ↔
    ∀ e : Y.toSSet _⦋1⦌, e ∈ Y.marking →
      CartesianEdge.IsPCartesian p.hom (SSet.yonedaEquiv.symm e) := by
  constructor
  · intro hp e he
    apply (CartesianEdge.isPCartesian_iff_rightHornLifting p.hom (SSet.yonedaEquiv.symm e)).mpr
    intro n a b hab hedge
    have hmarked : a.app (op ⦋1⦌) (rightHornEdgeSimplex.{u} n) ∈ Y.marking := by
      have h : a.app (op ⦋1⦌) (rightHornEdgeSimplex.{u} n) = e := by
        change (rightHornEdge a).edge = e
        exact hedge.trans (Equiv.apply_symm_apply SSet.yonedaEquiv e)
      exact h.symm ▸ he
    let a' : cartesianCriticalSource n ⟶ Y := ofCartesianCriticalSource a hmarked
    let b' : cartesianCriticalTarget n ⟶ max B := toMax b
    let _ : HasLiftingProperty (cartesianCriticalCell.{u} n) p := hp n
    have sq : CommSq a' (cartesianCriticalCell.{u} n) p b' := ⟨Hom.ext hab⟩
    refine ⟨sq.lift.hom, congrArg Hom.hom sq.fac_left, congrArg Hom.hom sq.fac_right⟩
  · intro hp n
    refine ⟨fun {a b} sq => ?_⟩
    have hmarked := a.preserve (show rightHornEdgeSimplex.{u} n ∈
      (cartesianCriticalSource.{u} n).marking from Or.inr rfl)
    have hcart : CartesianEdge.IsPCartesian p.hom
        (SSet.yonedaEquiv.symm (rightHornEdge a.hom).edge) := hp _ hmarked
    obtain ⟨f, hf, hbase⟩ := CartesianEdge.exists_fill_rightHorn_of_isPCartesian a.hom b.hom
      (congrArg Hom.hom sq.w) hcart
    have hcritical : f.app (op ⦋1⦌) ((horn.{u} (n + 2) (Fin.last (n + 2))).ι.app (op ⦋1⦌)
        (rightHornEdgeSimplex.{u} n)) ∈ Y.marking := by
      have h := ConcreteCategory.congr_hom (congr_app hf (op ⦋1⦌)) (rightHornEdgeSimplex.{u} n)
      exact h.symm ▸ hmarked
    let f' : cartesianCriticalTarget n ⟶ Y := ofCartesianCriticalTarget f hcritical
    exact CommSq.HasLift.mk' ⟨f', Hom.ext hf, Hom.ext hbase⟩

end SSet.Marked
