/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CocartesianCriticalCells

/-!
# Exact Cocartesian edge detection by the native marked critical cells

The original marked projection over the maximally marked base has the
right lifting property against these critical cells exactly when every
supplied marked edge has the actual relative Cocartesian slice condition.
Each filler retains the whole original horn and the full original base
simplex. This criterion imposes no quasicategory or marked-model premise.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- Native marked critical-cell lifting is exactly the actual Cocartesian condition on supplied marked edges. -/
theorem cocartesianCriticalCell_rlp_iff {Y : Marked.{u}} {B : SSet.{u}} (p : Y ⟶ max B) :
    (∀ n : ℕ, HasLiftingProperty (cocartesianCriticalCell.{u} n) p) ↔
    ∀ e : Y.toSSet _⦋1⦌, e ∈ Y.marking →
      CocartesianEdge.IsPCocartesian p.hom (SSet.yonedaEquiv.symm e) := by
  constructor
  · intro hp e he
    apply (CocartesianEdge.isPCocartesian_iff_leftHornLifting p.hom (SSet.yonedaEquiv.symm e)).mpr
    intro n a b hab hedge
    have hmarked : a.app (op ⦋1⦌) (leftHornEdgeSimplex.{u} n) ∈ Y.marking := by
      have h : a.app (op ⦋1⦌) (leftHornEdgeSimplex.{u} n) = e := by
        change (leftHornEdge a).edge = e
        exact hedge.trans (Equiv.apply_symm_apply SSet.yonedaEquiv e)
      exact h.symm ▸ he
    let a' : cocartesianCriticalSource n ⟶ Y := ofCocartesianCriticalSource a hmarked
    let b' : cocartesianCriticalTarget n ⟶ max B := toMax b
    let _ : HasLiftingProperty (cocartesianCriticalCell.{u} n) p := hp n
    have sq : CommSq a' (cocartesianCriticalCell.{u} n) p b' := ⟨Hom.ext hab⟩
    refine ⟨sq.lift.hom, congrArg Hom.hom sq.fac_left, congrArg Hom.hom sq.fac_right⟩
  · intro hp n
    refine ⟨fun {a b} sq => ?_⟩
    have hmarked := a.preserve (show leftHornEdgeSimplex.{u} n ∈
      (cocartesianCriticalSource.{u} n).marking from Or.inr rfl)
    have hcart : CocartesianEdge.IsPCocartesian p.hom
        (SSet.yonedaEquiv.symm (leftHornEdge a.hom).edge) := hp _ hmarked
    obtain ⟨f, hf, hbase⟩ := CocartesianEdge.exists_fill_leftHorn_of_isPCocartesian a.hom b.hom
      (congrArg Hom.hom sq.w) hcart
    have hcritical : f.app (op ⦋1⦌) ((horn.{u} (n + 2) ((0 : Fin (n + 3)))).ι.app (op ⦋1⦌)
        (leftHornEdgeSimplex.{u} n)) ∈ Y.marking := by
      have h := ConcreteCategory.congr_hom (congr_app hf (op ⦋1⦌)) (leftHornEdgeSimplex.{u} n)
      exact h.symm ▸ hmarked
    let f' : cocartesianCriticalTarget n ⟶ Y := ofCocartesianCriticalTarget f hcritical
    exact CommSq.HasLift.mk' ⟨f', Hom.ext hf, Hom.ext hbase⟩

end SSet.Marked
