/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.DirectedSimplexLifting
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.RightHornCriterion
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.EquivalenceLifting
import MathlibExt.AlgebraicTopology.SimplicialSet.LeftFibrationEquivalence

/-!
# Genuine categorical fibrations from directed horn lifting

A right fibration has actual Cartesian lifts of every original base edge.
Over a quasicategory, the existing equivalence-lifting criterion identifies
the same map as a genuine categorical fibration. Left fibrations use the
already proved strict equivalence lifting theorem.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet

/-- Every original edge of a right fibration satisfies the intrinsic Cartesian condition. -/
theorem RightFibration.isPCartesian {X B : SSet.{u}} (p : X ⟶ B) [RightFibration p]
    (e : (Δ[1] : SSet.{u}) ⟶ X) : CartesianEdge.IsPCartesian p e := by
  apply (CartesianEdge.isPCartesian_iff_rightHornLifting p e).mpr
  intro n a b h _
  let _ : HasLiftingProperty (horn (n + 2) (Fin.last (n + 2))).ι p :=
    RightFibration.hasLiftingProperty_horn (Fin.last (n + 2)) (by
      change 0 < n + 2
      omega)
  let sq : CommSq a (horn (n + 2) (Fin.last (n + 2))).ι p b := ⟨h⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- The actual right-fibration map has original target-prescribed Cartesian edge lifts. -/
theorem RightFibration.cartesianFibration {X B : SSet.{u}} (p : X ⟶ B)
    [RightFibration p] : CartesianFibration p where
  toInnerFibration := inferInstance
  lift y b e := by
    let _ : HasLiftingProperty (stdSimplex.δ.{u} (0 : Fin 2)) p :=
      RightFibration.hasLiftingProperty_target p
    have h : yonedaEquiv.symm y ≫ p = stdSimplex.δ (0 : Fin 2) ≫ yonedaEquiv.symm e.edge := by
      rw [yonedaEquiv_symm_comp, stdSimplex.δ_comp_yonedaEquiv_symm, e.tgt_eq]
    let sq : CommSq (yonedaEquiv.symm y) (stdSimplex.δ (0 : Fin 2)) p
        (yonedaEquiv.symm e.edge) := ⟨h⟩
    let x : X _⦋0⦌ := X.δ 1 (yonedaEquiv sq.lift)
    have ht : X.δ 0 (yonedaEquiv sq.lift) = y := by
      rw [← stdSimplex.yonedaEquiv_δ_comp, sq.fac_left, Equiv.apply_symm_apply]
    let a : Edge x y := Edge.mk (yonedaEquiv sq.lift) rfl ht
    have hm : (a.map p).edge = e.edge := by
      change p.app _ (yonedaEquiv sq.lift) = e.edge
      rw [← yonedaEquiv_comp, sq.fac_right, Equiv.apply_symm_apply]
    have hx : p.app _ x = b := by
      dsimp only [x]
      rw [δ_naturality_apply, ← yonedaEquiv_comp, sq.fac_right,
        Equiv.apply_symm_apply, e.src_eq]
    exact ⟨x, hx, a, RightFibration.isPCartesian p _, hm⟩

/-- The same original right fibration is a genuine categorical fibration over a quasicategory. -/
theorem RightFibration.categoricalFibration {X B : SSet.{u}} (p : X ⟶ B)
    [RightFibration p] [Quasicategory B] : categoricalFibrations p := by
  let _ : CartesianFibration p := RightFibration.cartesianFibration p
  exact CartesianFibration.categoricalFibration p

/-- The same original left fibration is a genuine categorical fibration over a quasicategory. -/
theorem LeftFibration.categoricalFibration {X B : SSet.{u}} (p : X ⟶ B)
    [LeftFibration p] [Quasicategory B] : categoricalFibrations p :=
  (categoricalFibrations_iff_innerFibration_and_hasStrictEquivalenceLifting p).mpr
    ⟨LeftFibration.innerFibration, hasStrictEquivalenceLifting_of_leftFibration p⟩

end SSet
