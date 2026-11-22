/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.EquivalenceReflection
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.Fibration
import MathlibExt.AlgebraicTopology.Quasicategory.EdgeCorrection
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.QuasicategoryFibrations

/-!
# Strict equivalence lifting for actual Cartesian fibrations

The supplied Cartesian lifts of base equivalences are proved equivalences
of the original total space. Inverting a lift of the original base inverse
and applying the existing inner-fibration edge correction gives strict
source-prescribed lifting. The existing genuine Joyal criterion then
identifies the same projection as a categorical fibration.
-/

noncomputable section
universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet

/-- The original target-prescribed Cartesian lift of a base equivalence is an equivalence. -/
theorem CartesianFibration.exists_equivalenceLift_target {X B : SSet.{u}} (p : X ⟶ B)
    [CartesianFibration p] [Quasicategory B] {x : X _⦋0⦌} {b : B _⦋0⦌}
    (g : Edge b (p.app _ x)) (hg : g.IsEquivalence) :
    ∃ (x' : X _⦋0⦌) (_ : p.app _ x' = b) (a : Edge x' x),
      a.IsEquivalence ∧ (a.map p).edge = g.edge := by
  obtain ⟨x', hx', a, ha, hb⟩ := CartesianFibration.lift (p := p) x b g
  have hmap : (a.map p).IsEquivalence := (Edge.isEquivalence_iff_of_edge_eq hb).mpr hg
  exact ⟨x', hx', a, CartesianEdge.isEquivalence_of_map p a ha hmap, hb⟩

/-- The original Cartesian projection has strict source-prescribed equivalence lifts. -/
theorem CartesianFibration.hasStrictEquivalenceLifting {X B : SSet.{u}} (p : X ⟶ B)
    [CartesianFibration p] [Quasicategory B] : HasStrictEquivalenceLifting p where
  exists_lift {x} {b} g hg := by
    let _ : Quasicategory X := CartesianFibration.quasicategory_source p
    obtain ⟨I⟩ := hg.nonempty_invStruct
    obtain ⟨x', hx', a, ha, hmap⟩ :=
      CartesianFibration.exists_equivalenceLift_target p I.inv I.invStructInv.isEquivalence
    obtain ⟨J⟩ := ha.nonempty_invStruct
    let f : Edge x x' := J.inv
    let IB : Edge.InvStruct (a.map p) := I.invStructInv.ofEq hmap.symm
    let _ : IsIso (a.map p).toHoHom := ha.map p
    have hf_inverse : (f.map p).toHoHom ≫ (a.map p).toHoHom =
        𝟙 (HomotopyCategory.mk (p.app _ x) : hoFunctor.obj B) := by
      rw [Edge.toHoHom_comp (J.invHomId.map p), Edge.map_id, Edge.toHoHom_id]
    have hw_inverse : IB.inv.toHoHom ≫ (a.map p).toHoHom =
        𝟙 (HomotopyCategory.mk (p.app _ x) : hoFunctor.obj B) := by
      rw [Edge.toHoHom_comp IB.invHomId, Edge.toHoHom_id]
    have hw : IB.inv.toHoHom = (f.map p).toHoHom :=
      (cancel_mono (a.map p).toHoHom).mp (hw_inverse.trans hf_inverse.symm)
    obtain ⟨f', hHo, hfmap⟩ := exists_edge_correction_of_innerFibration p
      (inferInstance : InnerFibration p) f IB.inv hw
    have hf' : f'.IsEquivalence := by
      change IsIso f'.toHoHom
      rw [hHo]
      exact J.invStructInv.isEquivalence
    refine ⟨x', hx', f', hf', ?_⟩
    exact hfmap.trans (show IB.inv.edge = g.edge from rfl)

/-- An actual Cartesian fibration over a quasicategory is a fibration in the genuine Joyal class. -/
theorem CartesianFibration.categoricalFibration {X B : SSet.{u}} (p : X ⟶ B)
    [CartesianFibration p] [Quasicategory B] : categoricalFibrations p := by
  exact (categoricalFibrations_iff_innerFibration_and_hasStrictEquivalenceLifting p).mpr
    ⟨inferInstance, CartesianFibration.hasStrictEquivalenceLifting p⟩

end SSet
