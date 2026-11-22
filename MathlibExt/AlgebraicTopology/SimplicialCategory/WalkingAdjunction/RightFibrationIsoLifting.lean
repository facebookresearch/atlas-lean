/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Quasicategory.RightFibration

/-!
# Exact equivalence-edge lifting for right fibrations

The existing target-prescribed left-fibration lift, applied to the
opposite original map, gives a source-prescribed right-fibration lift.
The result retains the selected source, the literal target equality,
and the entire original image edge, rather than only its homotopy class.
-/

@[expose] public section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet

/-- A right fibration over a quasicategory lifts each original equivalence
edge with its prescribed source and exact image simplex. -/
theorem hasStrictEquivalenceLifting_of_rightFibration {X Y : SSet.{u}}
    (p : X ⟶ Y) [RightFibration p] [Quasicategory Y] :
    HasStrictEquivalenceLifting p := by
  let _ : Quasicategory X := quasicategory_of_rightFibration p
  let _ : Quasicategory X.op := quasicategory_op X
  let _ : Quasicategory Y.op := quasicategory_op Y
  apply (hasStrictEquivalenceLifting_iff p).mpr
  intro x₀ y₁ g hg
  have hsource : (opFunctor.map p).app _ (opObjEquiv.symm x₀) =
      opObjEquiv.symm (p.app _ x₀) := by
    rw [opFunctor_map, Equiv.apply_symm_apply]
  obtain ⟨x₁op, hx₁op, fop, hfop, hmapop⟩ :=
    LeftFibration.exists_isoLift_target (F := opFunctor.map p)
      (u := g.op) hg.op hsource
  have htarget : p.app _ (opObjEquiv x₁op) = y₁ :=
    opObjEquiv.symm.injective ((opFunctor_map p x₁op).symm.trans hx₁op)
  let f : Edge x₀ (opObjEquiv x₁op) := Edge.mk fop.unop.edge
    (fop.unop.src_eq.trans (Equiv.apply_symm_apply opObjEquiv x₀))
    fop.unop.tgt_eq
  have hf : f.IsEquivalence :=
    (Edge.isEquivalence_iff_of_edge_eq (show f.edge = fop.unop.edge from rfl)).mpr
      hfop.unop
  have hmap : (f.map p).edge = g.edge := by
    have h := congrArg (opObjEquiv (X := Y) (n := op ⦋1⦌)) hmapop
    rw [Edge.map_edge, opFunctor_map, Edge.op_edge,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    exact h
  exact ⟨opObjEquiv x₁op, htarget, f, hf, hmap⟩

end SSet
