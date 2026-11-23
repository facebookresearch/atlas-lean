/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.CWComplex.Transport

/-!
# Universe lifting of the actual classical CW structure

The original characteristic partial equivalences are postcomposed with the
canonical lift equivalence. Every original finite frontier family, closed-set
criterion and covering is transported explicitly. The source topology and
finite-dimensional characteristic disks remain the original ones.
-/

public section

noncomputable section
set_option autoImplicit false

open Set Function Topology

universe u v

namespace Topology.CWComplex

/-- Lift the complete original CW structure by the canonical homeomorphism,
retaining the literal universe lifts of its original cell identifiers. -/
@[expose, instance_reducible] def uliftCWComplex (X : Type u) [TopologicalSpace X]
    [CWComplex (Set.univ : Set X)] :
    CWComplex (Set.univ : Set (ULift.{v} X)) :=
  transportULift (inferInstance : CWComplex (Set.univ : Set X)) Homeomorph.ulift.symm

/-- The complete characteristic maps are the literal lifts of the old maps. -/
@[simp] theorem uliftCWComplex_map (X : Type u) [TopologicalSpace X]
    [CWComplex (Set.univ : Set X)] (n : ℕ)
    (j : ULift.{v} ((inferInstance : CWComplex (Set.univ : Set X)).cell n))
    (z : Fin n → ℝ) :
    (uliftCWComplex X).map n j z =
      ULift.up ((inferInstance : CWComplex (Set.univ : Set X)).map n j.down z) := rfl

/-- The lifted zero cell is the actual old identifier and point in every coordinate. -/
theorem uliftCWComplex_zeroCell (X : Type u) [TopologicalSpace X]
    [CWComplex (Set.univ : Set X)] (x : X)
    (j : (inferInstance : CWComplex (Set.univ : Set X)).cell 0)
    (hj : (inferInstance : CWComplex (Set.univ : Set X)).map 0 j ![] = x) :
    ∃ j' : (uliftCWComplex X : CWComplex (Set.univ : Set (ULift.{v} X))).cell 0,
      ∀ z : Fin 0 → ℝ, (uliftCWComplex X).map 0 j' z = ULift.up x := by
  refine ⟨ULift.up j, ?_⟩
  intro z
  have hz : z = ![] := Subsingleton.elim _ _
  rw [uliftCWComplex_map, hz, hj]

end Topology.CWComplex

end
