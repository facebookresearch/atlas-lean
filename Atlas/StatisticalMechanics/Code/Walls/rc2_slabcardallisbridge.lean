/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































import Code.Walls.rc_core

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech













theorem rc2_countBoxBridge_iff_slabCardAll :
    rc_core_CountBoxBridge ↔ StatMech.poc_SlabCardAll :=
  rc_core_countBoxBridge_iff




theorem rc2_countBoxBridge_iff_forall_slab :
    rc_core_CountBoxBridge ↔
      ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n)))
        (k : ConfigSpace (Fin n) × ConfigSpace (Fin n)),
        #(StatMech.poc_slabBox A B k) ≤ #(StatMech.poc_slabImg A B k) :=
  Iff.rfl











theorem rc2_reimerWprobCore_of_bridge (h : rc_core_CountBoxBridge) : ReimerWprobCore :=
  rc_core_reimer_of_bridge h



theorem rc2_reimerWprobCore_of_slabCardAll (h : StatMech.poc_SlabCardAll) : ReimerWprobCore :=
  rc_core_reimer_of_bridge (rc2_countBoxBridge_iff_slabCardAll.mpr h)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in



theorem rc2_reimer_inequality_of_bridge (h : rc_core_CountBoxBridge) {E : Type*}
    [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1) (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  rc_core_reimer_inequality_of_bridge h hp A B








set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in




theorem rc2_slabCardAll_is_bridge :
    (rc_core_CountBoxBridge ↔ StatMech.poc_SlabCardAll) ∧
    (rc_core_CountBoxBridge → ReimerWprobCore) ∧
    (rc_core_CountBoxBridge → ∀ {E : Type*} [Fintype E] [DecidableEq E] {p : ℝ≥0}
      (hp : p ≤ 1) (A B : Set (ConfigSpace E)),
        (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
          ≤ (bernoulliProductMeasure (E := E) p hp).real A
            * (bernoulliProductMeasure (E := E) p hp).real B) := by
  refine ⟨rc2_countBoxBridge_iff_slabCardAll, rc2_reimerWprobCore_of_bridge, ?_⟩
  intro h E _ _ p hp A B
  exact rc2_reimer_inequality_of_bridge h hp A B

end StatMech.Walls
