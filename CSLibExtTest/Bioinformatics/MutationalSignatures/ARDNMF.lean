/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Bioinformatics.MutationalSignatures.ARDNMF
import Mathlib.Tactic.NormNum

/-! Tests for ARD-NMF: a `1 × 1 × 1` instance of the updates and their monotonicity
(non-vacuity witness), the relevance update and its floor, and pruning. -/

namespace CSLibExtTest.Bioinformatics.MutationalSignatures.ARDNMF

open Cslib.Bioinformatics.MutationalSignatures.ARDNMF

/-- `V = W = H = λ = φ = 1`: the `H` update halves `H`. -/
example : updateH (F := Unit) (K := Unit) (N := Unit) 1 (fun _ _ => 1) (fun _ _ => 1)
    (fun _ => 1) (fun _ _ => 1) () () = 1 / 2 := by
  simp [updateH, recon]; norm_num

example : objectiveH (F := Unit) (K := Unit) (N := Unit) 1 (fun _ _ => 1) (fun _ _ => 1)
    (fun _ => 1) (updateH (F := Unit) 1 (fun _ _ => 1) (fun _ _ => 1) (fun _ => 1) fun _ _ => 1) ≤
    objectiveH (F := Unit) (K := Unit) (N := Unit) 1 (fun _ _ => 1) (fun _ _ => 1) (fun _ => 1)
      fun _ _ => 1 :=
  objectiveH_updateH_le one_pos (fun _ => one_pos) (fun _ _ => zero_le_one)
    (fun _ _ => zero_le_one) (fun _ => ⟨(), one_pos⟩) (fun _ _ => one_pos)

example : objectiveW (F := Unit) (K := Unit) (N := Unit) 1 (fun _ _ => 1) (fun _ _ => 1)
    (fun _ => 1) (updateW (N := Unit) 1 (fun _ _ => 1) (fun _ _ => 1) (fun _ => 1) fun _ _ => 1) ≤
    objectiveW (F := Unit) (K := Unit) (N := Unit) 1 (fun _ _ => 1) (fun _ _ => 1) (fun _ => 1)
      fun _ _ => 1 :=
  objectiveW_updateW_le one_pos (fun _ => one_pos) (fun _ _ => zero_le_one)
    (fun _ _ => zero_le_one) (fun _ => ⟨(), one_pos⟩) (fun _ _ => one_pos)

/-- `KL(0 | y) = y`: zero data entries are scored correctly. -/
example : klDiv 0 3 = 3 := by simp [klDiv]

/-- Relevance `(1 + 1 + 1) / 3 = 1`. -/
example : relevance (F := Unit) (K := Unit) (N := Unit) (fun _ _ => 1) (fun _ _ => 1) 1 3 () =
    1 := by
  simp [relevance]; norm_num

example : IsMinOn (fun l => 3 / l + 3 * Real.log l) (Set.Ioi 0) (3 / 3) :=
  relevance_isMinOn (by norm_num) (by norm_num)

/-- A zero component sits exactly at the floor `b / c`. -/
example : relevance (F := Unit) (K := Unit) (N := Unit) (fun _ _ => 0) (fun _ _ => 0) 1 3 () =
    1 / 3 :=
  (relevance_eq_floor_iff (by norm_num) (fun _ _ => le_rfl) (fun _ _ => le_rfl) ()).2
    ⟨fun _ => rfl, fun _ => rfl⟩

example : updateH (F := Unit) (K := Unit) (N := Unit) 1 (fun _ _ => 1) (fun _ _ => 1)
    (fun _ => 1) (fun _ _ => 0) () () = 0 :=
  updateH_eq_zero _ _ _ _ rfl

end CSLibExtTest.Bioinformatics.MutationalSignatures.ARDNMF
