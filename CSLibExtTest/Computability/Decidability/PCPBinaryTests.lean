/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.PCPBinary

@[expose] public section

/-!
# Tests for PCP over a binary alphabet
-/

set_option autoImplicit false

open Cslib.Decidability Cslib.Decidability.Post

namespace CSLibExtTest.Computability.Decidability.PCPBinary

/-- The unary code of the letter with index `2`. -/
example : unaryCode (fun n : ℕ ↦ n) 2 = [true, true, false] := rfl

/-- Unary codes of distinct words differ. -/
example : [0, 1].flatMap (unaryCode fun n : ℕ ↦ n) ≠ [1, 0].flatMap (unaryCode fun n : ℕ ↦ n) :=
  fun h ↦ by simpa using unaryHom_injective (e := fun n : ℕ ↦ n) (fun _ _ h ↦ h) h

/-- A solvable instance stays solvable under the unary code. -/
example : PCP (mapInstance (fun w : List ℕ ↦ w.flatMap (unaryCode fun n ↦ n)) [([0], [0])]) :=
  (pcp_map_iff (unaryHom_injective (e := fun n : ℕ ↦ n) fun _ _ h ↦ h) _).mpr
    ⟨[([0], [0])], by simp, by simp, rfl⟩

example : ¬TM2Decidable (PCP (α := Bool)) := not_tm2Decidable_pcp_bool

end CSLibExtTest.Computability.Decidability.PCPBinary
