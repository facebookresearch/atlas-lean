/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.Enumerators
public import CSLibExt.Computability.Decidability.Undecidable

@[expose] public section

/-!
# Tests for enumerators
-/

set_option autoImplicit false

open Cslib.Decidability

namespace CSLibExtTest.Computability.Decidability.Enumerators

/-- The enumerator printing `2 * n` at step `n` enumerates the even numbers, so they are
recognizable. -/
theorem enumerates_even : Enumerates (fun n : ℕ ↦ some (2 * n)) fun m ↦ Even m := fun m ↦ by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp [two_mul]⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by simp only [Option.some.injEq] at hn; omega⟩

example : TM2Recognizable fun m : ℕ ↦ Even m :=
  tm2Recognizable_of_enumerates
    (Primrec.option_some.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)).to_comp
    enumerates_even

/-- The empty language is enumerated by the enumerator that never prints. -/
example : Enumerates (fun _ : ℕ ↦ (none : Option ℕ)) fun _ ↦ False := fun _ ↦ by simp

/-- Conversely, the halting problem's recognizer yields an enumerator. -/
example : ∃ e : ℕ → Option Nat.Partrec.Code, Computable e ∧
    Enumerates e fun c ↦ (c.eval 0).Dom :=
  tm2Recognizable_iff_exists_enumerator.mp (tm2Recognizable_halting 0)

end CSLibExtTest.Computability.Decidability.Enumerators
