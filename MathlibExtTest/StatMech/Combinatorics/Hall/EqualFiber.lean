/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Hall.EqualFiber
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.Hall.EqualFiber`

* `Fintype.hall_equalFiber_iff_card_fibers` in both directions: Hall's condition holds for the
  identity labelling of `Fin 3`, and fails for two elements of label `()` against one.
-/

@[expose] public section


namespace MathlibExtTest.StatMech.Combinatorics.Hall.EqualFiber

example : ∀ S : Finset (Fin 3), S.card ≤
    (Finset.univ.filter fun b => ∃ a, a ∈ S ∧ (id a : Fin 3) = id b).card := by
  have h := (Fintype.hall_equalFiber_iff_card_fibers (A := Fin 3) (B := Fin 3) id id).mpr
      fun _ => le_rfl
  convert h

example : ¬ ∀ S : Finset (Fin 2), S.card ≤
    (Finset.univ.filter fun b : Fin 1 => ∃ a, a ∈ S ∧ (fun _ => ()) a = (fun _ => ()) b).card := by
  intro h
  have h2 := (Fintype.hall_equalFiber_iff_card_fibers (A := Fin 2) (B := Fin 1) (fun _ => ())
    (fun _ => ())).mp (by convert h) ()
  simp at h2

end MathlibExtTest.StatMech.Combinatorics.Hall.EqualFiber
