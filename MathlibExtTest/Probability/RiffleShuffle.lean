/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.RiffleShuffle

@[expose] public section

open Finset
open MathlibExt.Probability.RiffleShuffle

namespace MathlibExtTest.Probability.RiffleShuffle

/-- One riffle shuffle (`a = 2`) of `4` cards leaves the deck in order for
`C(2 + 4 - r, 4)` label maps, `r = 1` rising sequence: the five monotone `0/1` label sequences. -/
example : (univ.filter (fun f : Fin 4 → Fin 2 => Tuple.sort f = (1 : Equiv.Perm (Fin 4))⁻¹)).card =
    (2 + 4 - risingSequences (1 : Equiv.Perm (Fin 4))).choose 4 :=
  card_sort_eq 4 2 1

/-- The formula for every arrangement of `3` cards under a `3`-shuffle. -/
example (π : Equiv.Perm (Fin 3)) :
    (univ.filter (fun f : Fin 3 → Fin 3 => Tuple.sort f = π⁻¹)).card =
      (3 + 3 - risingSequences π).choose 3 :=
  card_sort_eq 3 3 π

/-- The empty deck: the single label map. -/
example : (univ.filter (fun f : Fin 0 → Fin 5 => Tuple.sort f = (1 : Equiv.Perm (Fin 0))⁻¹)).card
    = 1 := by
  rw [card_sort_eq]
  simp

/-- An ordered deck has one rising sequence. -/
example : risingSequences (1 : Equiv.Perm (Fin 4)) = 1 := by
  classical
  simp only [risingSequences, inv_one, Equiv.Perm.coe_one, id_eq]
  rw [Finset.card_eq_zero.mpr]
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
    not_and, not_lt]
  intro h
  exact Fin.le_iff_val_le_val.mpr (by omega)

end MathlibExtTest.Probability.RiffleShuffle
