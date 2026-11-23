/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.InfinitaryHalesJewett
import Mathlib.Data.Finset.Range

/-! Tests for Hales–Jewett configurations in J-sets of words. -/

open MetaMathlibExt

-- With no variables, the unique substitution gives a member of D even at an empty level.
example {D : Set (FreeSemigroup ℕ)} (hD : IsMulJSet D) : D.Nonempty := by
  obtain ⟨w, _, hw⟩ := exists_variableWord_subst_mem_of_isMulJSet Finset.range
    Finset.range_mono (fun x => ⟨x + 1, Finset.mem_range.mpr (Nat.lt_succ_self x)⟩) 0 0 hD
  exact ⟨_, hw Fin.elim0 (fun i => i.elim0)⟩

-- Over the two-letter alphabet, one word realizes all four binary substitutions.
example {D : Set (FreeSemigroup Bool)} (hD : IsMulJSet D) :
    ∃ w : FreeSemigroup (Bool ⊕ Fin 2), Sum.inr 0 ∈ w.head :: w.tail ∧
      Sum.inr 1 ∈ w.head :: w.tail ∧
      ∀ a : Fin 2 → Bool, FreeSemigroup.map (Sum.elim id a) w ∈ D := by
  obtain ⟨w, hvars, hw⟩ := exists_variableWord_subst_mem_of_isMulJSet
    (fun _ => Finset.univ) monotone_const (fun x => ⟨0, Finset.mem_univ x⟩) 0 2 hD
  exact ⟨w, hvars 0, hvars 1, fun a => hw a (fun i => Finset.mem_univ (a i))⟩
