/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.DavenportElementaryTwo

namespace MetaMathlibExt

private abbrev lengths (a : ℕ) : Set ℕ :=
  {k : ℕ | 0 < k ∧ ∀ x : Fin k → Fin a → ZMod 2, ∃ I : Finset (Fin k), I.Nonempty ∧
    ∃ w : Fin k → ZMod 2, (∀ i ∈ I, w i ∈ ({1} : Set (ZMod 2))) ∧ ∑ i ∈ I, w i • x i = 0}

-- The trivial group still has a positive Davenport constant.
example : IsLeast (lengths 0) 1 := davenport_zmod_two_pow 0

-- In rank two the pair of coordinate vectors can be zero-sum-free, so two does not suffice.
example : 2 ∉ lengths 2 := by
  intro h
  have hmin : 3 ≤ 2 := (davenport_zmod_two_pow 2).2 h
  exact (by decide : ¬ 3 ≤ 2) hmin

-- At the threshold in rank two, drop the weights to recover the ordinary zero-sum statement.
example (x : Fin 3 → Fin 2 → ZMod 2) :
    ∃ I : Finset (Fin 3), I.Nonempty ∧ ∑ i ∈ I, x i = 0 := by
  obtain ⟨I, hI, w, hw, hsum⟩ := (davenport_zmod_two_pow 2).1.2 x
  refine ⟨I, hI, ?_⟩
  calc
    ∑ i ∈ I, x i = ∑ i ∈ I, w i • x i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [show w i = 1 from hw i hi]
      exact (one_smul (ZMod 2) (x i)).symm
    _ = 0 := hsum

end MetaMathlibExt
