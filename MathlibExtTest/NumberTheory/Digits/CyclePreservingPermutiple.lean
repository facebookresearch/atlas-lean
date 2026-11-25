/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.GroupTheory.Perm.Cycle.Concrete
import MathlibExt.NumberTheory.Digits.CyclePreservingPermutiple

open MetaMathlibExt

-- The six-cycle of the repeated base-four word repeats every digit, so the
-- cycle-preserving permutation the theorem supplies must separate the two
-- positions holding the digit `2`.
example :
    ∃ σ' : Equiv.Perm (Fin 8), IsPermutiple 2 4 ![0, 2, 1, 3, 0, 2, 1, 3] σ' ∧
      ∀ i : ℕ, (σ' ^ i) 1 ≠ 5 := by
  have hp : IsPermutiple 2 4 (k := 7) ![0, 2, 1, 3, 0, 2, 1, 3] c[1, 3, 2, 5, 7, 6] := by
    unfold IsPermutiple
    decide +revert
  obtain ⟨σ', hp', hgood⟩ :=
    exists_cyclePreserving_permutiple 2 4 ![0, 2, 1, 3, 0, 2, 1, 3] c[1, 3, 2, 5, 7, 6] hp
  refine ⟨σ', hp', fun i hi => ?_⟩
  have h1 := hgood 1 i (by rw [hi]; decide)
  rw [h1] at hi
  exact absurd hi (by decide)
