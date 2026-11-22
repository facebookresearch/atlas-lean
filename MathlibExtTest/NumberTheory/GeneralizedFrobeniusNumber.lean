/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralizedFrobeniusNumber
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

example : frobeniusRepCount ![2, 3] (-1) = 0 := frobeniusRepCount_eq_zero_of_neg _ (by norm_num)

example (m : ℤ) : frobeniusRepCount ![2, 3] m ≠ ⊤ :=
  frobeniusRepCount_ne_top (by decide) m

/-- A zero generator makes the representation set of `0` infinite, so the count is `⊤`. -/
example : frobeniusRepCount ![0] 0 = ⊤ := by
  rw [frobeniusRepCount, Set.encard_eq_top_iff]
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ![n]) ?_ ?_
  · intro m n h
    simpa using congrFun h 0
  · intro n
    simp

example {g g' : ℤ} (h : IsGenFrobeniusNumber ![2, 3] 0 g) (h' : IsGenFrobeniusNumber ![2, 3] 0 g') :
    g = g' :=
  h.unique h'

end MetaMathlibExt
