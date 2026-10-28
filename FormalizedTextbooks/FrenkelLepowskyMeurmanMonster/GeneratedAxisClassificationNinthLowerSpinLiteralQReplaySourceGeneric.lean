/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceData

/-! Exact source-array slices transfer every original label and signed letter. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

private theorem getD_extract_of_bounds {α : Type} (xs : Array α)
    (start stop j : ℕ) (fallback : α) (hj : j < min stop xs.size - start) :
    (xs.extract start stop).getD j fallback = xs.getD (start + j) fallback := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_extract, hj, ite_true]

/-- One exact slice transfers the whole bounded function, retaining every source value. -/
theorem generatedNinth_lower_spin_literal_q_replay_slice_function {α : Type}
    (xs small : Array α) (start count : ℕ) (fallback : α)
    (hsize : small.size = count)
    (hslice : xs.extract start (start + count) = small) :
    (fun j : Fin count => xs.getD (start + j.val) fallback) =
      (fun j : Fin count => small.getD j.val fallback) := by
  have hs : min (start + count) xs.size - start = count := by
    have h := congrArg Array.size hslice
    simpa only [Array.size_extract, hsize] using h
  funext j
  have hj : j.val < min (start + count) xs.size - start := by
    rw [hs]
    exact j.isLt
  rw [← getD_extract_of_bounds xs start (start + count) j.val fallback hj, hslice]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
