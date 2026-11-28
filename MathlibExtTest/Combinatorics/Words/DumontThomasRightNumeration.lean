/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Order.Filter.AtTopBot.Basic
import MathlibExt.Combinatorics.Words.DumontThomasRightNumeration

namespace MetaMathlibExt.dumontThomas_numeration.Tests

private def letterImage (_ : Bool) : List Bool := [false, true]

private def alternating (i : ℕ) : Bool := i % 2 == 1

private theorem alternating_fixed (n i : ℕ)
    (hi : i < (morphExtend letterImage ((List.range n).map alternating)).length) :
    (morphExtend letterImage ((List.range n).map alternating))[i] = alternating i := by
  have himage : morphExtend letterImage ((List.range n).map alternating) =
      (List.replicate n [false, true]).flatten := by
    simp [morphExtend, letterImage, List.flatMap, List.map_map, Function.comp_def,
      List.map_const']
  have hlookup (m j : ℕ) (hj : j < (List.replicate m [false, true]).flatten.length) :
      (List.replicate m [false, true]).flatten[j]? = some (alternating j) := by
    induction m generalizing j with
    | zero => simp at hj
    | succ m ih =>
      simp only [List.replicate_succ, List.flatten_cons] at hj ⊢
      by_cases h : 2 ≤ j
      · have hj' : j - 2 < (List.replicate m [false, true]).flatten.length := by
          simp only [List.length_append, List.length_cons, List.length_nil] at hj
          omega
        rw [List.getElem?_append_right h]
        change (List.replicate m [false, true]).flatten[j - 2]? = some (alternating j)
        rw [ih _ hj']
        have hmod : (j - 2) % 2 = j % 2 := by omega
        simp only [alternating, hmod]
      · have hj' : j = 0 ∨ j = 1 := by omega
        rcases hj' with rfl | rfl <;> rfl
  have h : (morphExtend letterImage ((List.range n).map alternating))[i]? =
      some (alternating i) := by
    rw [himage]
    exact hlookup n i (by simpa only [← himage] using hi)
  exact (List.getElem?_eq_some_iff.mp h).2

private theorem grows : Filter.Tendsto (fun k => (morphIterate letterImage k [false]).length)
    Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop.mpr fun m => ⟨m, fun k hk => ?_⟩
  rw [morphIterate_length_of_uniform (fun _ => rfl : ∀ b, (letterImage b).length = 2)]
  simpa only [List.length_singleton, Nat.mul_one] using hk.trans Nat.lt_two_pow_self.le

private theorem isSubstitution : IsSubstitution letterImage :=
  ⟨fun _ => by simp [letterImage], false, grows⟩

private def path (tail : List Bool × Bool) : ℕ → List Bool × Bool
  | 0 => tail
  | _ + 1 => ([false], true)

private theorem path_admissible (tail : List Bool × Bool)
    (h : tail.1 ++ [tail.2] <+: letterImage true) :
    IsLetterAdmissibleSequence letterImage false (path tail) 1 := by
  refine ⟨fun i hi => ?_, ⟨[], rfl⟩⟩
  obtain rfl : i = 0 := by omega
  exact h

-- At the length of the first seed iterate, the unique expansion skips that entire block.
example : ∃ (k : ℕ) (s : ℕ → List Bool × Bool),
    IsLetterAdmissibleSequence letterImage false s k ∧ k = 1 ∧
      s 1 = ([false], true) ∧ s 0 = ([], false) := by
  obtain ⟨k, s, hs, huniq⟩ :=
    dumontThomas_numeration letterImage isSubstitution false alternating alternating_fixed
      rfl grows 2 (by decide)
  obtain ⟨rfl, heq⟩ := huniq 1 (path ([], false))
    ⟨path_admissible _ (by decide), by decide, by decide⟩
  exact ⟨1, s, hs.1, rfl, (heq 1 (by decide)).symm, (heq 0 (by decide)).symm⟩

-- At length three the smaller word contributes as well, after the larger block.
example : ∃ (k : ℕ) (s : ℕ → List Bool × Bool),
    IsLetterAdmissibleSequence letterImage false s k ∧ k = 1 ∧
      s 1 = ([false], true) ∧ s 0 = ([false], true) := by
  obtain ⟨k, s, hs, huniq⟩ :=
    dumontThomas_numeration letterImage isSubstitution false alternating alternating_fixed
      rfl grows 3 (by decide)
  obtain ⟨rfl, heq⟩ := huniq 1 (path ([false], true))
    ⟨path_admissible _ (by decide), by decide, by decide⟩
  exact ⟨1, s, hs.1, rfl, (heq 1 (by decide)).symm, (heq 0 (by decide)).symm⟩

end MetaMathlibExt.dumontThomas_numeration.Tests
