/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.AlternatingSumDifferenceDominated

namespace MathlibExtTest.Combinatorics.Additive.AlternatingSumDifferenceDominated

open scoped Pointwise

private def sequence (m d k : ℤ) : ℕ → Finset ℤ
  | 0 => ∅
  | 1 => insert (-d) (insert ((k + 1) * m - d) (insert m
      ((Finset.Icc 0 (m - 1)).erase d ∪ (Finset.Icc 1 k).image (fun j => j * m - d) ∪
        ((Finset.Icc 0 (m - 1)).erase d).image (fun b => (k + 1) * m - 2 * d - b))))
  | n + 2 =>
      if (n + 2) % 2 = 0 then
        insert ((k + ((n + 2) / 2 : ℕ) + 1) * m - d) (sequence m d k (n + 1))
      else
        insert (-((n + 1) / 2 : ℕ) * m - d)
          (insert ((k + ((n + 1) / 2 : ℕ) + 1) * m - d) (sequence m d k n))

private theorem sequence_even (m d k : ℤ) (r : ℕ) (hr : 1 ≤ r) :
    sequence m d k (2 * r) =
      insert ((k + r + 1) * m - d) (sequence m d k (2 * r - 1)) := by
  cases r with
  | zero => omega
  | succ r =>
    rw [show 2 * (r + 1) = 2 * r + 2 by omega, sequence,
      ite_eq_left (show (2 * r + 2) % 2 = 0 by omega)]
    rw [show (2 * r + 2) / 2 = r + 1 by omega,
      show 2 * r + 2 - 1 = 2 * r + 1 by omega]

private theorem sequence_odd (m d k : ℤ) (r : ℕ) (hr : 1 ≤ r) :
    sequence m d k (2 * r + 1) = insert (-(r : ℤ) * m - d)
      (insert ((k + r + 1) * m - d) (sequence m d k (2 * r - 1))) := by
  cases r with
  | zero => omega
  | succ r =>
    rw [show 2 * (r + 1) + 1 = (2 * r + 1) + 2 by omega, sequence,
      ite_eq_right (show ((2 * r + 1) + 2) % 2 ≠ 0 by omega)]
    rw [show (2 * r + 1 + 1) / 2 = r + 1 by omega,
      show 2 * (r + 1) - 1 = 2 * r + 1 by omega]

example :
    (sequence 4 1 3 1 - sequence 4 1 3 1).card <
      (sequence 4 1 3 1 + sequence 4 1 3 1).card ∧
    ∀ r ≥ 1,
      (sequence 4 1 3 (2 * r) + sequence 4 1 3 (2 * r)).card <
        (sequence 4 1 3 (2 * r) - sequence 4 1 3 (2 * r)).card ∧
      (sequence 4 1 3 (2 * r + 1) - sequence 4 1 3 (2 * r + 1)).card <
        (sequence 4 1 3 (2 * r + 1) + sequence 4 1 3 (2 * r + 1)).card ∧
      sequence 4 1 3 (2 * r - 1) ⊂ sequence 4 1 3 (2 * r) ∧
      sequence 4 1 3 (2 * r) ⊂ sequence 4 1 3 (2 * r + 1) := by
  have h := MetaMathlibExt.alternating_sequence_from_nathanson
    (m := 4) (d := 1) (k := 3) (by decide) (by decide) (by decide)
    (by decide) (by decide) (sequence 4 1 3) rfl
    (sequence_even 4 1 3) (sequence_odd 4 1 3)
  refine ⟨h.1, ?_⟩
  intro r hr
  rcases h.2 r hr with ⟨he, ho, hs, ht, _, _, _, _⟩
  exact ⟨he, ho, hs, ht⟩

example : ∀ r ≥ 1,
    (sequence 4 3 4 (2 * r - 1) + sequence 4 3 4 (2 * r - 1)).card =
      (sequence 4 3 4 (2 * r - 1) - sequence 4 3 4 (2 * r - 1)).card + 1 ∧
    ((sequence 4 3 4 (2 * r) + sequence 4 3 4 (2 * r)).card : ℤ) ≤
      (sequence 4 3 4 (2 * r) - sequence 4 3 4 (2 * r)).card - 4 + 3 := by
  have h := MetaMathlibExt.alternating_sequence_from_nathanson
    (m := 4) (d := 3) (k := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) (sequence 4 3 4) rfl
    (sequence_even 4 3 4) (sequence_odd 4 3 4)
  intro r hr
  rcases h.2 r hr with ⟨_, _, _, _, _, _, hc, hb⟩
  exact ⟨hc, hb⟩

end MathlibExtTest.Combinatorics.Additive.AlternatingSumDifferenceDominated
