/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.FixedPerimeterDistinctArmLeg

namespace MetaMathlibExt

-- With a single part, the lower bound on that part still matters.
example {d a m : ℕ} (hd : 0 < d) (ha : 0 < a) (hm : 0 < m) (had : a ≤ d + 1) :
    perimeterDistinctArmLegCount d a m 1 = if a ≤ m then 1 else 0 := by
  obtain ⟨hne, hcount⟩ :=
    perimeterDistinctArmLegCount_ne_zero_iff_and_eq_choose hd ha hm (k := 1) (by decide) had
  simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero, Nat.choose_zero_right] at hne hcount
  split <;> rename_i h
  · exact hcount h
  · exact Classical.byContradiction (fun hn => h (hne.mp hn))

-- With three parts and gap two, the first possible largest part is a + 4.
-- Each unit of excess contributes to the upper index of the binomial coefficient.
example {a : ℕ} (ha : 0 < a) (had : a ≤ 3) (r : ℕ) :
    perimeterDistinctArmLegCount 2 a (a + 4 + r) 3 = (r + 2).choose 2 := by
  have h := (perimeterDistinctArmLegCount_ne_zero_iff_and_eq_choose (d := 2) (k := 3)
    (m := a + 4 + r) (by decide) ha (by omega) (by decide) had).2 (by omega)
  exact h.trans (congrArg (fun n : ℕ => n.choose 2) (by omega))

-- Direct enumeration just below and at the threshold for 2-distinct triples.
example : perimeterDistinctArmLegCount 2 1 4 3 = 0 ∧ perimeterDistinctArmLegCount 2 1 5 3 = 1 := by
  decide

end MetaMathlibExt
