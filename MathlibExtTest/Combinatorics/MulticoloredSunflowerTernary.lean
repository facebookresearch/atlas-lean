/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.MulticoloredSunflowerTernary

open MathlibExt.Combinatorics.MulticoloredSunflowerTernaryOWR12177Problem010Wanted

-- The unique triple in dimension zero cannot supply a nontrivial witness.
example : ¬ HasMulticoloredSunflower
    ({(0, 0, 0)} : Finset (TernaryVec 0 × TernaryVec 0 × TernaryVec 0)) := by
  simp [HasMulticoloredSunflower]

-- Two zero-sum triples with a common first entry suffice, since a witness may repeat a member.
example : HasMulticoloredSunflower
    ({(0, 0, 0), (0, 1, -1)} : Finset (TernaryVec 1 × TernaryVec 1 × TernaryVec 1)) := by
  refine ⟨(0, 1, -1), by simp, (0, 0, 0), by simp, (0, 0, 0), by simp, ?_, by simp⟩
  decide

-- Two distinct diagonal triples need not give a mixed zero sum.
example : ¬ HasMulticoloredSunflower
    ({(0, 0, 0), (1, 1, 1)} : Finset (TernaryVec 1 × TernaryVec 1 × TernaryVec 1)) := by
  rintro ⟨a, ha, b, hb, c, hc, hne, hsum⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    revert hne hsum <;> decide
