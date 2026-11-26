/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ExtendedCunninghamChain

open MetaMathlibExt

-- The even prime starts at index zero and its term at index five is 5 * 19.
example : extendedCunninghamChain 2 0 = 2 ∧ extendedCunninghamChain 2 4 = 47 ∧
    extendedCunninghamChain 2 5 = 95 := ⟨rfl, rfl, rfl⟩

-- The smallest prime generator and run length are both allowed.
example : ∃ i, 0 < i ∧ ¬ (extendedCunninghamChain 2 i).Prime := by
  obtain ⟨i, hi, hrun⟩ :=
    extendedCunninghamChain_exists_composite_run 2 (hp := by decide) 1 (hn := by decide)
  exact ⟨i, hi, by simpa using hrun 0 (by decide)⟩

-- For an odd prime generator the theorem gives consecutive composite terms.
example : ∃ i, 0 < i ∧ ¬ (extendedCunninghamChain 3 i).Prime ∧
    ¬ (extendedCunninghamChain 3 (i + 1)).Prime ∧
    ¬ (extendedCunninghamChain 3 (i + 2)).Prime := by
  obtain ⟨i, hi, hrun⟩ := extendedCunninghamChain_exists_composite_run 3 (by decide) 3 (by decide)
  exact ⟨i, hi, by simpa using hrun 0 (by decide), hrun 1 (by decide), hrun 2 (by decide)⟩
