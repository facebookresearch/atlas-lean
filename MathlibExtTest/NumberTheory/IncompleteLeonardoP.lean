/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.IncompleteLeonardoP

/-!
# Tests for incomplete Leonardo p-numbers
-/

open MetaMathlibExt

-- At the first admissible index, the top cutoff includes a vanishing binomial coefficient.
example : incompleteLeonardoP 2 3 2 = 4 := by
  decide

-- At an interior cutoff the next order adds a nonzero term.
example : incompleteLeonardoP 2 9 2 = 52 ∧ incompleteLeonardoP 2 9 3 = 55 := by
  decide

-- The recurrence specializes at the first admissible index and the maximum cutoff.
example (p : ℕ) (hp : 1 ≤ p) :
    incompleteLeonardoP p (p + 1) 2 =
      incompleteLeonardoP p p 2 + incompleteLeonardoP p 0 1 + p := by
  simpa using incompleteLeonardoP_succ p (p + 1) 1 hp (by omega) (by simp)
