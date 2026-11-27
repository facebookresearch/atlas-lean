/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LucasLeonardoPFromLucas

/-!
# Tests for the Lucas–Leonardo and Lucas `p`-number identity
-/

open MetaMathlibExt

-- The affine identity includes the exceptional zeroth term.
example : lucasLeonardoP 2 0 = 7 := by
  rw [lucasLeonardoP_eq_lucasP 2 0 (by decide), lucasP_zero]
  decide

-- The last index in the initial interval.
example : lucasLeonardoP 2 2 = 1 := by
  rw [lucasLeonardoP_eq_lucasP 2 2 (by decide), lucasP_of_le 2 (by decide) (by decide)]
  decide

-- The first recurrence step uses the exceptional zeroth term.
example : lucasLeonardoP 2 3 = 10 := by
  rw [lucasLeonardoP_eq_lucasP 2 3 (by decide), lucasP_of_lt 2 (by decide)]
  decide
