/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algorithms.AhoCorasick

@[expose] public section

/-- Boundary check: the pattern `ab` over `Char`-like atoms is
reported ending at position 1 of the text `ab`. -/
example : Reports [[1, 2]] [1, 2] 1 [1, 2] :=
  (reports_iff_occurs (by simp) (by simp) (by simp)).mpr ⟨[], by simp⟩
