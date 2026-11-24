/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Finset.Insert
import MathlibExt.Combinatorics.HypergraphColoringShared

/-! # Empty families and empty edges in hypergraph coloring -/

namespace MathlibExtTest.HypergraphColoringShared

open MathlibExt.Combinatorics.HypergraphColoringShared

example : HypergraphColorable (∅ : Finset (Finset (Fin 0))) 0 :=
  ⟨id, by simp⟩

example (n k : ℕ) : ¬ HypergraphColorable ({∅} : Finset (Finset (Fin n))) k := by
  rintro ⟨_, h⟩
  simpa using h ∅ (by simp)

end MathlibExtTest.HypergraphColoringShared
