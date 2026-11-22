/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Steven Warner
-/
module

public import MathlibExt.SetTheory.Tree.Special
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Order.Antichain
public import Mathlib.Order.SetNotation

@[expose] public section

namespace MathlibExtTest.SetTheory.Tree.Special

open MetaMathlibExt

-- Logic 16: Union of ω antichains

/-- Sanity check (positive): `ℕ` is a countable union of antichains — the singletons.
Rules out an unsatisfiable definition. -/

theorem isUnionOfOmegaAntichains_nat : IsUnionOfOmegaAntichains ℕ :=
  ⟨fun n => {n}, fun n => Set.subsingleton_singleton.isAntichain _, by ext x; simp⟩

-- Logic 36: Special partial order

/-- Check A (positive): `ℚ` is special. -/

theorem isSpecial_rat : IsSpecial ℚ := ⟨id, strictMono_id⟩

/-- Check B (negative): `ℝ` is not special.  On a linear order `StrictMono` forces
injectivity, so a special linear order is countable. -/

theorem not_isSpecial_real : ¬ IsSpecial ℝ := by
  rintro ⟨f, hf⟩
  have : Countable ℝ := hf.injective.countable
  exact absurd this (by simp)

end MathlibExtTest.SetTheory.Tree.Special

end
