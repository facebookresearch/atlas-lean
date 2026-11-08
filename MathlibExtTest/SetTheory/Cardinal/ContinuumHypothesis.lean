/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Steven Warner, Nam Trang
-/
module

public import MathlibExt.SetTheory.Cardinal.ContinuumHypothesis

@[expose] public section

open Cardinal Ordinal Set Order

namespace MathlibExtTest.SetTheory.Cardinal.ContinuumHypothesis

open MetaMathlibExt

-- Logic 3: Continuum Hypothesis (CH)

/-- CH says exactly that no cardinal sits strictly between ℵ₀ and 2 ^ ℵ₀. -/

theorem continuumHypothesis_iff_no_intermediate.{u} :

    ContinuumHypothesis.{u} ↔ ¬ ∃ c : Cardinal.{u}, ℵ₀ < c ∧ c < 2 ^ ℵ₀ := by

  constructor

  · rintro h ⟨c, hc0, hc1⟩

    rw [h] at hc1

    exact absurd (aleph_one_le_iff.2 hc0) (not_le.2 hc1)

  · intro h

    rcases (aleph_one_le_iff.2 (cantor (ℵ₀ : Cardinal.{u}))).lt_or_eq with hlt | heq

    · exact absurd ⟨ℵ₁, aleph0_lt_aleph_one, hlt⟩ h

    · exact heq.symm

end MathlibExtTest.SetTheory.Cardinal.ContinuumHypothesis

end
