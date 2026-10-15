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

public import Mathlib.SetTheory.Cardinal.Aleph
@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 3
-- Proposed path (advisory metadata only, not a review instruction).

open Cardinal Ordinal

-- Logic 3: Continuum Hypothesis (CH)
def ContinuumHypothesis.{u} : Prop := (2 : Cardinal.{u}) ^ ℵ₀ = ℵ₁

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

end
