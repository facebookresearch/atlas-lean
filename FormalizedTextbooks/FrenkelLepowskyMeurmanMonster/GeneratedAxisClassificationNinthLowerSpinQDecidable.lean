/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQCoordinateEvaluation

/-! Computable equality of the full genuine extraspecial coordinates, including the center. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Equality of genuine Q elements is exactly equality of their full base and central fields. -/
theorem generatedNinth_lower_spin_q_eq_iff (q r : Q) :
    q = r ↔ q.base = r.base ∧ q.coeff = r.coeff := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨hb, hc⟩
    exact NormalizedCocycleExtension.Extension.ext hb hc

/-- Full Q equality is decided by finite binary base coordinates and the actual central bit. -/
instance generatedNinthLowerSpinQDecidableEq : DecidableEq Q := fun q r =>
  decidable_of_iff (q.base = r.base ∧ q.coeff = r.coeff)
    (generatedNinth_lower_spin_q_eq_iff q r).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
