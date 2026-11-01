/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismBaseData

/-! The seven-point base determines every actual Golay automorphism. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The pointwise stabilizer of this concrete seven-point base is trivial. -/
theorem golayAutomorphism_eq_one_of_fix_base (p : golayAutomorphismSubgroup)
    (hp : ∀ j : Fin 7, p.val (golayBasePoints j) = golayBasePoints j) : p = 1 := by
  apply golayAutomorphism_eq_one_of_fix_except_two p
  intro i hi6 hi7
  by_cases hi5 : i = 5
  · subst i
    exact hp 6
  by_cases hi8 : i = 8
  · subst i
    exact hp 5
  apply Eq.symm
  apply golayBaseIncidenceTable_separates i (p.val i) hi5 hi8 hi6 hi7
  intro k
  rw [← golayBaseIncidenceTable_certificate k i,
    ← golayBaseIncidenceTable_certificate k (p.val i)]
  exact golayBaseIncidence_invariant p hp _ i

/-- Actual automorphisms are determined by their images of seven specified coordinates. -/
theorem golayAutomorphism_base_injective : Function.Injective
    (fun p : golayAutomorphismSubgroup => fun j : Fin 7 => p.val (golayBasePoints j)) := by
  intro p q hpq
  have h : q⁻¹ * p = 1 := golayAutomorphism_eq_one_of_fix_base _ (by
    intro j
    change q.val.symm (p.val (golayBasePoints j)) = golayBasePoints j
    have hj := congrFun hpq j
    change p.val (golayBasePoints j) = q.val (golayBasePoints j) at hj
    rw [hj, q.val.symm_apply_apply])
  exact (inv_mul_eq_one.mp h).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
