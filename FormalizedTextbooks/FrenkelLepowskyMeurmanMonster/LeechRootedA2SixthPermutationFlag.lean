/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2SixthPermutationTriple

/-! Actual Mathieu permutations preserving the root pair and third plane point. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual permutations preserve the unordered root pair and fix the third physical coordinate. -/
def leechRootedA2SixthPermutationFlag : Subgroup golayAutomorphismSubgroup where
  carrier := {p | ((p.val 16 = 16 ∧ p.val 17 = 17) ∨
    (p.val 16 = 17 ∧ p.val 17 = 16)) ∧ p.val 19 = 19}
  one_mem' := ⟨Or.inl ⟨rfl, rfl⟩, rfl⟩
  mul_mem' := by
    rintro p q ⟨hp, hp19⟩ ⟨hq, hq19⟩
    refine ⟨?_, ?_⟩
    · change ((p.val (q.val 16) = 16 ∧ p.val (q.val 17) = 17) ∨
        (p.val (q.val 16) = 17 ∧ p.val (q.val 17) = 16))
      rcases hp with hp | hp <;> rcases hq with hq | hq <;>
        simp [hq.1, hq.2, hp.1, hp.2]
    · change p.val (q.val 19) = 19
      rw [hq19, hp19]
  inv_mem' := by
    rintro p ⟨hp, hp19⟩
    refine ⟨?_, ?_⟩
    · rcases hp with ⟨hp16, hp17⟩ | ⟨hp16, hp17⟩
      · left
        constructor
        · change p.val.symm 16 = 16
          exact p.val.symm_apply_eq.mpr hp16.symm
        · change p.val.symm 17 = 17
          exact p.val.symm_apply_eq.mpr hp17.symm
      · right
        constructor
        · change p.val.symm 16 = 17
          exact p.val.symm_apply_eq.mpr hp17.symm
        · change p.val.symm 17 = 16
          exact p.val.symm_apply_eq.mpr hp16.symm
    · change p.val.symm 19 = 19
      exact p.val.symm_apply_eq.mpr hp19.symm

/-- Every ordered-triple stabilizer element preserves the actual unordered flag. -/
theorem leechRootedA2SixthPermutationTriple_le :
    leechRootedA2SixthPermutationTriple ≤ leechRootedA2SixthPermutationFlag := by
  intro p hp
  obtain ⟨h0, h1, h2⟩ := (leechRootedA2SixthPermutationTriple_mem p).mp hp
  exact ⟨Or.inl ⟨h0, h1⟩, h2⟩

/-- The actual Mathieu group contains a root-pair swap fixing the third plane coordinate. -/
theorem leechRootedA2SixthPermutationSwap_exists :
    ∃ p : golayAutomorphismSubgroup, p.val 16 = 17 ∧ p.val 17 = 16 ∧ p.val 19 = 19 := by
  obtain ⟨p, hp⟩ := leechRootedA2_three_transitive
    (![16, 17, 19] : Fin 3 → Fin 24) ![17, 16, 19] (by decide +kernel) (by decide +kernel)
  exact ⟨p, hp 0, hp 1, hp 2⟩

/-- One genuine root-pair swap selected from actual Mathieu three-transitivity. -/
def leechRootedA2SixthPermutationSwap : golayAutomorphismSubgroup :=
  Classical.choose leechRootedA2SixthPermutationSwap_exists

/-- The selected actual permutation has the exact root-pair/third-coordinate images. -/
theorem leechRootedA2SixthPermutationSwap_spec :
    leechRootedA2SixthPermutationSwap.val 16 = 17 ∧
      leechRootedA2SixthPermutationSwap.val 17 = 16 ∧
      leechRootedA2SixthPermutationSwap.val 19 = 19 :=
  Classical.choose_spec leechRootedA2SixthPermutationSwap_exists

/-- The selected root-pair swap is an actual flag permutation. -/
theorem leechRootedA2SixthPermutationSwap_mem :
    leechRootedA2SixthPermutationSwap ∈ leechRootedA2SixthPermutationFlag :=
  ⟨Or.inr ⟨leechRootedA2SixthPermutationSwap_spec.1,
    leechRootedA2SixthPermutationSwap_spec.2.1⟩, leechRootedA2SixthPermutationSwap_spec.2.2⟩

/-- The two genuine flag-permutation cosets are parameterized by the ordered-triple stabilizer. -/
def leechRootedA2SixthPermutationEnumeration
    (x : Fin 2 × leechRootedA2SixthPermutationTriple) : leechRootedA2SixthPermutationFlag :=
  if x.1 = 0 then
    ⟨x.2.val, leechRootedA2SixthPermutationTriple_le x.2.property⟩
  else
    ⟨leechRootedA2SixthPermutationSwap * x.2.val,
      leechRootedA2SixthPermutationFlag.mul_mem leechRootedA2SixthPermutationSwap_mem
        (leechRootedA2SixthPermutationTriple_le x.2.property)⟩

/-- The two actual cosets have unique parameters. -/
theorem leechRootedA2SixthPermutationEnumeration_injective :
    Function.Injective leechRootedA2SixthPermutationEnumeration := by
  rintro ⟨i, p⟩ ⟨j, q⟩ h
  have hi := (leechRootedA2SixthPermutationTriple_mem p.val).mp p.property
  have hj := (leechRootedA2SixthPermutationTriple_mem q.val).mp q.property
  have he := congrArg Subtype.val h
  have hc := congrArg (fun p : golayAutomorphismSubgroup => p.val 16) he
  fin_cases i <;> fin_cases j
  · apply Prod.ext
    · rfl
    apply Subtype.ext
    simpa [leechRootedA2SixthPermutationEnumeration] using he
  · simp [leechRootedA2SixthPermutationEnumeration, hi.1, hj.1,
      leechRootedA2SixthPermutationSwap_spec.1] at hc
  · simp [leechRootedA2SixthPermutationEnumeration, hi.1, hj.1,
      leechRootedA2SixthPermutationSwap_spec.1] at hc
  · apply Prod.ext
    · rfl
    apply Subtype.ext
    apply mul_left_cancel (a := leechRootedA2SixthPermutationSwap)
    simpa [leechRootedA2SixthPermutationEnumeration] using he

/-- Every actual flag permutation belongs to one of the two original cosets. -/
theorem leechRootedA2SixthPermutationEnumeration_surjective :
    Function.Surjective leechRootedA2SixthPermutationEnumeration := by
  intro p
  rcases p.property.1 with hp | hp
  · let q : leechRootedA2SixthPermutationTriple :=
      ⟨p.val, (leechRootedA2SixthPermutationTriple_mem p.val).mpr
        ⟨hp.1, hp.2, p.property.2⟩⟩
    exact ⟨(0, q), Subtype.ext rfl⟩
  · have hs := leechRootedA2SixthPermutationSwap_spec
    have h0 : (leechRootedA2SixthPermutationSwap⁻¹ * p.val).val 16 = 16 := by
      change leechRootedA2SixthPermutationSwap.val.symm (p.val.val 16) = 16
      rw [hp.1, ← hs.1, Equiv.symm_apply_apply]
    have h1 : (leechRootedA2SixthPermutationSwap⁻¹ * p.val).val 17 = 17 := by
      change leechRootedA2SixthPermutationSwap.val.symm (p.val.val 17) = 17
      rw [hp.2, ← hs.2.1, Equiv.symm_apply_apply]
    have h2 : (leechRootedA2SixthPermutationSwap⁻¹ * p.val).val 19 = 19 := by
      change leechRootedA2SixthPermutationSwap.val.symm (p.val.val 19) = 19
      rw [p.property.2]
      exact leechRootedA2SixthPermutationSwap.val.symm_apply_eq.mpr hs.2.2.symm
    let q : leechRootedA2SixthPermutationTriple :=
      ⟨leechRootedA2SixthPermutationSwap⁻¹ * p.val,
        (leechRootedA2SixthPermutationTriple_mem _).mpr ⟨h0, h1, h2⟩⟩
    refine ⟨(1, q), ?_⟩
    apply Subtype.ext
    change leechRootedA2SixthPermutationSwap *
      (leechRootedA2SixthPermutationSwap⁻¹ * p.val) = p.val
    simp only [mul_inv_cancel_left]

/-- The full genuine Mathieu flag-permutation stabilizer has40320 elements. -/
theorem leechRootedA2SixthPermutationFlag_card : Nat.card leechRootedA2SixthPermutationFlag =
    40320 := by
  rw [← Nat.card_congr (Equiv.ofBijective leechRootedA2SixthPermutationEnumeration
    ⟨leechRootedA2SixthPermutationEnumeration_injective,
      leechRootedA2SixthPermutationEnumeration_surjective⟩), Nat.card_prod,
    leechRootedA2SixthPermutationTriple_card]
  rw [Nat.card_eq_fintype_card, Fintype.card_fin]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
