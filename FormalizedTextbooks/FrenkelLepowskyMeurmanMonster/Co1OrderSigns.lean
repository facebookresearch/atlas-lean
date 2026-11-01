/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Finiteness

/-! Counting the genuine central signs in the lattice isometry group.
This supplies the factor of two in any eventual Co₀ order computation;
it does not assume or assert the outstanding Co₀ enumeration. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual negative identity preserves the coordinate Leech lattice. -/
noncomputable def leechNegativeIdentity : leechIsomSubgroup :=
  ⟨({ toFun := fun x => -x
      invFun := fun x => -x
      left_inv := neg_neg
      right_inv := neg_neg
      map_add' := neg_add
      map_smul' := by intros; simp } : (Fin 24 → ℝ) ≃ₗ[ℝ] (Fin 24 → ℝ)), by
    change IsLeechIsom _
    constructor
    · intro x y
      simp [stdPairingFun]
    · intro x
      exact LeechLattice.neg_mem_iff.symm⟩

@[simp] theorem leechNegativeIdentity_apply (x : Fin 24 → ℝ) :
    leechNegativeIdentity.val x = -x := rfl

theorem leechNegativeIdentity_ne_one : leechNegativeIdentity ≠ 1 := by
  intro h
  have hh := congrArg (fun e : leechIsomSubgroup => e.val (fun _ => 1) 0) h
  norm_num [leechNegativeIdentity] at hh

/-- Enumerating exactly the two signs by their actual real linear maps. -/
noncomputable def leechSignEnumeration (b : Bool) : signsSubgroup :=
  if b then ⟨leechNegativeIdentity, Or.inr (fun _ => rfl)⟩
  else ⟨1, Or.inl rfl⟩

theorem leechSignEnumeration_bijective : Function.Bijective leechSignEnumeration := by
  constructor
  · intro a b h
    cases a <;> cases b
    · rfl
    · have hh := congrArg (fun e : signsSubgroup => e.val) h
      exact False.elim (leechNegativeIdentity_ne_one (by
        simpa [leechSignEnumeration] using hh.symm))
    · have hh := congrArg (fun e : signsSubgroup => e.val) h
      exact False.elim (leechNegativeIdentity_ne_one (by
        simpa [leechSignEnumeration] using hh))
    · rfl
  · intro s
    rcases s.property with hs | hs
    · refine ⟨false, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      simpa [leechSignEnumeration] using hs.symm
    · refine ⟨true, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      simpa [leechSignEnumeration] using (hs x).symm

/-- The central subgroup has order two, proved from its defining maps. -/
theorem signsSubgroup_card : Nat.card signsSubgroup = 2 := by
  rw [← Nat.card_congr (Equiv.ofBijective leechSignEnumeration leechSignEnumeration_bijective)]
  simp

/-- The exact quotient relation for the actual lattice isometry group. -/
theorem leechIsomSubgroup_card :
    Nat.card leechIsomSubgroup = 2 * Nat.card Co1 := by
  have h := signsSubgroup.card_mul_index
  rw [signsSubgroup_card] at h
  exact h.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
