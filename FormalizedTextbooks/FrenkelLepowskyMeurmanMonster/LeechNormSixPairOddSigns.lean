/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixPairAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechOddSigns

/-! Odd norm-six sign transports preserve the actual fixed positive norm-four root. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A Golay sign fixing a nonzero coordinate of an actual vector has zero code bit there. -/
theorem leechSign_fixed_nonzero_coordinate (d : golayCode) (u : leechIntegral)
    (i : Fin 24) (hi : u.val i ≠ 0)
    (h : (leechIntegralAction (golaySignIsometry d) u).val i = u.val i) :
    d.val i = 0 := by
  by_contra hn
  rw [leechIntegralAction_golaySign] at h
  change (if d.val i = 0 then u.val i else -u.val i) = u.val i at h
  rw [ite_eq_right hn] at h
  omega

/-- Zero Golay sign bits at both root coordinates fix the actual positive root. -/
theorem leechSign_fixes_positive_root (d : golayCode) (h0 : d.val 0 = 0)
    (h1 : d.val 1 = 0) :
    leechIntegralAction (golaySignIsometry d) leechRootedA2Root = leechRootedA2Root := by
  apply Subtype.ext
  rw [leechIntegralAction_golaySign]
  funext i
  by_cases hi0 : i = 0
  · subst i
    simp [golayIntegerSign, h0]
  · by_cases hi1 : i = 1
    · subst i
      simp [golayIntegerSign, h1]
    · simp [golayIntegerSign, leechRootedA2Root, leechRootedA2RootIntegral, hi0, hi1]

/-- Actual odd paired vectors with equal magnitudes and the same root coordinates are related
by a genuine positive-root stabilizer element. -/
theorem leechNormSixPair_odd_sign_transport (u v : LeechNormSixPair)
    (hu : Odd (u.val.val 0)) (hv : Odd (v.val.val 0))
    (hn0 : u.val.val 0 ≠ 0) (hn1 : u.val.val 1 ≠ 0)
    (h0 : u.val.val 0 = v.val.val 0) (h1 : u.val.val 1 = v.val.val 1)
    (habs : ∀ i, (u.val.val i).natAbs = (v.val.val i).natAbs) :
    ∃ e : leechRootedA2PositiveRootSubgroup, e • u = v := by
  obtain ⟨d, hd⟩ := leechOdd_same_magnitudes_transport u.val v.val hu hv habs
  have hd0 : d.val 0 = 0 := leechSign_fixed_nonzero_coordinate d u.val 0 hn0
    ((congrArg (fun w : leechIntegral => w.val 0) hd).trans h0.symm)
  have hd1 : d.val 1 = 0 := leechSign_fixed_nonzero_coordinate d u.val 1 hn1
    ((congrArg (fun w : leechIntegral => w.val 1) hd).trans h1.symm)
  have hr := leechSign_fixes_positive_root d hd0 hd1
  let e : leechRootedA2PositiveRootSubgroup :=
    ⟨⟨golaySignIsometry d, (leechRootedA2RootLineSubgroup_mem _).mpr (Or.inl hr)⟩, hr⟩
  exact ⟨e, Subtype.ext hd⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
