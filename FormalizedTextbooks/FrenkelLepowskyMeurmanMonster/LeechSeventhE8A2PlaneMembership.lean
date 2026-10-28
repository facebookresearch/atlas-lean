/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2Planes
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2PairBounds
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2SortedTriples
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2PlaneKeys

/-! Intrinsic actual root incidence distinguishes the finite A2 planes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

private theorem dot_outer_sum {ι n : Type*} [Fintype ι] [Fintype n]
    (u : ι → n → ℝ) (x : n → ℝ) :
    x ⬝ᵥ leechSeventhRootOuterSum u x = ∑ j, (u j ⬝ᵥ x) ^ 2 := by
  rw [leechSeventhRootOuterSum_apply, dotProduct_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [dotProduct_smul, dotProduct_comm x, pow_two, smul_eq_mul]

/-- The actual section root lines in a candidate plane are precisely its three named lines. -/
theorem leechSeventhE8A2Plane_root_iff (p : Fin 1120) (r : Fin 120) :
    leechSeventhE8RealRoot r ∈ leechSeventhE8A2Plane p ↔
      ∃ j : Fin 3, leechSeventhE8A2Indices p j = r := by
  constructor
  · intro hr
    have hf := (leechSeventhE8A2Plane_mem_iff p _).mp hr
    have hd := congrArg (fun x => leechSeventhE8RealRoot r ⬝ᵥ x) hf
    rw [dot_outer_sum, dotProduct_smul] at hd
    change (∑ j : Fin 3,
      (stdPairingFun (leechSeventhE8A2PlaneRoots p j) (leechSeventhE8RealRoot r)) ^ 2) =
        (6 : ℝ) * stdPairingFun (leechSeventhE8RealRoot r) (leechSeventhE8RealRoot r) at hd
    rw [leechSeventhE8RealRoot_norm] at hd
    norm_num only [show (6 : ℝ) * 4 = 24 by norm_num] at hd
    by_contra hn
    push Not at hn
    have hb : (∑ j : Fin 3,
        (stdPairingFun (leechSeventhE8A2PlaneRoots p j) (leechSeventhE8RealRoot r)) ^ 2) ≤
          ∑ _j : Fin 3, (4 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      exact leechSeventhE8RealRoot_pairing_square_bound _ r (hn j)
    norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
    linarith only [hd, hb]
  · rintro ⟨j, hj⟩
    rw [← hj]
    exact leechSeventhE8A2Plane_root_mem p j

/-- Distinct original candidate addresses give distinct actual real A2 planes. -/
theorem leechSeventhE8A2Plane_injective : Function.Injective leechSeventhE8A2Plane := by
  intro p q hpq
  apply leechSeventhE8A2Indices_injective
  apply leechSeventh_sorted_triple_unique
    (leechSeventhE8A2Indices p) (leechSeventhE8A2Indices q)
    (leechSeventhE8A2_indices_sorted p) (leechSeventhE8A2_indices_sorted q)
  intro r
  rw [← leechSeventhE8A2Plane_root_iff, ← leechSeventhE8A2Plane_root_iff, hpq]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
