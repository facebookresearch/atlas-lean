/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A nonzero genuine spin coefficient distinguishes the two scalar kernel signs. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Finiteness

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

private theorem scalar_of_conjugation_eq (a b : SpinHolomorph)
    (he : spinConjugation a = spinConjugation b) :
    ∃ c : ℝ, (c = 1 ∨ c = -1) ∧ ∀ x : SpinSpace, a.val x = c • b.val x := by
  let s : SpinHolomorph := a * b⁻¹
  have hk : s ∈ spinConjugation.ker := by
    change spinConjugation s = 1
    dsimp only [s]
    rw [map_mul, map_inv, he, mul_inv_cancel]
  obtain ⟨c, hc, hs⟩ := spinHolomorph_conjugation_kernel_scalar ⟨s, hk⟩
  refine ⟨c, hc, ?_⟩
  intro x
  have h := hs (b.val x)
  change a.val (b.val.symm (b.val x)) = c • b.val x at h
  rw [LinearEquiv.symm_apply_apply] at h
  exact h

/-- Equal actual Q conjugation and one equal nonzero spin coefficient imply equality of lifts. -/
theorem monsterNortonSpin_eq_of_conjugation_eq_of_coefficient (a b : SpinHolomorph)
    (he : spinConjugation a = spinConjugation b) (x : SpinSpace) (t : SpinIndex)
    (hcoef : a.val x t = b.val x t) (hn : b.val x t ≠ 0) : a = b := by
  obtain ⟨c, hc, hs⟩ := scalar_of_conjugation_eq a b he
  have hc1 : c = 1 := by
    rcases hc with h | h
    · exact h
    · have hx := congrFun (hs x) t
      simp only [Pi.smul_apply, smul_eq_mul, h, neg_one_mul] at hx
      rw [hcoef] at hx
      exfalso
      apply hn
      linarith
  subst c
  apply Subtype.ext
  apply LinearEquiv.ext
  intro y
  simpa only [one_smul] using hs y

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
