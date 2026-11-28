/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.HospitalsResidentsWithCouplesDefs

namespace MetaMathlibExt.Complexity.NPComplete.HospitalsResidentsWithCouples

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : HospitalsResidentsWithCouplesInstance) :
    hospitalsResidentsWithCouplesDec (bitEncode i) = true ↔
      WellFormed i ∧ HospitalsResidentsWithCouplesFeasible i := by
  simp [hospitalsResidentsWithCouplesDec, bitDecode_bitEncode]

/-- Two hospitals of capacity one, `h₀` ranking the couple member `1` above the single
resident `0`, and `h₁` with the preference list `p₁`; the single resident `0` ranks `h₀` above
`h₁`; the couple `(1, 2)` accepts only the pair `(h₀, h₁)`. -/
private abbrev market (p₁ : List ℕ) : HospitalsResidentsWithCouplesInstance :=
  ([(1, [1, 0]), (1, p₁)], [(0, [0, 1])], [((1, 2), [(0, 1)])])

/-- The couple at `(h₀, h₁)` and the single resident unassigned. -/
private def coupleIn : ℕ → Option ℕ := fun r =>
  if r = 1 then some 0 else if r = 2 then some 1 else none

/-- A lone continuation bit is a truncated instance encoding. -/
example : hospitalsResidentsWithCouplesDec [true] = false := by
  have h : bitDecode (α := HospitalsResidentsWithCouplesInstance) [true] = none := rfl
  simp [hospitalsResidentsWithCouplesDec, h]

/-- When `h₁` ranks the couple member `2` first, placing the couple at `(h₀, h₁)` is
MM-stable: both hospitals prefer their couple member to the single resident, and the couple has
its only acceptable pair. -/
example : hospitalsResidentsWithCouplesDec (bitEncode (market [2, 0])) = true := by
  apply (accepts_encoding _).2
  refine ⟨?_, coupleIn, ?_, ?_⟩
  · simp only [WellFormed, residents, hospitalPrefs]
    refine ⟨by decide, by decide, by decide, by decide, ?_, by decide, by decide⟩
    intro h hh
    have : h = 0 ∨ h = 1 := by simp at hh; omega
    rcases this with rfl | rfl <;> decide
  · simp only [IsMatching, assigned, residents, capacity, coupleIn]
    refine ⟨by simp, by decide, ?_⟩
    intro h hh
    have : h = 0 ∨ h = 1 := by simp at hh; omega
    rcases this with rfl | rfl <;> decide
  · simp [IsMMStable, BlockedBySingle, BlockedByCoupleAndHospital, BlockedByCoupleAndPair,
      CouplePrefers, Undersubscribed, PrefersToSome, Prefers, assigned, residents, capacity,
      hospitalPrefs, coupleIn]

/-- When `h₁` ranks the single resident `0` first, every matching is blocked: with the couple
placed, `0` and `h₁` block; with the couple unplaced, either `0` is at `h₀` and the couple
blocks with `(h₀, h₁)`, or `0` is elsewhere and blocks with the empty `h₀`. -/
example : hospitalsResidentsWithCouplesDec (bitEncode (market [0, 2])) = false := by
  rw [Bool.eq_false_iff]
  intro hacc
  obtain ⟨-, M, ⟨hs, hc, hcap⟩, hsingle, hhosp, hpair⟩ := (accepts_encoding _).1 hacc
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hs hc
  simp only [exists_eq_left] at hc
  rcases hc with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · -- the couple is unassigned
    cases h₀ : M 0 with
    | none =>
      apply hsingle
      refine ⟨_, List.mem_cons_self, 0, List.mem_cons_self, ?_, Or.inl ?_⟩
      · simp [h₀]
      · simp [Undersubscribed, assigned, residents, capacity, h₀, h₁, h₂]
    | some h =>
      rw [h₀] at hs
      simp at hs
      rcases hs with rfl | rfl
      · apply hpair
        refine ⟨_, List.mem_cons_self, (0, 1), List.mem_cons_self, by simp [h₁],
          by simp [h₂], by simp [CouplePrefers, h₁, h₂], Or.inl ⟨by decide, Or.inr ?_,
          Or.inl ?_⟩⟩
        · simp [PrefersToSome, Prefers, assigned, residents, hospitalPrefs, h₀, h₁, h₂]
        · simp [Undersubscribed, assigned, residents, capacity, h₀, h₁, h₂]
      · apply hsingle
        refine ⟨_, List.mem_cons_self, 0, List.mem_cons_self, ?_, Or.inl ?_⟩
        · simp [h₀, Prefers]
        · simp [Undersubscribed, assigned, residents, capacity, h₀, h₁, h₂]
  · -- the couple is at `(h₀, h₁)`
    cases h₀ : M 0 with
    | none =>
      apply hsingle
      refine ⟨_, List.mem_cons_self, 1, by simp, by simp [h₀], Or.inr ?_⟩
      simp [PrefersToSome, Prefers, assigned, residents, hospitalPrefs, h₀, h₁, h₂]
    | some h =>
      exfalso
      rw [h₀] at hs
      simp at hs
      rcases hs with rfl | rfl
      · have := hcap 0 (by decide)
        simp [assigned, residents, capacity, h₀, h₁, h₂] at this
      · have := hcap 1 (by decide)
        simp [assigned, residents, capacity, h₀, h₁, h₂] at this

/-- The no-instance above is well formed, so it is rejected for infeasibility. -/
example : WellFormed (market [0, 2]) := by
  simp only [WellFormed, residents, hospitalPrefs]
  refine ⟨by decide, by decide, by decide, by decide, ?_, by decide, by decide⟩
  intro h hh
  have : h = 0 ∨ h = 1 := by simp at hh; omega
  rcases this with rfl | rfl <;> decide

end MetaMathlibExt.Complexity.NPComplete.HospitalsResidentsWithCouples
