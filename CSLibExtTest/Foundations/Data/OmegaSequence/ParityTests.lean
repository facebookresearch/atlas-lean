/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Foundations.Data.OmegaSequence.Parity

/-!
# Tests for the max-parity condition

* An unbounded sequence with `0` at even indices and the index itself at odd indices: `0` is the
  only value occurring infinitely often, so the sequence satisfies `ParityEven` although no tail is
  bounded by `0`.
* A strictly increasing sequence has no value occurring infinitely often, so neither parity holds.
* `0, 1, 0, 1, ...` satisfies `ParityOdd`.
-/

@[expose] public section

namespace Cslib.ωSequence.ParityTests

open Filter

/-- `0` at even indices, the index itself at odd indices. -/
def zeroOrIndex : ωSequence ℕ := fun k => if k % 2 = 0 then 0 else k

theorem frequently_zeroOrIndex_iff (m : ℕ) :
    (∃ᶠ k in atTop, zeroOrIndex k = m) ↔ m = 0 := by
  constructor
  · intro h
    obtain ⟨k, hk, hkm⟩ := frequently_atTop.mp h (m + 1)
    change (if k % 2 = 0 then 0 else k) = m at hkm
    split_ifs at hkm <;> omega
  · rintro rfl
    rw [frequently_atTop]
    intro a
    exact ⟨2 * a, by omega, by change (if 2 * a % 2 = 0 then 0 else 2 * a) = 0; simp⟩

/-- `ParityEven` holds although infinitely many entries exceed `0`. -/
example : ParityEven zeroOrIndex :=
  ⟨0, ⟨0, rfl⟩, (frequently_zeroOrIndex_iff 0).mpr rfl,
    fun m hm => ((frequently_zeroOrIndex_iff m).mp hm).le⟩

/-- No tail of `zeroOrIndex` is bounded by `0`. -/
example : ¬ ∀ᶠ k in atTop, zeroOrIndex k ≤ 0 := by
  intro h
  obtain ⟨n, hn⟩ := eventually_atTop.mp h
  have := hn (2 * n + 1) (by omega)
  change (if (2 * n + 1) % 2 = 0 then 0 else 2 * n + 1) ≤ 0 at this
  split_ifs at this <;> omega

/-- The identity sequence `0, 1, 2, ...`. -/
def natSeq : ωSequence ℕ := fun k : ℕ => k

/-- The identity sequence has no value occurring infinitely often: neither parity holds. -/
example : ¬ ParityEven natSeq ∧ ¬ ParityOdd natSeq := by
  have hnot : ∀ n, ¬ ∃ᶠ k in atTop, natSeq k = n := fun n h => by
    obtain ⟨k, hk, hkn⟩ := frequently_atTop.mp h (n + 1)
    change k = n at hkn
    omega
  exact ⟨fun ⟨n, _, hn, _⟩ => hnot n hn, fun ⟨n, _, hn, _⟩ => hnot n hn⟩

/-- `0, 1, 0, 1, ...` is won by the odd parity. -/
example : ParityOdd (fun k => k % 2 : ωSequence ℕ) := by
  refine ⟨1, odd_one, ?_, fun m hm => ?_⟩
  · rw [frequently_atTop]
    intro a
    exact ⟨2 * a + 1, by omega, by change (2 * a + 1) % 2 = 1; omega⟩
  · obtain ⟨k, hk⟩ := hm.exists
    change k % 2 = m at hk
    omega

end Cslib.ωSequence.ParityTests
