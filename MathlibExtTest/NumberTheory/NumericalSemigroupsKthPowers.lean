/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.NumericalSemigroupsKthPowers
import Mathlib.NumberTheory.FrobeniusNumber

/-!
# Embedding dimension and conductor bounds

In an earlier tail, each power is the sum of two copies of its predecessor.
At the start of its own tail it is minimal. Thus the growth hypothesis holds with slope one.

The conductor inequality gives a sharp upper bound for the generators 6 and 5.
It also applies when the common divisor is zero.
-/

namespace MetaMathlibExt.embeddingDimension_le_of_firstAppearance_ge

private abbrev tail (m : ℕ) := AddSubmonoid.closure ((fun i : ℕ ↦ (2 : ℕ) ^ i) '' Set.Ici m)

private abbrev generators (m : ℕ) : Set ℕ :=
  {s | s ∈ tail m ∧ s ≠ 0 ∧ ∀ a ∈ tail m, ∀ b ∈ tail m, a + b = s → a = 0 ∨ b = 0}

example (n : ℕ) (hn : 1 ≤ n) : (generators n).ncard ≤ 1 := by
  have hr (k : ℕ) (hk : 1 ≤ k) : k ≤ sInf {m : ℕ | 1 ≤ m ∧ 2 ^ k ∈ generators m} := by
    apply le_csInf
    · refine ⟨k, hk, AddSubmonoid.subset_closure ⟨k, le_refl k, rfl⟩, pow_ne_zero _ (by decide),
        ?_⟩
      have hdvd {a : ℕ} (ha : a ∈ tail k) : 2 ^ k ∣ a := by
        induction ha using AddSubmonoid.closure_induction with
        | mem _ h =>
          obtain ⟨j, hj, rfl⟩ := h
          exact pow_dvd_pow _ hj
        | zero => exact dvd_zero _
        | add _ _ _ _ ha hb => exact dvd_add ha hb
      intro a ha b _ hab
      by_cases ha₀ : a = 0
      · exact Or.inl ha₀
      · have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero ha₀) (hdvd ha)
        exact Or.inr (by omega)
    · rintro m ⟨_, _, _, h⟩
      by_contra! hlt
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      have hj : 2 ^ j ∈ tail m := AddSubmonoid.subset_closure ⟨j, Nat.le_of_lt_succ hlt, rfl⟩
      simpa using h _ hj _ hj (by rw [pow_succ, Nat.mul_two])
  have hx := pow_right_strictMono₀ (by decide : 1 < (2 : ℕ))
  have h := embeddingDimension_le_of_firstAppearance_ge _ hx 1 zero_lt_one
    (fun k hk ↦ by simpa using hr k hk) n hn
  change ((generators n).ncard : ℤ) ≤ _ at h
  simpa using h

end MetaMathlibExt.embeddingDimension_le_of_firstAppearance_ge

namespace MetaMathlibExt.conductor_union_le

private noncomputable abbrev conductor (s : Set ℕ) :=
  sInf {m : ℕ | ∀ j ≥ m, j ∈ AddSubmonoid.closure s}

private lemma conductor_pair_le (a b : ℕ) (hab : a.Coprime b) (ha : 1 < a) (hb : 1 < b) :
    conductor {a, b} ≤ a * b - a - b + 1 := by
  apply Nat.sInf_le
  exact fun j hj ↦ (frobeniusNumber_iff.mp (frobeniusNumber_pair hab ha hb)).2 j hj

example : conductor {6, 5} ≤ 20 := by
  have h := conductor_union_le {6} {5} (Set.singleton_nonempty _) (Set.singleton_nonempty _)
    (fun g hg ↦ Nat.eq_one_of_dvd_one (Nat.dvd_gcd (hg 6 (Or.inl rfl)) (hg 5 (Or.inr rfl))))
    2 (by simp)
  simp only [Set.image_singleton, Set.singleton_union] at h
  have h₁ : conductor {3, 5} ≤ 8 := conductor_pair_le 3 5 (by decide) (by decide) (by decide)
  have h₂ : conductor {5, 2} ≤ 4 := conductor_pair_le 5 2 (by decide) (by decide) (by decide)
  exact h.trans (add_le_add (Nat.mul_le_mul_left 2 h₁) h₂)

example (B : Set ℕ) (hB : B.Nonempty) (hgcd : Nat.setGcd B = 1) :
    conductor ({0} ∪ B) ≤ conductor (B ∪ {0}) := by
  have h := conductor_union_le {0} B (Set.singleton_nonempty _) hB (fun g hg ↦ by
    apply Nat.eq_one_of_dvd_one
    rw [← hgcd]
    exact Nat.dvd_setGcd_iff.mpr fun b hb ↦ hg b (Or.inr hb)) 0 (by simp)
  simpa only [Nat.zero_mul, Nat.zero_add] using h

end MetaMathlibExt.conductor_union_le
