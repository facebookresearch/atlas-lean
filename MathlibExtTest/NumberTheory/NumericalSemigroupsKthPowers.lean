/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.NumericalSemigroupsKthPowers

/-!
# Tests for tail semigroups

In a tail of the powers of two, each power after the first is twice its predecessor.
At the start of its own tail it is minimal. So its first appearance is its own index: the growth
hypothesis holds with slope one, each power is a minimal generator of its own tail only, and every
tail has exactly one minimal generator.

For squares, the recursion gives explicit conductor bounds starting from the tail containing one.
-/

namespace MetaMathlibExt.embeddingDimension_le_of_firstAppearance_ge

private abbrev tail (m : ℕ) := AddSubmonoid.closure ((fun i : ℕ ↦ (2 : ℕ) ^ i) '' Set.Ici m)

private abbrev generators (m : ℕ) : Set ℕ :=
  {s | s ∈ tail m ∧ s ≠ 0 ∧ ∀ a ∈ tail m, ∀ b ∈ tail m, a + b = s → a = 0 ∨ b = 0}

/-- Every element of the `k`-th tail is a multiple of `2 ^ k`, so `2 ^ k` is minimal there. -/
private lemma pow_mem_generators (k : ℕ) : 2 ^ k ∈ generators k := by
  refine ⟨AddSubmonoid.subset_closure ⟨k, le_refl k, rfl⟩, pow_ne_zero _ (by decide), ?_⟩
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

/-- In an earlier tail, `2 ^ k` is the sum of two copies of its predecessor, so the first tail
with `2 ^ k` as a minimal generator is the `k`-th. -/
private lemma firstAppearance_eq (k : ℕ) (hk : 1 ≤ k) :
    sInf {m : ℕ | 1 ≤ m ∧ 2 ^ k ∈ generators m} = k := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨hk, pow_mem_generators k⟩
  refine le_csInf ⟨k, hk, pow_mem_generators k⟩ ?_
  rintro m ⟨_, _, _, h⟩
  by_contra! hlt
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hj : 2 ^ j ∈ tail m := AddSubmonoid.subset_closure ⟨j, Nat.le_of_lt_succ hlt, rfl⟩
  simpa using h _ hj _ hj (by rw [pow_succ, Nat.mul_two])

example (n : ℕ) (hn : 1 ≤ n) : (generators n).ncard ≤ 1 := by
  have hx := pow_right_strictMono₀ (by decide : 1 < (2 : ℕ))
  have h := embeddingDimension_le_of_firstAppearance_ge _ hx 1 zero_lt_one
    (fun k hk ↦ by simpa using (firstAppearance_eq k hk).ge) n hn
  change ((generators n).ncard : ℤ) ≤ _ at h
  simpa using h

/-- The power `2 ^ k` is a minimal generator of the `n`-th tail only for `n = k`. -/
example (k n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) : 2 ^ k ∈ generators n ↔ n = k := by
  have hx := pow_right_strictMono₀ (by decide : 1 < (2 : ℕ))
  have h := (mem_minimalGenerators_iff_firstAppearance_le _ hx k n hk hn).1
  change 2 ^ k ∈ generators n ↔ sInf {m : ℕ | 1 ≤ m ∧ 2 ^ k ∈ generators m} ≤ n ∧ n ≤ k at h
  rw [h, firstAppearance_eq k hk]
  omega

/-- Every tail has exactly one minimal generator, so the singleton bound is attained. -/
example (n : ℕ) (hn : 1 ≤ n) : (generators n).ncard = 1 := by
  have hx := pow_right_strictMono₀ (by decide : 1 < (2 : ℕ))
  have h := (mem_minimalGenerators_iff_firstAppearance_le _ hx n n hn hn).2
  change (generators n).ncard =
    {j : ℕ | 1 ≤ j ∧ sInf {m : ℕ | 1 ≤ m ∧ 2 ^ j ∈ generators m} ≤ n ∧ n ≤ j}.ncard at h
  have hset : {j : ℕ | 1 ≤ j ∧ sInf {m : ℕ | 1 ≤ m ∧ 2 ^ j ∈ generators m} ≤ n ∧ n ≤ j} = {n} := by
    ext j
    refine ⟨fun ⟨hj, hr, hnj⟩ ↦ ?_, fun hj ↦ ?_⟩
    · rw [firstAppearance_eq j hj] at hr
      exact le_antisymm hr hnj
    · subst hj
      exact ⟨hn, (firstAppearance_eq j hn).le, le_rfl⟩
  rw [h, hset, Set.ncard_singleton]

end MetaMathlibExt.embeddingDimension_le_of_firstAppearance_ge

namespace MetaMathlibExt.conductor_powers_le

private noncomputable abbrev squareConductor (n : ℕ) :=
  sInf {c : ℕ | ∀ j ≥ c, j ∈ AddSubmonoid.closure ((fun i : ℕ => i ^ 2) '' Set.Ici n)}

/-- Starting from conductor zero at index one, recurse through an even and an odd index. -/
example : squareConductor 3 ≤ 300 := by
  have h₁ : squareConductor 1 = 0 := by
    apply Nat.le_zero.mp
    apply Nat.sInf_le
    intro j _
    have h : 1 ∈ AddSubmonoid.closure ((fun i : ℕ => i ^ 2) '' Set.Ici 1) :=
      AddSubmonoid.subset_closure ⟨1, by decide, rfl⟩
    simpa using (AddSubmonoid.nsmul_mem _ h j)
  have h₂ : squareConductor 2 ≤ 4 * squareConductor 1 + 48 :=
    conductor_powers_le 2 2 (by decide) (by decide)
  have h₃ : squareConductor 3 ≤ 4 * squareConductor 2 + 108 :=
    conductor_powers_le 3 2 (by decide) (by decide)
  omega

end MetaMathlibExt.conductor_powers_le
