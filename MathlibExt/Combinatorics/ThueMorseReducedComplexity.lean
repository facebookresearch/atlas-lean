/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.ReducedComplexities
import Mathlib.Order.Interval.Set.Nat

/-!
# Reduced complexity of the Thue–Morse word at even lengths

`rhoRed_thueMorse_even` gives the recurrences for lengths congruent to zero and two modulo
four. We count changes of letter in a sliding window. In every aligned block of four adjacent
pairs, the first three change indicators are 1, 0, 1, and the fourth is the indicator at the
corresponding position of the original sequence.
-/

namespace MathlibExt.Combinatorics.ReducedComplexitiesWanted

open MetaMathlibExt InfiniteWord

private theorem thueMorse_double (i : ℕ) : thueMorse (2 * i) = thueMorse i := by
  rcases i with _ | i
  · rfl
  · simp [thueMorse]

private theorem thueMorse_double_add_one (i : ℕ) : thueMorse (2 * i + 1) = !thueMorse i := by
  rw [Nat.add_comm, thueMorse, Nat.digits_add 2 (by decide) 1 i (by decide) (Or.inl (by decide))]
  simp [thueMorse, ← decide_not]
  omega

-- The second half of a block of length 2^(k+1) complements its first half.
private theorem thueMorse_shift (k i : ℕ) (hi : i < 2 ^ k) :
    thueMorse (2 ^ k + i) = !thueMorse i := by
  induction k generalizing i with
  | zero =>
    have : i = 0 := by simpa using hi
    subst i
    decide +kernel
  | succ k ih =>
    rw [pow_succ] at hi ⊢
    obtain h | h : i = 2 * (i / 2) ∨ i = 2 * (i / 2) + 1 := by omega
    · rw [show 2 ^ k * 2 + i = 2 * (2 ^ k + i / 2) by omega, thueMorse_double,
        ih _ (by omega), ← thueMorse_double (i / 2), ← h]
    · rw [show 2 ^ k * 2 + i = 2 * (2 ^ k + i / 2) + 1 by omega,
        thueMorse_double_add_one, ih _ (by omega), ← thueMorse_double_add_one (i / 2), ← h]

private def edge (i : ℕ) : ℕ := if thueMorse i = thueMorse (i + 1) then 0 else 1

private theorem edge_le_one (i : ℕ) : edge i ≤ 1 := by
  unfold edge
  split <;> decide

-- A length-(n+1) factor at i contains n adjacent pairs.
private def changes : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, i => changes n (i + 1) + edge i

private theorem changes_snoc (n i : ℕ) :
    changes (n + 1) i = changes n i + edge (i + n) := by
  induction n generalizing i with
  | zero => simp [changes]
  | succ n ih =>
    change changes (n + 1) (i + 1) + edge i = changes n (i + 1) + edge i + _
    rw [ih, show i + 1 + n = i + (n + 1) by omega]
    omega

private theorem changes_shift (k n i : ℕ) (hi : i + n < 2 ^ k) :
    changes n (2 ^ k + i) = changes n i := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp only [changes, Nat.add_assoc, ih (i + 1) (by omega), edge,
      thueMorse_shift k i (by omega), thueMorse_shift k (i + 1) (by omega)]
    cases thueMorse i <;> cases thueMorse (i + 1) <;> rfl

-- Either first letter occurs with each attainable number of changes.
private theorem exists_start (n i : ℕ) (b : Bool) :
    ∃ j, thueMorse j = b ∧ changes n j = changes n i := by
  by_cases h : thueMorse i = b
  · exact ⟨i, h, rfl⟩
  let k := i + n
  have hk : i + n < 2 ^ k := Nat.lt_two_pow_self
  refine ⟨2 ^ k + i, ?_, changes_shift k n i hk⟩
  rw [thueMorse_shift k i (by omega)]
  cases b <;> cases ht : thueMorse i <;> simp_all

private def alternatingWord : Bool → ℕ → List Bool
  | b, 0 => [b]
  | b, n + 1 => b :: alternatingWord (!b) n

private theorem alternatingWord_length (b : Bool) (n : ℕ) :
    (alternatingWord b n).length = n + 1 := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih => simp [alternatingWord, ih]

private theorem alternatingWord_injective :
    Function.Injective (fun p : Bool × ℕ => alternatingWord p.1 p.2) := by
  rintro ⟨b, n⟩ ⟨c, m⟩ h
  change alternatingWord b n = alternatingWord c m at h
  have hl := congrArg List.length h
  simp only [alternatingWord_length, Nat.add_right_cancel_iff] at hl
  subst m
  cases n <;> simpa [alternatingWord] using congrArg List.head? h

private theorem factorList_succ (n i : ℕ) :
    factorList thueMorse (n + 1) i = thueMorse i :: factorList thueMorse n (i + 1) := by
  simp only [factorList, List.ofFn_succ, factor_apply, Fin.val_zero, Nat.add_zero]
  congr 2
  funext j
  change thueMorse (i + (j.val + 1)) = thueMorse (i + 1 + j.val)
  congr 1
  omega

private theorem redWord_factor (n i : ℕ) :
    redWord (factorList thueMorse (n + 1) i) = alternatingWord (thueMorse i) (changes n i) := by
  induction n generalizing i with
  | zero =>
    simp [factorList, redWord, changes, alternatingWord]
  | succ n ih =>
    rw [factorList_succ, factorList_succ n (i + 1), redWord, ← factorList_succ, ih]
    by_cases h : thueMorse i = thueMorse (i + 1)
    · simp [h, changes, edge]
    · have h' : (!thueMorse i) = thueMorse (i + 1) := by
        cases hi : thueMorse i <;> cases hj : thueMorse (i + 1) <;> simp_all
      simp [h, changes, edge, alternatingWord, h']

private structure ChangeBounds (n lo hi : ℕ) : Prop where
  bounds : ∀ i, lo ≤ changes n i ∧ changes n i ≤ hi
  reachesLo : lo ∈ Set.range (changes n)
  reachesHi : hi ∈ Set.range (changes n)

private theorem exists_changeBounds (n : ℕ) : ∃ lo hi, ChangeBounds n lo hi := by
  have le_length (k i : ℕ) : changes k i ≤ k := by
    induction k generalizing i with
    | zero => rfl
    | succ k ih =>
      rw [changes]
      exact Nat.add_le_add (ih _) (edge_le_one i)
  let s := Set.range (changes n)
  have hb : BddAbove s := ⟨n, fun _ ⟨i, hi⟩ => hi ▸ le_length n i⟩
  have hne : s.Nonempty := Set.range_nonempty _
  exact ⟨sInf s, sSup s, fun i =>
    ⟨Nat.sInf_le (Set.mem_range_self i), le_csSup hb (Set.mem_range_self i)⟩,
    Nat.sInf_mem hne, Nat.sSup_mem hne hb⟩

-- Sliding the window changes its count by at most one, so it takes every intermediate value.
private theorem changes_range {n lo hi : ℕ} (h : ChangeBounds n lo hi) :
    Set.range (changes n) = Set.Icc lo hi := by
  apply Set.Subset.antisymm
  · rintro _ ⟨i, rfl⟩
    exact h.bounds i
  intro x ⟨hlo, hhi⟩
  by_contra hmiss
  have ne (i : ℕ) : changes n i ≠ x := fun he => hmiss ⟨i, he⟩
  have side (i : ℕ) : changes n i < x ↔ changes n 0 < x := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [← ih]
      have hs := changes_snoc n i
      change changes n (i + 1) + edge i = changes n i + edge (i + n) at hs
      have := edge_le_one i
      have := edge_le_one (i + n)
      have := ne i
      have := ne (i + 1)
      omega
  obtain ⟨i, hi'⟩ := h.reachesLo
  obtain ⟨j, hj⟩ := h.reachesHi
  have := (side i).trans (side j).symm
  have := ne i
  omega

private theorem rhoRed_of_bounds {n lo hi : ℕ} (h : ChangeBounds n lo hi) :
    rhoRed thueMorse (n + 1) = 2 * (hi + 1 - lo) := by
  let encode (p : Bool × ℕ) := alternatingWord p.1 p.2
  have words : (fun v => redWord (List.ofFn v)) '' factorSet thueMorse (n + 1) =
      encode '' (Set.univ ×ˢ Set.Icc lo hi) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨v, ⟨i, rfl⟩, rfl⟩
      exact ⟨(thueMorse i, changes n i), ⟨Set.mem_univ _, h.bounds i⟩, (redWord_factor n i).symm⟩
    · rintro _ ⟨⟨b, a⟩, ⟨_, ha⟩, rfl⟩
      obtain ⟨i, hi⟩ : a ∈ Set.range (changes n) := changes_range h ▸ ha
      obtain ⟨j, hj, hj'⟩ := exists_start n i b
      refine ⟨factor thueMorse (n + 1) j, ⟨j, rfl⟩, ?_⟩
      exact (redWord_factor n j).trans (by simp [encode, hj, hj', hi])
  rw [rhoRed, words, Set.ncard_image_of_injective _ alternatingWord_injective, Set.ncard_prod]
  simp

private theorem edge_double (i : ℕ) : edge (2 * i) = 1 := by
  rw [edge, thueMorse_double, thueMorse_double_add_one]
  cases thueMorse i <;> rfl

private theorem edge_double_add_one (i : ℕ) : edge (2 * i + 1) = 1 - edge i := by
  simp only [edge, thueMorse_double_add_one, show 2 * i + 1 + 1 = 2 * (i + 1) by omega,
    thueMorse_double]
  cases thueMorse i <;> cases thueMorse (i + 1) <;> rfl

private theorem edge_four (i : ℕ) :
    edge (4 * i) = 1 ∧ edge (4 * i + 1) = 0 ∧
      edge (4 * i + 2) = 1 ∧ edge (4 * i + 3) = edge i := by
  rw [show 4 * i + 3 = 2 * (2 * i + 1) + 1 by omega,
    show 4 * i + 2 = 2 * (2 * i + 1) by omega, show 4 * i = 2 * (2 * i) by omega]
  simp [edge_double_add_one, edge_double]
  have := edge_le_one i
  omega

private theorem edge_four_prefix (i r : ℕ) (hr : r < 3) :
    edge (4 * i + r) = if r = 1 then 0 else 1 := by
  obtain ⟨h₀, h₁, h₂, _⟩ := edge_four i
  obtain rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  · exact h₀
  · exact h₁
  · exact h₂

private theorem changes_aligned (n i : ℕ) :
    changes (4 * n) (4 * i) = 2 * n + changes n i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 4 * (n + 1) = 4 * n + 1 + 1 + 1 + 1 by omega]
    simp only [changes_snoc, ih]
    obtain ⟨h₀, h₁, h₂, h₃⟩ := edge_four (i + n)
    simp only [Nat.mul_add, Nat.add_assoc] at h₀ h₁ h₂ h₃ ⊢
    omega

-- Shifting the start by up to three positions replaces each removed edge by an equal one.
private theorem changes_four_mul (n i r : ℕ) (hr : r < 4) :
    changes (4 * n) (4 * i + r) = 2 * n + changes n i := by
  induction r with
  | zero => exact changes_aligned n i
  | succ r ih =>
    have hs := changes_snoc (4 * n) (4 * i + r)
    change changes (4 * n) (4 * i + r + 1) + edge (4 * i + r) = _ at hs
    rw [ih (by omega), show 4 * i + r + 4 * n = 4 * (i + n) + r by omega,
      edge_four_prefix i r (by omega), edge_four_prefix (i + n) r (by omega)] at hs
    exact Nat.add_right_cancel hs

private theorem bounds_four_add_one {n lo hi : ℕ} (h : ChangeBounds n lo hi) :
    ChangeBounds (4 * n + 1) (2 * n + lo) (2 * n + hi + 1) := by
  have count (i r : ℕ) (hr : r < 4) :
      changes (4 * n + 1) (4 * i + r) = 2 * n + changes n i + edge (4 * (i + n) + r) := by
    rw [changes_snoc, changes_four_mul n i r hr, show 4 * i + r + 4 * n = 4 * (i + n) + r by omega]
  constructor
  · intro j
    have hc := count (j / 4) (j % 4) (by omega)
    rw [show 4 * (j / 4) + j % 4 = j by omega] at hc
    have := h.bounds (j / 4)
    have := edge_le_one (4 * (j / 4 + n) + j % 4)
    omega
  · obtain ⟨i, hi⟩ := h.reachesLo
    exact ⟨4 * i + 1, by rw [count i 1 (by decide), (edge_four (i + n)).2.1, hi, Nat.add_zero]⟩
  · obtain ⟨i, hi⟩ := h.reachesHi
    exact ⟨4 * i + 0, by rw [count i 0 (by decide), Nat.add_zero, (edge_four (i + n)).1, hi]⟩

private theorem bounds_four_sub_one {n lo hi : ℕ} (hn : 0 < n) (h : ChangeBounds n lo hi) :
    ChangeBounds (4 * n - 1) (2 * n + lo - 1) (2 * n + hi) := by
  have count (i r : ℕ) (hr : r < 4) :
      changes (4 * n - 1) (4 * i + r) + edge (4 * i + r + (4 * n - 1)) =
        2 * n + changes n i := by
    rw [← changes_snoc, show 4 * n - 1 + 1 = 4 * n by omega, changes_four_mul n i r hr]
  constructor
  · intro j
    have hc := count (j / 4) (j % 4) (by omega)
    rw [show 4 * (j / 4) + j % 4 = j by omega] at hc
    have := h.bounds (j / 4)
    have := edge_le_one (j + (4 * n - 1))
    omega
  · obtain ⟨i, hi⟩ := h.reachesLo
    refine ⟨4 * i + 1, ?_⟩
    have hc := count i 1 (by decide)
    rw [show 4 * i + 1 + (4 * n - 1) = 4 * (i + n) by omega, (edge_four (i + n)).1, hi] at hc
    omega
  · obtain ⟨i, hi⟩ := h.reachesHi
    refine ⟨4 * i + 2, ?_⟩
    have hc := count i 2 (by decide)
    rw [show 4 * i + 2 + (4 * n - 1) = 4 * (i + n) + 1 by omega,
      (edge_four (i + n)).2.1, hi, Nat.add_zero] at hc
    exact hc

/-- **Reduced complexity of the Thue–Morse word at even lengths.** Let $t$ be the Thue–Morse
sequence and $\rho^{\mathrm{red}}_t$ its reduced factor complexity. For every natural number
$m \ge 1$, $\rho^{\mathrm{red}}_t(4m) = \rho^{\mathrm{red}}_t(m+1) + 2$, and for every natural
number $m \ge 0$, $\rho^{\mathrm{red}}_t(4m+2) = \rho^{\mathrm{red}}_t(m+1) + 2$.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Theorem 1. -/
public theorem rhoRed_thueMorse_even (m : ℕ) :
    rhoRed thueMorse (4 * (m + 1)) = rhoRed thueMorse (m + 2) + 2 ∧
      rhoRed thueMorse (4 * m + 2) = rhoRed thueMorse (m + 1) + 2 := by
  constructor
  · obtain ⟨lo, hi, h⟩ := exists_changeBounds (m + 1)
    have hf := rhoRed_of_bounds (bounds_four_sub_one (by omega) h)
    rw [show 4 * (m + 1) - 1 + 1 = 4 * (m + 1) by omega] at hf
    rw [hf, rhoRed_of_bounds h]
    have := h.bounds 0
    omega
  · obtain ⟨lo, hi, h⟩ := exists_changeBounds m
    rw [rhoRed_of_bounds (bounds_four_add_one h), rhoRed_of_bounds h]
    have := h.bounds 0
    omega

end MathlibExt.Combinatorics.ReducedComplexitiesWanted
