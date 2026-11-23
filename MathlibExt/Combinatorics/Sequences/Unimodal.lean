/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum

/-!
# Unimodal and log-concave sequences

Definitions from Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed. (author's draft of
15 July 2011, https://math.mit.edu/~rstan/ec/ec1.pdf), Chapter 1, Exercise 50, for a finite
sequence `(a₀, a₁, …, aₙ)` of real numbers, represented by `a : ℕ → ℝ` and the last index `n`
(values beyond `n` are ignored):

* `IsUnimodal a n`: `a₀ ≤ a₁ ≤ ⋯ ≤ aⱼ ≥ aⱼ₊₁ ≥ ⋯ ≥ aₙ` for some `0 ≤ j ≤ n`;
* `IsLogConcave a n`: `aᵢ² ≥ aᵢ₋₁ aᵢ₊₁` for `1 ≤ i ≤ n - 1`;
* `NoInternalZeros a n`: there are no `i < j < k ≤ n` with `aᵢ ≠ 0`, `aⱼ = 0`, `aₖ ≠ 0`.

Main results:

* `isUnimodal_of_isLogConcave`: a log-concave sequence of nonnegative reals with no internal zeros
  is unimodal (Exercise 1.50(a)).
* `choose_isLogConcave`, `choose_isUnimodal`: each row of Pascal's triangle is log-concave, hence
  unimodal (a direct computation with the ratio of consecutive binomial coefficients).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Sequences.Unimodal

/-- **Unimodal sequence.** A finite sequence `(a₀, …, aₙ)` of real numbers is unimodal if
`a₀ ≤ a₁ ≤ ⋯ ≤ aⱼ ≥ aⱼ₊₁ ≥ ⋯ ≥ aₙ` for some `0 ≤ j ≤ n` (Stanley, *Enumerative Combinatorics*,
vol. 1, 2nd ed., author's draft of 15 July 2011, Chapter 1, Exercise 50). -/
def IsUnimodal (a : ℕ → ℝ) (n : ℕ) : Prop :=
  ∃ j ≤ n, (∀ i < j, a i ≤ a (i + 1)) ∧ ∀ i, j ≤ i → i < n → a (i + 1) ≤ a i

/-- **Log-concave sequence.** A finite sequence `(a₀, …, aₙ)` of real numbers is log-concave if
`aᵢ² ≥ aᵢ₋₁ aᵢ₊₁` for `1 ≤ i ≤ n - 1` (Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed.,
author's draft of 15 July 2011, Chapter 1, Exercise 50). Written with `i = k + 1`. -/
def IsLogConcave (a : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ k, k + 2 ≤ n → a k * a (k + 2) ≤ a (k + 1) ^ 2

/-- **No internal zeros.** A finite sequence `(a₀, …, aₙ)` has no internal zeros if there do not
exist `i < j < k ≤ n` with `aᵢ ≠ 0`, `aⱼ = 0` and `aₖ ≠ 0` (Stanley, *Enumerative
Combinatorics*, vol. 1, 2nd ed., author's draft of 15 July 2011, Chapter 1, Exercise 50). -/
def NoInternalZeros (a : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ i j k, i < j → j < k → k ≤ n → a i ≠ 0 → a k ≠ 0 → a j ≠ 0

section Proof

variable {a : ℕ → ℝ} {n : ℕ}

/-- Once a log-concave nonnegative sequence without internal zeros strictly drops at `i`, it is
weakly decreasing, and below `aᵢ`, from `i + 1` on. -/
private lemma descent_propagates (hnn : ∀ i ≤ n, 0 ≤ a i) (hlc : IsLogConcave a n)
    (hnz : NoInternalZeros a n) {i : ℕ} (hin : i + 1 ≤ n) (hdrop : a (i + 1) < a i) :
    ∀ k, i ≤ k → k + 1 ≤ n → a (k + 1) ≤ a k ∧ (a (k + 1) < a k ∨ a (k + 1) = 0) := by
  have hai : a i ≠ 0 := (lt_of_le_of_lt (hnn _ hin) hdrop).ne'
  intro k hik hkn
  induction k, hik using Nat.le_induction with
  | base => exact ⟨hdrop.le, Or.inl hdrop⟩
  | succ k hik ih =>
    obtain ⟨hle, hlt | hz⟩ := ih (by omega)
    · by_cases hk1 : a (k + 1) = 0
      · have : a (k + 2) = 0 := by
          by_contra h
          exact hnz i (k + 1) (k + 2) (by omega) (by omega) hkn hai h hk1
        exact ⟨by rw [this, hk1], Or.inr this⟩
      · have hpos1 : 0 < a (k + 1) := lt_of_le_of_ne (hnn _ (by omega)) (Ne.symm hk1)
        have hposk : 0 < a k := lt_of_le_of_lt (hnn _ (by omega)) hlt
        have hlc' := hlc k hkn
        have : a (k + 2) < a (k + 1) := by
          by_contra h
          have h := not_lt.mp h
          nlinarith
        exact ⟨this.le, Or.inl this⟩
    · have : a (k + 2) = 0 := by
        by_contra h
        exact hnz i (k + 1) (k + 2) (by omega) (by omega) hkn hai h hz
      exact ⟨by rw [this, hz], Or.inr this⟩

/-- Symmetrically, once the sequence strictly rises at `i`, it is weakly increasing up to `i`. -/
private lemma ascent_propagates (hnn : ∀ i ≤ n, 0 ≤ a i) (hlc : IsLogConcave a n)
    (hnz : NoInternalZeros a n) {i : ℕ} (hin : i + 1 ≤ n) (hrise : a i < a (i + 1)) :
    ∀ d, d ≤ i → a (i - d) ≤ a (i - d + 1) ∧ (a (i - d) < a (i - d + 1) ∨ a (i - d) = 0) := by
  have hai : a (i + 1) ≠ 0 := (lt_of_le_of_lt (hnn _ (by omega)) hrise).ne'
  intro d hd
  induction d with
  | zero => exact ⟨hrise.le, Or.inl hrise⟩
  | succ d ih =>
    obtain ⟨hle, hlt | hz⟩ := ih (by omega)
    · have hidx : i - (d + 1) + 1 = i - d := by omega
      rw [hidx]
      by_cases hk : a (i - d) = 0
      · have : a (i - (d + 1)) = 0 := by
          by_contra h
          exact hnz (i - (d + 1)) (i - d) (i + 1) (by omega) (by omega) hin h hai hk
        exact ⟨by rw [this, hk], Or.inr this⟩
      · have hpos : 0 < a (i - d) := lt_of_le_of_ne (hnn _ (by omega)) (Ne.symm hk)
        have hpos1 : 0 < a (i - d + 1) := lt_of_le_of_lt (hnn _ (by omega)) hlt
        have hlc' := hlc (i - (d + 1)) (by omega)
        have h1 : i - (d + 1) + 1 = i - d := by omega
        have h2 : i - (d + 1) + 2 = i - d + 1 := by omega
        rw [h1, h2] at hlc'
        have : a (i - (d + 1)) < a (i - d) := by
          by_contra h
          have h := not_lt.mp h
          nlinarith
        exact ⟨this.le, Or.inl this⟩
    · have hidx : i - (d + 1) + 1 = i - d := by omega
      rw [hidx]
      have : a (i - (d + 1)) = 0 := by
        by_contra h
        exact hnz (i - (d + 1)) (i - d) (i + 1) (by omega) (by omega) hin h hai hz
      exact ⟨by rw [this, hz], Or.inr this⟩

end Proof

/-- **Log-concave implies unimodal.** A log-concave sequence `(a₀, …, aₙ)` of nonnegative real
numbers with no internal zeros is unimodal (Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed.,
author's draft of 15 July 2011, Chapter 1, Exercise 50(a)). Any index of a maximal term can serve
as the peak. -/
theorem isUnimodal_of_isLogConcave {a : ℕ → ℝ} {n : ℕ} (hnn : ∀ i ≤ n, 0 ≤ a i)
    (hlc : IsLogConcave a n) (hnz : NoInternalZeros a n) : IsUnimodal a n := by
  obtain ⟨j, hj, hmax⟩ : ∃ j ∈ Finset.range (n + 1), ∀ i ∈ Finset.range (n + 1), a i ≤ a j :=
    Finset.exists_max_image _ a ⟨0, by simp⟩
  rw [Finset.mem_range] at hj
  refine ⟨j, by omega, fun i hij => ?_, fun i hji hin => ?_⟩
  · by_contra h
    rw [not_le] at h
    have hprop := descent_propagates hnn hlc hnz (by omega) h
    -- `a` is weakly decreasing on `[i + 1, n]`, so `a j ≤ a (i + 1) < a i ≤ a j`.
    have hdec : ∀ m, i + 1 ≤ m → m ≤ n → a m ≤ a (i + 1) := by
      intro m hm hmn
      induction m, hm using Nat.le_induction with
      | base => exact le_rfl
      | succ m hm ih => exact ((hprop m (by omega) hmn).1).trans (ih (by omega))
    have := hmax i (Finset.mem_range.mpr (by omega))
    linarith [hdec j (by omega) (by omega)]
  · by_contra h
    rw [not_le] at h
    have hprop := ascent_propagates hnn hlc hnz (by omega) h
    -- `a` is weakly increasing on `[0, i]`, so `a j ≤ a i < a (i + 1) ≤ a j`.
    have hinc : ∀ d, d ≤ i → a (i - d) ≤ a i := by
      intro d hd
      induction d with
      | zero => simp
      | succ d ih =>
        have h1 := (hprop (d + 1) hd).1
        have h2 : i - (d + 1) + 1 = i - d := by omega
        rw [h2] at h1
        exact h1.trans (ih (by omega))
    have := hmax (i + 1) (Finset.mem_range.mpr (by omega))
    have hji' := hinc (i - j) (by omega)
    rw [show i - (i - j) = j by omega] at hji'
    linarith

/-- **Rows of Pascal's triangle are log-concave.** For every `n`, the sequence
`(C(n, 0), C(n, 1), …, C(n, n))` satisfies `C(n, k) C(n, k + 2) ≤ C(n, k + 1)²`. Proof: by
`C(n, j + 1) (j + 1) = C(n, j) (n - j)`, multiplying `C(n, k) C(n, k + 2)` by `(n - k)(k + 2)`
gives `C(n, k + 1)² (k + 1)(n - k - 1)`, which is at most `C(n, k + 1)² (n - k)(k + 2)`; that is,
the ratio `C(n, k + 1) / C(n, k) = (n - k) / (k + 1)` decreases with `k`. Log-concavity is in the
sense of Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed., author's draft of 15 July 2011,
Chapter 1, Exercise 50. -/
theorem choose_isLogConcave (n : ℕ) : IsLogConcave (fun k => (n.choose k : ℝ)) n := by
  intro k hk
  simp only
  have e1 := Nat.choose_succ_right_eq n k
  have e2 := Nat.choose_succ_right_eq n (k + 1)
  -- `C(n,k) C(n,k+2) (n-k)(k+2) = C(n,k+1)^2 (k+1)(n-k-1)`.
  have key : n.choose k * n.choose (k + 2) * ((n - k) * (k + 2)) =
      n.choose (k + 1) ^ 2 * ((k + 1) * (n - (k + 1))) := by
    calc n.choose k * n.choose (k + 2) * ((n - k) * (k + 2))
        = (n.choose k * (n - k)) * (n.choose (k + 1 + 1) * (k + 1 + 1)) := by ring
      _ = (n.choose (k + 1) * (k + 1)) * (n.choose (k + 1) * (n - (k + 1))) := by rw [e1, e2]
      _ = n.choose (k + 1) ^ 2 * ((k + 1) * (n - (k + 1))) := by ring
  have hle : (k + 1) * (n - (k + 1)) ≤ (n - k) * (k + 2) := by
    calc (k + 1) * (n - (k + 1)) ≤ (k + 2) * (n - k) := Nat.mul_le_mul (by omega) (by omega)
      _ = (n - k) * (k + 2) := Nat.mul_comm _ _
  have hpos : 0 < (n - k) * (k + 2) := Nat.mul_pos (by omega) (by omega)
  have : n.choose k * n.choose (k + 2) ≤ n.choose (k + 1) ^ 2 := by
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    rw [key]
    exact Nat.mul_le_mul_left _ hle
  exact_mod_cast this

/-- **Rows of Pascal's triangle are unimodal.** For every `n`, the sequence
`(C(n, 0), …, C(n, n))` is unimodal, as a log-concave sequence of positive integers (Stanley,
*Enumerative Combinatorics*, vol. 1, 2nd ed., author's draft of 15 July 2011, Chapter 1,
Exercise 50(a)). -/
theorem choose_isUnimodal (n : ℕ) : IsUnimodal (fun k => (n.choose k : ℝ)) n :=
  isUnimodal_of_isLogConcave (fun _ _ => Nat.cast_nonneg _) (choose_isLogConcave n)
    (fun _ j _ _ hjk hkn _ _ => by
      simp only [ne_eq, Nat.cast_eq_zero]
      exact (Nat.choose_pos (by omega)).ne')

end MathlibExt.Combinatorics.Sequences.Unimodal
