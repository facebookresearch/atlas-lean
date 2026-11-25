/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Sequences.ThrowbackSequences
import Mathlib.Data.Nat.ModEq

/-!
# Perfect mixing for consecutive integers

For the throwback operation on consecutive positive integers starting at `m`, the positions
of the first `n + 1` terms run through a cycle of length `(m + 1) ^ (n + 1)`.
Deleting the minimum and subtracting one from the other terms sends each block of
`m + 1` steps to `m` steps from the same starting sequence.
-/

namespace MetaMathlibExt

namespace throwback_consecutive_perfect_mixing

private def orbit (m k : ℕ) : ℕ → ℕ := (throwback id)^[k] (fun i => m + i)

private theorem orbit_succ (m k : ℕ) : orbit m (k + 1) = throwback id (orbit m k) :=
  Function.iterate_succ_apply' ..

private theorem le_orbit (m k : ℕ) : ∀ i, m ≤ orbit m k i := by
  induction k with
  | zero => exact fun i => Nat.le_add_right m i
  | succ k ih =>
    intro i
    rw [orbit_succ]
    unfold throwback
    split_ifs <;> exact ih _

/-- Insert `m` at position `p`, adding one to every other term. -/
private def insertMin (m p : ℕ) (s : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < p then s i + 1 else if i = p then m else s (i - 1) + 1

private theorem insertMin_self (m p : ℕ) (s : ℕ → ℕ) : insertMin m p s p = m := by
  simp [insertMin]

private theorem insertMin_eq_min {m p i : ℕ} {s : ℕ → ℕ} (hs : ∀ j, m ≤ s j) :
    insertMin m p s i = m ↔ i = p := by
  refine ⟨fun h => ?_, fun h => h ▸ insertMin_self m p s⟩
  unfold insertMin at h
  split_ifs at h with hlt heq
  · have := hs i
    omega
  · exact heq
  · have := hs (i - 1)
    omega

/-- A step led by the inserted term leaves the other terms in order. -/
private theorem throwback_insertMin_zero (m : ℕ) (s : ℕ → ℕ) :
    throwback id (insertMin m 0 s) = insertMin m m s := by
  funext i
  simp only [throwback, insertMin_self, id_eq]
  by_cases hlt : i < m
  · simp [insertMin, hlt]
  by_cases heq : i = m
  · subst i
    simp [insertMin_self]
  · have hi : i ≠ 0 := by omega
    simp [insertMin, hlt, heq, hi]

/-- While the inserted term moves one position left, the other terms take a throwback
step after their values and the leader's insertion index are reduced by one. -/
private theorem throwback_insertMin_succ {m p : ℕ} (s : ℕ → ℕ) (hp : p < m)
    (hs : m ≤ s 0) :
    throwback id (insertMin m (p + 1) s) = insertMin m p (throwback id s) := by
  funext i
  have hlead : insertMin m (p + 1) s 0 = s 0 + 1 := by simp [insertMin]
  simp only [throwback, hlead, id_eq]
  rcases lt_trichotomy i p with hlt | heq | hgt
  · have h₁ : i < s 0 + 1 := by omega
    have h₂ : i + 1 < p + 1 := by omega
    have h₃ : i < s 0 := by omega
    simp [insertMin, throwback, hlt, h₁, h₂, h₃]
  · subst i
    have h : p < s 0 + 1 := by omega
    simp [insertMin, h]
  · have h₁ : ¬ i < p := by omega
    have h₂ : i ≠ p := by omega
    rcases lt_trichotomy i (s 0 + 1) with hlt | heq | hgt'
    · have h₃ : ¬ i + 1 < p + 1 := by omega
      have h₅ : i - 1 < s 0 := by omega
      have h₆ : i - 1 + 1 = i := by omega
      simp [insertMin, throwback, h₁, h₂, hlt, h₃, h₅, h₆]
    · subst i
      have h₃ : ¬ s 0 + 1 < p := by omega
      have h₄ : s 0 + 1 ≠ p := by omega
      simp [insertMin, throwback, h₃, h₄]
    · have h₃ : ¬ i < s 0 + 1 := by omega
      have h₄ : i ≠ s 0 + 1 := by omega
      have h₅ : ¬ i < p + 1 := by omega
      have h₆ : i ≠ p + 1 := by omega
      have h₇ : ¬ i - 1 < s 0 := by omega
      have h₈ : i - 1 ≠ s 0 := by omega
      simp [insertMin, throwback, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈]

/-- After the first step of a block, the minimum starts at position `m`, and each
further step moves it left while advancing the throwback on the remaining terms. -/
private theorem orbit_block_succ (m q : ℕ)
    (hbase : orbit m (q * (m + 1)) = insertMin m 0 (orbit m (q * m)))
    (r : ℕ) (hr : r ≤ m) :
    orbit m (q * (m + 1) + 1 + r) = insertMin m (m - r) (orbit m (q * m + r)) := by
  induction r with
  | zero => simpa [orbit_succ, hbase] using throwback_insertMin_zero m (orbit m (q * m))
  | succ r ih =>
    have hpos : m - r = (m - (r + 1)) + 1 := by omega
    rw [← Nat.add_assoc, orbit_succ, ih (by omega), hpos, ← Nat.add_assoc, orbit_succ]
    exact throwback_insertMin_succ _ (by omega) (le_orbit m (q * m + r) 0)

private theorem orbit_block_start (m q : ℕ) :
    orbit m (q * (m + 1)) = insertMin m 0 (orbit m (q * m)) := by
  induction q with
  | zero =>
    funext i
    cases i <;> simp [orbit, insertMin, Nat.add_assoc]
  | succ q ih =>
    have htime : (q + 1) * (m + 1) = q * (m + 1) + 1 + m := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    rw [htime, orbit_block_succ m q ih m le_rfl, Nat.sub_self, Nat.add_mul, Nat.one_mul]

private theorem orbit_block (m q r : ℕ) (hr : r ≤ m) :
    orbit m (q * (m + 1) + r) =
      insertMin m (if r = 0 then 0 else m + 1 - r) (orbit m (q * m + (r - 1))) := by
  cases r with
  | zero => simpa using orbit_block_start m q
  | succ r =>
    simpa [Nat.add_assoc, Nat.add_comm 1 r, Nat.add_sub_add_right] using
      orbit_block_succ m q (orbit_block_start m q) r (by omega)

private theorem orbit_div_mod (m k : ℕ) :
    orbit m k = insertMin m (if k % (m + 1) = 0 then 0 else m + 1 - k % (m + 1))
      (orbit m (k / (m + 1) * m + (k % (m + 1) - 1))) := by
  have hr : k % (m + 1) ≤ m := Nat.lt_succ_iff.mp (Nat.mod_lt _ (Nat.succ_pos m))
  have h := orbit_block m (k / (m + 1)) (k % (m + 1)) hr
  rwa [Nat.mul_comm _ (m + 1), Nat.add_comm, Nat.mod_add_div] at h

private def samePositions (m n : ℕ) (s t : ℕ → ℕ) : Prop :=
  ∀ i ≤ n, ∀ p, (s p = m + i ↔ t p = m + i)

private theorem samePositions_insertMin_zero {m p q : ℕ} {s t : ℕ → ℕ}
    (hs : ∀ j, m ≤ s j) (ht : ∀ j, m ≤ t j) :
    samePositions m 0 (insertMin m p s) (insertMin m q t) ↔ p = q := by
  constructor
  · intro h
    apply (insertMin_eq_min ht).mp
    exact (h 0 le_rfl p).mp (by simp [insertMin])
  · rintro rfl i hi j
    rw [Nat.eq_zero_of_le_zero hi, Nat.add_zero, insertMin_eq_min hs, insertMin_eq_min ht]

private theorem samePositions_insertMin_succ {m n p q : ℕ} {s t : ℕ → ℕ}
    (hs : ∀ j, m ≤ s j) (ht : ∀ j, m ≤ t j) :
    samePositions m (n + 1) (insertMin m p s) (insertMin m q t) ↔
      p = q ∧ samePositions m n s t := by
  constructor
  · intro h
    have hpq := (samePositions_insertMin_zero hs ht).mp
      (fun i hi j => h i (by omega) j)
    subst q
    refine ⟨rfl, fun i hi j => ?_⟩
    have heq : m + (i + 1) = m + i + 1 := (Nat.add_assoc m i 1).symm
    by_cases hj : j < p
    · simpa [insertMin, hj, heq] using h (i + 1) (by omega) j
    · have hj' : ¬ j + 1 < p := by omega
      have hj'' : j + 1 ≠ p := by omega
      simpa [insertMin, hj', hj'', heq] using h (i + 1) (by omega) (j + 1)
  · rintro ⟨rfl, h⟩ i hi j
    cases i with
    | zero => exact (samePositions_insertMin_zero hs ht).mpr rfl 0 le_rfl j
    | succ i =>
      have heq : m + (i + 1) = m + i + 1 := (Nat.add_assoc m i 1).symm
      by_cases hj : j < p
      · simpa [insertMin, hj, heq] using h i (by omega) j
      by_cases hj' : j = p
      · simp [insertMin, hj']
      · simpa [insertMin, hj, hj', heq] using h i (by omega) (j - 1)

private theorem blockPosition_eq_iff {m r s : ℕ} (hr : r ≤ m) (hs : s ≤ m) :
    (if r = 0 then 0 else m + 1 - r) = (if s = 0 then 0 else m + 1 - s) ↔ r = s := by
  split_ifs <;> omega

/-- Agreement on the first terms is exactly congruence of the iteration times. -/
private theorem samePositions_iff_modEq (m n k l : ℕ) (hm : 0 < m) :
    samePositions m n (orbit m k) (orbit m l) ↔ k ≡ l [MOD (m + 1) ^ (n + 1)] := by
  have hm' : 0 < m + 1 := Nat.lt_succ_of_lt hm
  have hrem (t : ℕ) : t % (m + 1) ≤ m := Nat.lt_succ_iff.mp (Nat.mod_lt t hm')
  induction n generalizing k l with
  | zero =>
    rw [orbit_div_mod m k, orbit_div_mod m l,
      samePositions_insertMin_zero (le_orbit m _) (le_orbit m _),
      blockPosition_eq_iff (hrem k) (hrem l), pow_one]
    rfl
  | succ n ih =>
    rw [orbit_div_mod m k, orbit_div_mod m l,
      samePositions_insertMin_succ (le_orbit m _) (le_orbit m _),
      blockPosition_eq_iff (hrem k) (hrem l)]
    simp only [ih]
    -- For equal remainders, the difference of projected times is `m` times
    -- the difference of the quotients. Coprimality lets us cancel `m`.
    have hcop : Nat.Coprime ((m + 1) ^ (n + 1)) m :=
      Nat.Coprime.pow_left _ (by simp [Nat.Coprime])
    have hmod (h : k % (m + 1) = l % (m + 1)) :
        (k / (m + 1) * m + (k % (m + 1) - 1) ≡
          l / (m + 1) * m + (l % (m + 1) - 1) [MOD (m + 1) ^ (n + 1)]) ↔
          k ≡ l [MOD (m + 1) ^ (n + 1 + 1)] := by
      rw [h, (Nat.ModEq.refl _).add_iff_right]
      have hmul : (k / (m + 1) * m ≡ l / (m + 1) * m [MOD (m + 1) ^ (n + 1)]) ↔
          k / (m + 1) ≡ l / (m + 1) [MOD (m + 1) ^ (n + 1)] :=
        ⟨Nat.ModEq.cancel_right_of_coprime hcop, fun h' => h'.mul_right m⟩
      rw [hmul, pow_succ (m + 1) (n + 1)]
      conv_rhs =>
        rw [← Nat.mod_add_div k (m + 1), ← Nat.mod_add_div l (m + 1)]
      rw [h, (Nat.ModEq.refl _).add_iff_left, Nat.mul_comm ((m + 1) ^ (n + 1))]
      exact (Nat.ModEq.mul_left_cancel_iff' hm'.ne').symm
    refine ⟨fun ⟨h, h'⟩ => (hmod h).mp h', fun h => ?_⟩
    have hr : k ≡ l [MOD m + 1] := h.of_dvd (by rw [pow_succ]; exact dvd_mul_left _ _)
    exact ⟨hr, (hmod hr).mpr h⟩

end throwback_consecutive_perfect_mixing

open throwback_consecutive_perfect_mixing in
/-- **Perfect mixing for consecutive integers.** Let $m \ge 1$ and $n \ge 0$, let
$X = (m, m + 1, m + 2, \dots)$, and let $\tau$ be the throwback. Then the positions of the terms
$m, m + 1, \dots, m + n$ in $\tau^k(X)$ are different for different $k$ with
$0 \le k < (m + 1)^{n + 1}$: for $0 \le k < l < (m + 1)^{n + 1}$, some $m + i$ with $i \le n$
occupies different positions in $\tau^k(X)$ and $\tau^l(X)$. Moreover, each of
$m, m + 1, \dots, m + n$ occupies the same positions in $\tau^{(m+1)^{n+1}}(X)$ as in $X$.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Theorem 9 (`jis-2025-25.5.1-thm-9`). -/
public theorem throwback_consecutive_perfect_mixing (m n : ℕ) (hm : 0 < m) :
    let Y : ℕ → ℕ → ℕ := fun k => (throwback id)^[k] (fun i => m + i)
    (∀ i ≤ n, ∀ p, (Y ((m + 1) ^ (n + 1)) p = m + i ↔ Y 0 p = m + i)) ∧
      ∀ k l, k < l → l < (m + 1) ^ (n + 1) →
        ¬ ∀ i ≤ n, ∀ p, (Y k p = m + i ↔ Y l p = m + i) := by
  refine ⟨(samePositions_iff_modEq m n _ _ hm).mpr Nat.modulus_modEq_zero, ?_⟩
  intro k l hkl hl h
  have hmod := (samePositions_iff_modEq m n k l hm).mp h
  exact hkl.ne (hmod.eq_of_lt_of_lt (hkl.trans hl) hl)

end MetaMathlibExt
