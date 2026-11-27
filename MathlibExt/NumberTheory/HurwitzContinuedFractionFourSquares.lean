/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Errors of Hurwitz continued fraction convergents

`hurwitzQ_mul_sub_hurwitzP` expresses the convergent error as a signed reciprocal
product of the iterates and recovers the next iterate from two consecutive errors.
`norm_hurwitzQ_lt_succ` proves that the denominator norms increase at legal indices.
`norm_sub_hurwitz_convergent_le` proves Lakein's first theorem: at every legal index the
distance from $z$ to its convergent is at most the reciprocal of the squared denominator norm.

The iterates and convergents follow Zhaonan Wang and Yingpu Deng, *Finding Sums of Four
Squares via Complex Continued Fractions*. Rounding ties go to the larger integer in each
coordinate. The final index of a finite expansion is legal, and its next iterate is zero.
-/

open Complex

namespace MetaMathlibExt

@[expose] public section

/-- **Hurwitz rounding to the nearest Gaussian integer.** For a complex number $z$, let
$[z] = m + n i$, where $m = \lfloor \operatorname{Re} z + 1/2 \rfloor$ and
$n = \lfloor \operatorname{Im} z + 1/2 \rfloor$; that is, the real and imaginary parts of $z$ are
rounded to the nearest integer, with halves rounded up. Then $[z]$ is a Gaussian integer nearest
to $z$.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Section 2 (notation `[z]`). -/
noncomputable def hurwitzRound (z : ℂ) : ℂ :=
  (⌊z.re + 1 / 2⌋ : ℂ) + (⌊z.im + 1 / 2⌋ : ℂ) * I

/-- **Iterates of the Hurwitz algorithm.** For a complex number $z$, the Hurwitz iterates are
$z_0 = z$ and $z_{n+1} = (z_n - [z_n])^{-1}$ for $n \ge 0$, where $[u]$ is the Gaussian integer
nearest to $u$, obtained by rounding the real and imaginary parts of $u$ to the nearest integer
with halves rounded up, and where the inverse of $0$ is taken to be $0$.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Section 2. -/
noncomputable def hurwitzIter (z : ℂ) : ℕ → ℂ
  | 0 => z
  | n + 1 => (hurwitzIter z n - hurwitzRound (hurwitzIter z n))⁻¹

/-- **Partial quotients of the Hurwitz expansion.** Let $z$ be a complex number with Hurwitz
iterates $z_0 = z, z_1, z_2, \dots$. For $n \ge 0$, the $n$-th partial quotient is $a_n = [z_n]$,
the Gaussian integer nearest to $z_n$, obtained by rounding the real and imaginary parts of
$z_n$ to the nearest integer with halves rounded up.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Section 2. -/
noncomputable def hurwitzDigit (z : ℂ) (n : ℕ) : ℂ :=
  hurwitzRound (hurwitzIter z n)

/-- **Consecutive pairs of Hurwitz convergents.** Let $z$ be a complex number with Hurwitz
partial quotients $a_0, a_1, a_2, \dots$. This is the sequence whose term for $n \ge 0$ is the
pair of pairs of complex numbers $((P_{n-1}, Q_{n-1}), (P_n, Q_n))$, where $P_{-1} = 1$,
$Q_{-1} = 0$, $P_0 = a_0$, $Q_0 = 1$, and $P_{n+1} = a_{n+1} P_n + P_{n-1}$ and
$Q_{n+1} = a_{n+1} Q_n + Q_{n-1}$ for $n \ge 0$.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Section 2. -/
noncomputable def hurwitzPQ (z : ℂ) : ℕ → (ℂ × ℂ) × (ℂ × ℂ)
  | 0 => ((1, 0), (hurwitzDigit z 0, 1))
  | n + 1 =>
    (((hurwitzPQ z n).2.1, (hurwitzPQ z n).2.2),
      (hurwitzDigit z (n + 1) * (hurwitzPQ z n).2.1 + (hurwitzPQ z n).1.1,
        hurwitzDigit z (n + 1) * (hurwitzPQ z n).2.2 + (hurwitzPQ z n).1.2))

/-- **Convergent numerators of the Hurwitz expansion.** Let $z$ be a complex number with Hurwitz
partial quotients $a_0, a_1, a_2, \dots$. Its convergent numerators $P_n$, $n \ge 0$, are given by
$P_{-1} = 1$, $P_0 = a_0$ and $P_{n+1} = a_{n+1} P_n + P_{n-1}$ for $n \ge 0$.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Section 2. -/
noncomputable def hurwitzP (z : ℂ) (n : ℕ) : ℂ :=
  (hurwitzPQ z n).2.1

/-- **Convergent denominators of the Hurwitz expansion.** Let $z$ be a complex number with
Hurwitz partial quotients $a_0, a_1, a_2, \dots$. Its convergent denominators $Q_n$, $n \ge 0$,
are given by $Q_{-1} = 0$, $Q_0 = 1$ and $Q_{n+1} = a_{n+1} Q_n + Q_{n-1}$ for $n \ge 0$.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Section 2. -/
noncomputable def hurwitzQ (z : ℂ) (n : ℕ) : ℂ :=
  (hurwitzPQ z n).2.2

/-- **Legal indices of the Hurwitz expansion.** Let $z$ be a complex number with Hurwitz iterates
$z_j$ and partial quotients $a_j$. A natural number $n$ is a legal index for $z$ when
$z_j \ne a_j$ for every $j < n$, that is, when the Hurwitz expansion of $z$ has not terminated
before step $n$.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Section 2 (remark after Proposition 1). -/
def HurwitzLegal (z : ℂ) (n : ℕ) : Prop :=
  ∀ j < n, hurwitzIter z j ≠ hurwitzDigit z j

/-- **Rounding error of the nearest Gaussian integer.** For every complex number $z$, let $[z]$ be
the Gaussian integer nearest to $z$, obtained by rounding the real and imaginary parts to the
nearest integer with halves rounded up. Then $|\operatorname{Re}(z - [z])| \le 1/2$ and
$|\operatorname{Im}(z - [z])| \le 1/2$.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Section 2 (the set `Φ`). -/
theorem abs_re_sub_hurwitzRound_le (z : ℂ) :
    |(z - hurwitzRound z).re| ≤ 1 / 2 ∧ |(z - hurwitzRound z).im| ≤ 1 / 2 := by
  simp only [hurwitzRound, sub_re, add_re, intCast_re, mul_re, intCast_im, I_re, I_im,
    sub_im, add_im, mul_im, mul_zero, mul_one, sub_zero, zero_add, add_zero]
  have h1 := Int.floor_le (z.re + 1 / 2)
  have h2 := Int.lt_floor_add_one (z.re + 1 / 2)
  have h3 := Int.floor_le (z.im + 1 / 2)
  have h4 := Int.lt_floor_add_one (z.im + 1 / 2)
  constructor <;> rw [abs_le] <;> constructor <;> linarith

/-- **Recursion for the Hurwitz convergents.** Let $z$ be a complex number with Hurwitz partial
quotients $a_n$, convergent numerators $P_n$ and convergent denominators $Q_n$. Then
$P_0 = a_0$, $Q_0 = 1$, $P_1 = a_1 a_0 + 1$ and $Q_1 = a_1$, and for every $n \ge 0$,
$P_{n+2} = a_{n+2} P_{n+1} + P_n$ and $Q_{n+2} = a_{n+2} Q_{n+1} + Q_n$.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Section 2. -/
theorem hurwitzPQ_recursion (z : ℂ) (n : ℕ) :
    hurwitzP z 0 = hurwitzDigit z 0 ∧ hurwitzQ z 0 = 1 ∧
      hurwitzP z 1 = hurwitzDigit z 1 * hurwitzDigit z 0 + 1 ∧
      hurwitzQ z 1 = hurwitzDigit z 1 ∧
      hurwitzP z (n + 2) = hurwitzDigit z (n + 2) * hurwitzP z (n + 1) + hurwitzP z n ∧
      hurwitzQ z (n + 2) = hurwitzDigit z (n + 2) * hurwitzQ z (n + 1) + hurwitzQ z n := by
  simp [hurwitzP, hurwitzQ, hurwitzPQ]

namespace hurwitzQ_mul_sub_hurwitzP

private noncomputable def error (z : ℂ) (pq : ℂ × ℂ) : ℂ := pq.2 * z - pq.1

-- The pair at index zero includes the initial error Q₋₁ z - P₋₁ = -1.
private theorem error_step (z : ℂ) (n : ℕ) (hn : HurwitzLegal z n) :
    error z (hurwitzPQ z n).1 ≠ 0 ∧
      error z (hurwitzPQ z n).2 = -error z (hurwitzPQ z n).1 / hurwitzIter z (n + 1) := by
  induction n with
  | zero => simp [error, hurwitzPQ, hurwitzIter, hurwitzDigit]
  | succ n ih =>
    obtain ⟨hne, hstep⟩ := ih (fun j hj => hn j (Nat.lt_succ_of_lt hj))
    have hz : hurwitzIter z (n + 1) ≠ 0 :=
      inv_ne_zero (sub_ne_zero.mpr (hn n (Nat.lt_succ_self n)))
    refine ⟨hstep ▸ div_ne_zero (neg_ne_zero.mpr hne) hz, ?_⟩
    have hrec : error z (hurwitzPQ z (n + 1)).2 =
        hurwitzDigit z (n + 1) * error z (hurwitzPQ z n).2 + error z (hurwitzPQ z n).1 := by
      simp only [error, hurwitzPQ]
      ring
    rw [hrec]
    change _ = -error z (hurwitzPQ z n).2 / (hurwitzIter z (n + 1) - hurwitzDigit z (n + 1))⁻¹
    rw [div_inv_eq_mul]
    linear_combination (eq_div_iff hz).mp hstep

end hurwitzQ_mul_sub_hurwitzP

/-- **Error of the Hurwitz convergents.** Let $z$ be a complex number with Hurwitz iterates
$z_0 = z, z_1, z_2, \dots$, convergent numerators $P_n$ and convergent denominators $Q_n$. For
every legal index $n$ for $z$,
$$Q_n z - P_n = (-1)^n (z_1 z_2 \cdots z_{n+1})^{-1},$$
and if moreover $n \ge 1$, then $z_{n+1} = -(Q_{n-1} z - P_{n-1}) / (Q_n z - P_n)$. Here the
inverse of $0$ and any quotient by $0$ are taken to be $0$.

The case $n = 0$ of the second identity, $z_1 = (z - a_0)^{-1}$ with $a_0$ the first partial
quotient (and $Q_{-1} = 0$, $P_{-1} = 1$), is the definition of the iterates.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Proposition 1 (`integers-2024-A25-prop-1`). -/
theorem hurwitzQ_mul_sub_hurwitzP (z : ℂ) (n : ℕ) (hn : HurwitzLegal z n) :
    hurwitzQ z n * z - hurwitzP z n =
        (-1) ^ n * (∏ j ∈ Finset.range (n + 1), hurwitzIter z (j + 1))⁻¹ ∧
      (1 ≤ n → hurwitzIter z (n + 1) =
        -(hurwitzQ z (n - 1) * z - hurwitzP z (n - 1)) / (hurwitzQ z n * z - hurwitzP z n)) := by
  induction n with
  | zero => simp [hurwitzQ, hurwitzP, hurwitzPQ, hurwitzIter, hurwitzDigit]
  | succ n ih =>
    obtain ⟨hne, hstep⟩ := hurwitzQ_mul_sub_hurwitzP.error_step z (n + 1) hn
    change hurwitzQ z n * z - hurwitzP z n ≠ 0 at hne
    change hurwitzQ z (n + 1) * z - hurwitzP z (n + 1) =
      -(hurwitzQ z n * z - hurwitzP z n) / hurwitzIter z (n + 2) at hstep
    rw [hstep]
    refine ⟨?_, fun _ => (div_div_cancel₀ (neg_ne_zero.mpr hne)).symm⟩
    rw [(ih (fun j hj => hn j (Nat.lt_succ_of_lt hj))).1, Finset.prod_range_succ _ (n + 1),
      pow_succ, mul_inv_rev, div_eq_mul_inv]
    ring


namespace norm_hurwitzQ_lt_succ

private def gaussian (a b : ℤ) : ℂ := (a : ℂ) + (b : ℂ) * I

@[local simp] private theorem gaussian_re (a b : ℤ) : (gaussian a b).re = a := by
  simp [gaussian, mul_re]

@[local simp] private theorem gaussian_im (a b : ℤ) : (gaussian a b).im = b := by
  simp [gaussian, mul_im]

private theorem gaussian_add (a b p q : ℤ) :
    gaussian a b + gaussian p q = gaussian (a + p) (b + q) := by
  apply Complex.ext <;> simp

private def InSquare (u : ℂ) : Prop := |u.re| ≤ 1 / 2 ∧ |u.im| ≤ 1 / 2

private theorem normSq_le_half {u : ℂ} (hu : InSquare u) : normSq u ≤ 1 / 2 := by
  obtain ⟨hr₁, hr₂⟩ := abs_le.mp hu.1
  obtain ⟨hi₁, hi₂⟩ := abs_le.mp hu.2
  rw [normSq_apply]
  nlinarith [mul_nonneg (sub_nonneg.mpr hr₂) (sub_nonneg.mpr hr₁),
    mul_nonneg (sub_nonneg.mpr hi₂) (sub_nonneg.mpr hi₁)]

private theorem gaussian_cases (a b : ℤ) :
    4 ≤ normSq (gaussian a b) ∨ normSq (gaussian a b) = 2 ∨
      gaussian a b ∈ ({0, 1, -1, I, -I} : Set ℂ) := by
  by_cases h : 4 ≤ a * a + b * b
  · left
    simpa [normSq_apply] using (show (4 : ℝ) ≤ (↑a : ℝ) * ↑a + ↑b * ↑b by exact_mod_cast h)
  · right
    have bounds (x y : ℤ) (hxy : ¬ 4 ≤ x * x + y * y) : -1 ≤ x ∧ x ≤ 1 := by
      constructor <;> by_contra! hx
      · have hx' : x ≤ -2 := by omega
        nlinarith [mul_nonneg (show 0 ≤ -x - 2 by omega) (show 0 ≤ -x + 2 by omega)]
      · have hx' : 2 ≤ x := by omega
        nlinarith [mul_nonneg (show 0 ≤ x - 2 by omega) (show 0 ≤ x + 2 by omega)]
    obtain ⟨ha₁, ha₂⟩ := bounds a b h
    obtain ⟨hb₁, hb₂⟩ := bounds b a (by simpa [add_comm] using h)
    interval_cases a <;> interval_cases b <;>
      norm_num [normSq_apply, gaussian, neg_mul]

private theorem inv_sub_comparison {u : ℂ} (d : ℂ) (hu : u ≠ 0) :
    (normSq (u⁻¹ - d) - 1) * normSq u =
      1 - 2 * (d * u).re + (normSq d - 1) * normSq u := by
  rw [sub_mul, one_mul, ← normSq_mul, sub_mul, inv_mul_cancel₀ hu]
  simp only [normSq_apply, sub_re, sub_im, one_re, one_im, mul_re, mul_im]
  ring

private theorem inv_sub_diagonal {u : ℂ} (a b : ℤ) (hu : u ≠ 0)
    (hd : normSq (gaussian a b) = 2) :
    (normSq (u⁻¹ - gaussian a b) - 1) * normSq u =
      normSq (u - gaussian a (-b)) - 1 := by
  rw [inv_sub_comparison _ hu]
  simp only [normSq_apply, mul_re, sub_re, sub_im, gaussian_re, gaussian_im, Int.cast_neg] at hd ⊢
  linear_combination (u.re * u.re + u.im * u.im - 1) * hd

private theorem one_le_normSq_inv_sub {u d : ℂ} (hu : u ≠ 0) (hs : InSquare u)
    (hd : d ∈ ({0, 1, -1, I, -I} : Set ℂ)) : 1 ≤ normSq (u⁻¹ - d) := by
  apply sub_nonneg.mp
  apply nonneg_of_mul_nonneg_left _ (normSq_pos.mpr hu)
  rw [inv_sub_comparison d hu]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  have hhalf := normSq_le_half hs
  obtain ⟨hr, hi⟩ := hs
  obtain rfl | rfl | rfl | rfl | rfl := hd
  · simpa using (show 0 ≤ 1 - normSq u by linarith)
  all_goals
    simp [mul_re, normSq_neg]
    linarith [abs_le.mp hr, abs_le.mp hi]

private theorem one_lt_normSq_sub_of_large {w d : ℂ} (hw : normSq w < 1)
    (hd : 4 ≤ normSq d) : 1 < normSq (w - d) := by
  simp only [normSq_eq_norm_sq] at hw hd ⊢
  have hw' : ‖w‖ < 1 := by nlinarith [norm_nonneg w]
  have hd' : 2 ≤ ‖d‖ := by nlinarith [norm_nonneg d]
  have hdist : 1 < ‖w - d‖ := by
    have h := norm_sub_norm_le d w
    rw [norm_sub_rev] at h
    linarith
  simpa using (sq_lt_sq₀ zero_le_one (norm_nonneg _)).2 hdist

-- The forward iterate and the negative previous denominator ratio are separated by the
-- lattice unit disks. The open disk on the forward side accommodates rounding ties.
private def Separated (x w : ℂ) : Prop :=
  ∀ a b : ℤ, normSq (x - gaussian a b) < 1 → 1 < normSq (w - gaussian a b)

private theorem separated_zero {u : ℂ} (hu : u ≠ 0) (hs : InSquare u) :
    Separated u⁻¹ 0 := by
  intro p q hclose
  rcases gaussian_cases p q with hlarge | hdiag | hsmall
  · exact one_lt_normSq_sub_of_large (by simp) hlarge
  · simp [hdiag]
  · exact (not_lt_of_ge (one_le_normSq_inv_sub hu hs hsmall) hclose).elim

private theorem separated_step {x w : ℂ} (a b : ℤ) (hsep : Separated x w)
    (hx : x - gaussian a b ≠ 0) (hs : InSquare (x - gaussian a b))
    (hw : 1 < normSq (w - gaussian a b)) :
    Separated (x - gaussian a b)⁻¹ (w - gaussian a b)⁻¹ := by
  have hw₀ := normSq_pos.mp (zero_lt_one.trans hw)
  intro p q hclose
  rcases gaussian_cases p q with hlarge | hdiag | hsmall
  · apply one_lt_normSq_sub_of_large _ hlarge
    rw [normSq_inv, inv_lt_one₀ (by linarith : 0 < normSq (w - gaussian a b))]
    exact hw
  · have hforward := inv_sub_diagonal p q hx hdiag
    have hbackward := inv_sub_diagonal p q hw₀ hdiag
    have hclose' : normSq (x - gaussian (a + p) (b - q)) < 1 := by
      rw [sub_eq_add_neg b q, ← gaussian_add, ← sub_sub]
      have h := mul_neg_of_neg_of_pos (sub_neg.mpr hclose) (normSq_pos.mpr hx)
      rw [hforward] at h
      exact sub_neg.mp h
    have hfar := hsep (a + p) (b - q) hclose'
    rw [sub_eq_add_neg b q, ← gaussian_add, ← sub_sub] at hfar
    rw [← sub_pos, ← mul_pos_iff_of_pos_right (normSq_pos.mpr hw₀), hbackward]
    exact sub_pos.mpr hfar
  · exact (not_lt_of_ge (one_le_normSq_inv_sub hx hs hsmall) hclose).elim

private theorem digit_far {x w : ℂ} (hsep : Separated x w) :
    1 < normSq (w - hurwitzRound x) := by
  exact hsep ⌊x.re + 1 / 2⌋ ⌊x.im + 1 / 2⌋
    ((normSq_le_half (abs_re_sub_hurwitzRound_le x)).trans_lt (by norm_num))

private theorem denominator_step {z w : ℂ} {n : ℕ}
    (hw : w * hurwitzQ z n = -(hurwitzPQ z n).1.2) :
    hurwitzQ z (n + 1) = (hurwitzDigit z (n + 1) - w) * hurwitzQ z n := by
  change hurwitzDigit z (n + 1) * hurwitzQ z n + (hurwitzPQ z n).1.2 = _
  rw [sub_mul, hw, sub_neg_eq_add]

private theorem denominator_state (z : ℂ) (n : ℕ) (hn : HurwitzLegal z (n + 1)) :
    ∃ w, w * hurwitzQ z n = -(hurwitzPQ z n).1.2 ∧
      hurwitzQ z n ≠ 0 ∧ Separated (hurwitzIter z (n + 1)) w := by
  induction n with
  | zero =>
    refine ⟨0, by simp [hurwitzPQ], by simp [hurwitzQ, hurwitzPQ], ?_⟩
    exact separated_zero (sub_ne_zero.mpr (hn 0 Nat.zero_lt_one))
      (abs_re_sub_hurwitzRound_le z)
  | succ n ih =>
    obtain ⟨w, hw, hq, hsep⟩ := ih (fun j hj => hn j (Nat.lt_succ_of_lt hj))
    have hfar := digit_far hsep
    let a := hurwitzDigit z (n + 1)
    change 1 < normSq (w - a) at hfar
    have hw₀ := normSq_pos.mp (zero_lt_one.trans hfar)
    have hrec : hurwitzQ z (n + 1) = (a - w) * hurwitzQ z n := denominator_step hw
    have hneg : a - w = -(w - a) := by ring
    refine ⟨(w - a)⁻¹, ?_, ?_, ?_⟩
    · change (w - a)⁻¹ * hurwitzQ z (n + 1) = -hurwitzQ z n
      rw [hrec, hneg, neg_mul, mul_neg, ← mul_assoc, inv_mul_cancel₀ hw₀, one_mul]
    · rw [hrec, hneg]
      exact mul_ne_zero (neg_ne_zero.mpr hw₀) hq
    · have hx : hurwitzIter z (n + 1) - hurwitzDigit z (n + 1) ≠ 0 :=
        sub_ne_zero.mpr (hn (n + 1) (Nat.lt_succ_self _))
      exact separated_step ⌊(hurwitzIter z (n + 1)).re + 1 / 2⌋
        ⌊(hurwitzIter z (n + 1)).im + 1 / 2⌋ hsep hx
        (abs_re_sub_hurwitzRound_le _) hfar

end norm_hurwitzQ_lt_succ

namespace norm_sub_hurwitz_convergent_le

private theorem geom_h4 (p q u v : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) (hq0 : 0 ≤ q)
    (hq : q ≤ 1 / 2) (hN : (1 - (p ^ 2 + q ^ 2)) * (u ^ 2 + v ^ 2) -
      2 * (p * u + q * v) + (p ^ 2 + q ^ 2) < 0)
    (hd00 : (0 : ℝ) < u ^ 2 + v ^ 2 - 1) (hd10 : (0 : ℝ) < (u - 1) ^ 2 + v ^ 2 - 1)
    (hd01 : (0 : ℝ) < u ^ 2 + (v - 1) ^ 2 - 1)
    (hd11 : (0 : ℝ) < (u - 1) ^ 2 + (v - 1) ^ 2 - 1) : False := by
  have hRle : p ^ 2 + q ^ 2 ≤ 1 / 2 := by
    nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hp), mul_nonneg hq0 (sub_nonneg.mpr hq)]
  have hR : (0 : ℝ) < 1 - (p ^ 2 + q ^ 2) := by linarith
  have hA : (0 : ℝ) ≤ (1 - (p ^ 2 + q ^ 2) - p) * (1 - (p ^ 2 + q ^ 2) - q) := by
    apply mul_nonneg <;> nlinarith [hRle, hp, hq]
  have hB : (0 : ℝ) ≤ p * (1 - (p ^ 2 + q ^ 2) - q) := mul_nonneg hp0 (by nlinarith [hRle, hp, hq])
  have hC : (0 : ℝ) ≤ q * (1 - (p ^ 2 + q ^ 2) - p) := mul_nonneg hq0 (by nlinarith [hRle, hp, hq])
  have hD : (0 : ℝ) ≤ p * q := mul_nonneg hp0 hq0
  set m : ℝ := min (min (u ^ 2 + v ^ 2 - 1) ((u - 1) ^ 2 + v ^ 2 - 1))
    (min (u ^ 2 + (v - 1) ^ 2 - 1) ((u - 1) ^ 2 + (v - 1) ^ 2 - 1)) with hmdef
  have hm : (0 : ℝ) < m := lt_min (lt_min hd00 hd10) (lt_min hd01 hd11)
  have hW : (0 : ℝ) < (1 - (p ^ 2 + q ^ 2) - p) * (1 - (p ^ 2 + q ^ 2) - q) +
      p * (1 - (p ^ 2 + q ^ 2) - q) + q * (1 - (p ^ 2 + q ^ 2) - p) + p * q := by
    have e : (1 - (p ^ 2 + q ^ 2) - p) * (1 - (p ^ 2 + q ^ 2) - q) +
        p * (1 - (p ^ 2 + q ^ 2) - q) + q * (1 - (p ^ 2 + q ^ 2) - p) + p * q =
        (1 - (p ^ 2 + q ^ 2)) ^ 2 := by ring
    rw [e]; exact pow_pos hR 2
  have hm00 : m ≤ u ^ 2 + v ^ 2 - 1 := by
    rw [hmdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hm10 : m ≤ (u - 1) ^ 2 + v ^ 2 - 1 := by
    rw [hmdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hm01 : m ≤ u ^ 2 + (v - 1) ^ 2 - 1 := by
    rw [hmdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hm11 : m ≤ (u - 1) ^ 2 + (v - 1) ^ 2 - 1 := by
    rw [hmdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have e1 := mul_le_mul_of_nonneg_left hm00 hA
  have e2 := mul_le_mul_of_nonneg_left hm10 hB
  have e3 := mul_le_mul_of_nonneg_left hm01 hC
  have e4 := mul_le_mul_of_nonneg_left hm11 hD
  have hpos : (0 : ℝ) < (1 - (p ^ 2 + q ^ 2) - p) * (1 - (p ^ 2 + q ^ 2) - q) *
      (u ^ 2 + v ^ 2 - 1) + p * (1 - (p ^ 2 + q ^ 2) - q) * ((u - 1) ^ 2 + v ^ 2 - 1) +
      q * (1 - (p ^ 2 + q ^ 2) - p) * (u ^ 2 + (v - 1) ^ 2 - 1) +
      p * q * ((u - 1) ^ 2 + (v - 1) ^ 2 - 1) := by
    have hprod : (0 : ℝ) < m * ((1 - (p ^ 2 + q ^ 2) - p) * (1 - (p ^ 2 + q ^ 2) - q) +
        p * (1 - (p ^ 2 + q ^ 2) - q) + q * (1 - (p ^ 2 + q ^ 2) - p) + p * q) :=
      mul_pos hm hW
    have hring : m * ((1 - (p ^ 2 + q ^ 2) - p) * (1 - (p ^ 2 + q ^ 2) - q) +
        p * (1 - (p ^ 2 + q ^ 2) - q) + q * (1 - (p ^ 2 + q ^ 2) - p) + p * q) =
        (1 - (p ^ 2 + q ^ 2) - p) * (1 - (p ^ 2 + q ^ 2) - q) * m +
        p * (1 - (p ^ 2 + q ^ 2) - q) * m + q * (1 - (p ^ 2 + q ^ 2) - p) * m +
        p * q * m := by ring
    linarith [hprod, hring, e1, e2, e3, e4]
  have hid : (1 - (p ^ 2 + q ^ 2) - p) * (1 - (p ^ 2 + q ^ 2) - q) *
      (u ^ 2 + v ^ 2 - 1) + p * (1 - (p ^ 2 + q ^ 2) - q) * ((u - 1) ^ 2 + v ^ 2 - 1) +
      q * (1 - (p ^ 2 + q ^ 2) - p) * (u ^ 2 + (v - 1) ^ 2 - 1) +
      p * q * ((u - 1) ^ 2 + (v - 1) ^ 2 - 1) =
      (1 - (p ^ 2 + q ^ 2)) * ((1 - (p ^ 2 + q ^ 2)) * (u ^ 2 + v ^ 2) -
        2 * (p * u + q * v) + (p ^ 2 + q ^ 2)) + (p + q - 1) * (1 - (p ^ 2 + q ^ 2)) := by
    ring
  have h1 : (1 - (p ^ 2 + q ^ 2)) * ((1 - (p ^ 2 + q ^ 2)) * (u ^ 2 + v ^ 2) -
      2 * (p * u + q * v) + (p ^ 2 + q ^ 2)) < 0 := mul_neg_of_pos_of_neg hR hN
  have h2 : (p + q - 1) * (1 - (p ^ 2 + q ^ 2)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hR)
  rw [hid] at hpos
  linarith

private theorem geom_h3 (p q u v : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) (hq0 : 0 ≤ q)
    (hq : q ≤ 1 / 2) (hN : (1 - (p ^ 2 + q ^ 2)) * (u ^ 2 + v ^ 2) -
      2 * (p * u + q * v) + (p ^ 2 + q ^ 2) < 0)
    (hd00 : (0 : ℝ) < u ^ 2 + v ^ 2 - 1) (hd10 : (0 : ℝ) < (u - 1) ^ 2 + v ^ 2 - 1)
    (hd01 : (0 : ℝ) < u ^ 2 + (v - 1) ^ 2 - 1)
    (hW : (0 : ℝ) ≤ 1 - (p ^ 2 + q ^ 2) - p - q) : False := by
  have hRle : p ^ 2 + q ^ 2 ≤ 1 / 2 := by
    nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hp), mul_nonneg hq0 (sub_nonneg.mpr hq)]
  have hR : (0 : ℝ) < 1 - (p ^ 2 + q ^ 2) := by linarith
  set m : ℝ := min (u ^ 2 + v ^ 2 - 1) (min ((u - 1) ^ 2 + v ^ 2 - 1) (u ^ 2 + (v - 1) ^ 2 - 1))
    with hmdef
  have hm : (0 : ℝ) < m := lt_min hd00 (lt_min hd10 hd01)
  have hWsum : (0 : ℝ) < (1 - (p ^ 2 + q ^ 2) - p - q) + p + q := by linarith
  have hm00 : m ≤ u ^ 2 + v ^ 2 - 1 := by rw [hmdef]; exact min_le_left _ _
  have hm10 : m ≤ (u - 1) ^ 2 + v ^ 2 - 1 := by
    rw [hmdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hm01 : m ≤ u ^ 2 + (v - 1) ^ 2 - 1 := by
    rw [hmdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have e1 := mul_le_mul_of_nonneg_left hm00 hW
  have e2 := mul_le_mul_of_nonneg_left hm10 hp0
  have e3 := mul_le_mul_of_nonneg_left hm01 hq0
  have hpos : (0 : ℝ) < (1 - (p ^ 2 + q ^ 2) - p - q) * (u ^ 2 + v ^ 2 - 1) +
      p * ((u - 1) ^ 2 + v ^ 2 - 1) + q * (u ^ 2 + (v - 1) ^ 2 - 1) := by
    have hprod : (0 : ℝ) < m * ((1 - (p ^ 2 + q ^ 2) - p - q) + p + q) := mul_pos hm hWsum
    have hring : m * ((1 - (p ^ 2 + q ^ 2) - p - q) + p + q) =
        (1 - (p ^ 2 + q ^ 2) - p - q) * m + p * m + q * m := by ring
    linarith [hprod, hring, e1, e2, e3]
  have hid : (1 - (p ^ 2 + q ^ 2) - p - q) * (u ^ 2 + v ^ 2 - 1) +
      p * ((u - 1) ^ 2 + v ^ 2 - 1) + q * (u ^ 2 + (v - 1) ^ 2 - 1) =
      (1 - (p ^ 2 + q ^ 2)) * (u ^ 2 + v ^ 2) - 2 * (p * u + q * v) + (p ^ 2 + q ^ 2) +
        (p + q - 1) := by ring
  rw [hid] at hpos
  linarith [hN, hp, hq]

private theorem geom_vbound (p q u v : ℝ) (hN : (1 - (p ^ 2 + q ^ 2)) * (u ^ 2 + v ^ 2) -
    2 * (p * u + q * v) + (p ^ 2 + q ^ 2) < 0)
    (hR : (0 : ℝ) < 1 - (p ^ 2 + q ^ 2)) :
    ((1 - (p ^ 2 + q ^ 2)) * v - q) ^ 2 < (p ^ 2 + q ^ 2) ^ 2 := by
  nlinarith [sq_nonneg ((1 - (p ^ 2 + q ^ 2)) * u - p), hN, hR,
    mul_pos hR (show (0 : ℝ) < 1 - (p ^ 2 + q ^ 2) from hR)]

private theorem geom_h2 (p q u v : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) (hq0 : 0 ≤ q)
    (hq : q ≤ 1 / 2) (hN : (1 - (p ^ 2 + q ^ 2)) * (u ^ 2 + v ^ 2) -
      2 * (p * u + q * v) + (p ^ 2 + q ^ 2) < 0)
    (hd00 : (0 : ℝ) < u ^ 2 + v ^ 2 - 1) (hd10 : (0 : ℝ) < (u - 1) ^ 2 + v ^ 2 - 1)
    (hkey : 2 * q * (q + (p ^ 2 + q ^ 2)) ≤ (1 - p) * (1 - (p ^ 2 + q ^ 2))) : False := by
  have hRle : p ^ 2 + q ^ 2 ≤ 1 / 2 := by
    nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hp), mul_nonneg hq0 (sub_nonneg.mpr hq)]
  have hR : (0 : ℝ) < 1 - (p ^ 2 + q ^ 2) := by linarith
  have hvbound : 2 * q * v ≤ 1 - p := by
    by_cases hv : v ≤ 0
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos hq0 hv, hp]
    · rw [not_le] at hv
      rcases eq_or_lt_of_le hq0 with hqeq | hqpos
      · rw [← hqeq]; norm_num; linarith [hp]
      have hv2 := geom_vbound p q u v hN hR
      have hRnn : (0 : ℝ) ≤ p ^ 2 + q ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
      have habs : |(1 - (p ^ 2 + q ^ 2)) * v - q| < p ^ 2 + q ^ 2 := by
        have h := sq_lt_sq.mp hv2
        rwa [abs_of_nonneg hRnn] at h
      have hvlt : (1 - (p ^ 2 + q ^ 2)) * v - q < p ^ 2 + q ^ 2 := (abs_lt.mp habs).2
      have hvlt2 : v < (q + (p ^ 2 + q ^ 2)) / (1 - (p ^ 2 + q ^ 2)) := by
        rw [lt_div_iff₀ hR]; linarith [hvlt]
      have hlt : 2 * q * v < 2 * q * ((q + (p ^ 2 + q ^ 2)) / (1 - (p ^ 2 + q ^ 2))) :=
        mul_lt_mul_of_pos_left hvlt2 (by linarith [hqpos])
      rw [mul_div_assoc'] at hlt
      have hle : 2 * q * (q + (p ^ 2 + q ^ 2)) / (1 - (p ^ 2 + q ^ 2)) ≤ 1 - p := by
        rw [div_le_iff₀ hR]; linarith [hkey]
      linarith [hlt, hle]
  have hWge : (0 : ℝ) ≤ 1 - (p ^ 2 + q ^ 2) - p := by nlinarith [hRle, hp, hq]
  set m : ℝ := min (u ^ 2 + v ^ 2 - 1) ((u - 1) ^ 2 + v ^ 2 - 1) with hmdef
  have hm : (0 : ℝ) < m := lt_min hd00 hd10
  have hWsum : (0 : ℝ) < (1 - (p ^ 2 + q ^ 2) - p) + p := by linarith
  have hm00 : m ≤ u ^ 2 + v ^ 2 - 1 := by rw [hmdef]; exact min_le_left _ _
  have hm10 : m ≤ (u - 1) ^ 2 + v ^ 2 - 1 := by rw [hmdef]; exact min_le_right _ _
  have e1 := mul_le_mul_of_nonneg_left hm00 hWge
  have e2 := mul_le_mul_of_nonneg_left hm10 hp0
  have hpos : (0 : ℝ) < (1 - (p ^ 2 + q ^ 2) - p) * (u ^ 2 + v ^ 2 - 1) +
      p * ((u - 1) ^ 2 + v ^ 2 - 1) := by
    have hprod : (0 : ℝ) < m * ((1 - (p ^ 2 + q ^ 2) - p) + p) := mul_pos hm hWsum
    have hring : m * ((1 - (p ^ 2 + q ^ 2) - p) + p) =
        (1 - (p ^ 2 + q ^ 2) - p) * m + p * m := by ring
    linarith [hprod, hring, e1, e2]
  have hid : (1 - (p ^ 2 + q ^ 2) - p) * (u ^ 2 + v ^ 2 - 1) +
      p * ((u - 1) ^ 2 + v ^ 2 - 1) =
      (1 - (p ^ 2 + q ^ 2)) * (u ^ 2 + v ^ 2) - 2 * (p * u + q * v) + (p ^ 2 + q ^ 2) +
        2 * q * v + p - 1 := by ring
  rw [hid] at hpos
  linarith [hN, hvbound]

private theorem geom_aux (p q u v : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) (hq0 : 0 ≤ q)
    (hq : q ≤ 1 / 2)
    (hsep : ∀ a b : ℤ, (p - a) ^ 2 + (q - b) ^ 2 < 1 → (u - a) ^ 2 + (v - b) ^ 2 > 1) :
    (p ^ 2 + q ^ 2) * (u ^ 2 + v ^ 2) ≤ (p - u) ^ 2 + (q - v) ^ 2 := by
  by_contra hcon
  have hN : (1 - (p ^ 2 + q ^ 2)) * (u ^ 2 + v ^ 2) -
      2 * (p * u + q * v) + (p ^ 2 + q ^ 2) < 0 := by nlinarith [hcon]
  have hd00 : (0 : ℝ) < u ^ 2 + v ^ 2 - 1 := by
    have h := hsep 0 0 (by
      simp only [Int.cast_zero, sub_zero]
      nlinarith [hp0, hp, hq0, hq, mul_nonneg hp0 (sub_nonneg.mpr hp),
        mul_nonneg hq0 (sub_nonneg.mpr hq)])
    have h2 := h
    simp only [Int.cast_zero, sub_zero] at h2
    linarith
  by_cases h10 : (p - 1) ^ 2 + q ^ 2 < 1
  · have ht10 := hsep 1 0 (by
      simp only [Int.cast_one, Int.cast_zero, sub_zero]
      exact h10)
    simp only [Int.cast_one, Int.cast_zero, sub_zero] at ht10
    have hd10 : (0 : ℝ) < (u - 1) ^ 2 + v ^ 2 - 1 := by linarith
    by_cases h01 : p ^ 2 + (q - 1) ^ 2 < 1
    · have ht01 := hsep 0 1 (by
        simp only [Int.cast_one, Int.cast_zero, sub_zero]
        exact h01)
      simp only [Int.cast_one, Int.cast_zero, sub_zero] at ht01
      have hd01 : (0 : ℝ) < u ^ 2 + (v - 1) ^ 2 - 1 := by linarith
      by_cases h11 : (p - 1) ^ 2 + (q - 1) ^ 2 < 1
      · have ht11 := hsep 1 1 (by
          simp only [Int.cast_one]
          exact h11)
        simp only [Int.cast_one] at ht11
        have hd11 : (0 : ℝ) < (u - 1) ^ 2 + (v - 1) ^ 2 - 1 := by linarith
        exact geom_h4 p q u v hp0 hp hq0 hq hN hd00 hd10 hd01 hd11
      · have g11 : (p - 1) ^ 2 + (q - 1) ^ 2 ≥ 1 := not_lt.mp h11
        have hW : (0 : ℝ) ≤ 1 - (p ^ 2 + q ^ 2) - p - q := by
          nlinarith only [sq_nonneg (p - q), sq_nonneg (p + q - 1), mul_nonneg hp0 hq0,
            mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hq), sq_nonneg (2 * p - 1),
            sq_nonneg (2 * q - 1), mul_nonneg hp0 (sub_nonneg.mpr hp),
            mul_nonneg hq0 (sub_nonneg.mpr hq), g11]
        exact geom_h3 p q u v hp0 hp hq0 hq hN hd00 hd10 hd01 hW
    · have g01 : p ^ 2 + (q - 1) ^ 2 ≥ 1 := not_lt.mp h01
      by_cases h11 : (p - 1) ^ 2 + (q - 1) ^ 2 < 1
      · exfalso
        have e : (q - 1) ^ 2 = q ^ 2 - 2 * q + 1 := by ring
        linarith [h11, g01, e, hq]
      · have hkey : 2 * q * (q + (p ^ 2 + q ^ 2)) ≤ (1 - p) * (1 - (p ^ 2 + q ^ 2)) := by
          nlinarith only [sq_nonneg (p - q), sq_nonneg (p + q - 1), mul_nonneg hp0 hq0,
            mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hq), sq_nonneg (2 * p - 1),
            sq_nonneg (2 * q - 1), mul_nonneg hp0 (sub_nonneg.mpr hp), h10, g01]
        exact geom_h2 p q u v hp0 hp hq0 hq hN hd00 hd10 hkey
  · have g10 : (p - 1) ^ 2 + q ^ 2 ≥ 1 := not_lt.mp h10
    by_cases h01 : p ^ 2 + (q - 1) ^ 2 < 1
    · have ht01 := hsep 0 1 (by
        simp only [Int.cast_one, Int.cast_zero, sub_zero]
        exact h01)
      simp only [Int.cast_one, Int.cast_zero, sub_zero] at ht01
      have hd01 : (0 : ℝ) < u ^ 2 + (v - 1) ^ 2 - 1 := by linarith
      by_cases h11 : (p - 1) ^ 2 + (q - 1) ^ 2 < 1
      · exfalso
        have e : (p - 1) ^ 2 = p ^ 2 - 2 * p + 1 := by ring
        linarith [h11, g10, e, hp]
      · have hkey : 2 * p * (p + (p ^ 2 + q ^ 2)) ≤ (1 - q) * (1 - (p ^ 2 + q ^ 2)) := by
          nlinarith only [sq_nonneg (p - q), sq_nonneg (p + q - 1), mul_nonneg hp0 hq0,
            mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hq), sq_nonneg (2 * p - 1),
            sq_nonneg (2 * q - 1), mul_nonneg hq0 (sub_nonneg.mpr hq), h01, g10]
        -- swapped version of geom_h2
        have hN' : (1 - (q ^ 2 + p ^ 2)) * (v ^ 2 + u ^ 2) -
            2 * (q * v + p * u) + (q ^ 2 + p ^ 2) < 0 := by
          have e : (1 - (q ^ 2 + p ^ 2)) * (v ^ 2 + u ^ 2) -
              2 * (q * v + p * u) + (q ^ 2 + p ^ 2) =
              (1 - (p ^ 2 + q ^ 2)) * (u ^ 2 + v ^ 2) -
                2 * (p * u + q * v) + (p ^ 2 + q ^ 2) := by ring
          rw [e]; exact hN
        have hd00' : (0 : ℝ) < v ^ 2 + u ^ 2 - 1 := by linarith [hd00]
        have hd01' : (0 : ℝ) < (v - 1) ^ 2 + u ^ 2 - 1 := by linarith [hd01]
        have hkey' : 2 * p * (p + (q ^ 2 + p ^ 2)) ≤ (1 - q) * (1 - (q ^ 2 + p ^ 2)) := by
          rw [show q ^ 2 + p ^ 2 = p ^ 2 + q ^ 2 from add_comm _ _]
          exact hkey
        exact geom_h2 q p v u hq0 hq hp0 hp hN' hd00' hd01' hkey'
    · have g01 : p ^ 2 + (q - 1) ^ 2 ≥ 1 := not_lt.mp h01
      exfalso
      have e10 : (p - 1) ^ 2 + q ^ 2 = (p ^ 2 + q ^ 2) - 2 * p + 1 := by ring
      have e01 : p ^ 2 + (q - 1) ^ 2 = (p ^ 2 + q ^ 2) - 2 * q + 1 := by ring
      have hrp : 2 * p ≤ p ^ 2 + q ^ 2 := by linarith [g10, e10]
      have hrq : 2 * q ≤ p ^ 2 + q ^ 2 := by linarith [g01, e01]
      have hp2 : p ^ 2 ≤ p / 2 := by nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hp)]
      have hq2 : q ^ 2 ≤ q / 2 := by nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq)]
      have hp_eq : p = 0 := by linarith
      have hq_eq : q = 0 := by linarith
      rw [hp_eq, hq_eq] at hN
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
        sub_zero, one_mul] at hN
      have h0 : u ^ 2 + v ^ 2 < 0 := by linarith [hN]
      exact absurd (add_nonneg (sq_nonneg u) (sq_nonneg v)) (by linarith)

private theorem normSq_sub_gaussian (x : ℂ) (a b : ℤ) :
    normSq (x - ((a : ℂ) + (b : ℂ) * I)) = (x.re - a) ^ 2 + (x.im - b) ^ 2 := by
  simp only [normSq_apply, sub_re, sub_im, add_re, add_im, intCast_re, intCast_im,
    mul_re, mul_im, I_re, I_im, mul_zero, mul_one, sub_zero, zero_add, add_zero]
  ring

/-- General-sign version of `geom_aux`, by reflecting each coordinate. -/
private theorem geom_general (p q u v : ℝ) (hp : |p| ≤ 1 / 2) (hq : |q| ≤ 1 / 2)
    (hsep : ∀ a b : ℤ, (p - a) ^ 2 + (q - b) ^ 2 < 1 → (u - a) ^ 2 + (v - b) ^ 2 > 1) :
    (p ^ 2 + q ^ 2) * (u ^ 2 + v ^ 2) ≤ (p - u) ^ 2 + (q - v) ^ 2 := by
  have hpabs := abs_le.mp hp
  have hqabs := abs_le.mp hq
  by_cases hp0 : 0 ≤ p
  · by_cases hq0 : 0 ≤ q
    · exact geom_aux p q u v hp0 hpabs.2 hq0 hqabs.2 hsep
    · have hq0' : 0 ≤ -q := by linarith [not_le.mp hq0]
      have hsep' : ∀ a b : ℤ, (p - a) ^ 2 + (-q - b) ^ 2 < 1 →
          (u - a) ^ 2 + (-v - b) ^ 2 > 1 := by
        intro a b h
        have h2 := hsep a (-b) (by
          simp only [Int.cast_neg]
          have e : (q - -((b : ℤ) : ℝ)) ^ 2 = (-q - (b : ℝ)) ^ 2 := by ring
          rw [e]
          exact h)
        simp only [Int.cast_neg] at h2
        have e : (-v - (b : ℝ)) ^ 2 = (v - -((b : ℤ) : ℝ)) ^ 2 := by ring
        rw [e]; exact h2
      have h := geom_aux p (-q) u (-v) hp0 hpabs.2 hq0' (by linarith) hsep'
      have e1 : (p - u) ^ 2 + (q - v) ^ 2 ≥ (p - u) ^ 2 + (-q - -v) ^ 2 := by
        have e' : (q - v) ^ 2 = (-q - -v) ^ 2 := by ring
        rw [e']
      linarith [h, e1]
  · have hp0' : 0 ≤ -p := by linarith [not_le.mp hp0]
    by_cases hq0 : 0 ≤ q
    · have hsep' : ∀ a b : ℤ, (-p - a) ^ 2 + (q - b) ^ 2 < 1 →
          (-u - a) ^ 2 + (v - b) ^ 2 > 1 := by
        intro a b h
        have h2 := hsep (-a) b (by
          simp only [Int.cast_neg]
          have e : (p - -((a : ℤ) : ℝ)) ^ 2 = (-p - (a : ℝ)) ^ 2 := by ring
          rw [e]
          exact h)
        simp only [Int.cast_neg] at h2
        have e : (-u - (a : ℝ)) ^ 2 = (u - -((a : ℤ) : ℝ)) ^ 2 := by ring
        rw [e]; exact h2
      have h := geom_aux (-p) q (-u) v hp0' (by linarith) hq0 hqabs.2 hsep'
      have e1 : (p - u) ^ 2 + (q - v) ^ 2 ≥ (-p - -u) ^ 2 + (q - v) ^ 2 := by
        have e' : (p - u) ^ 2 = (-p - -u) ^ 2 := by ring
        rw [e']
      linarith [h, e1]
    · have hq0' : 0 ≤ -q := by linarith [not_le.mp hq0]
      have hsep' : ∀ a b : ℤ, (-p - a) ^ 2 + (-q - b) ^ 2 < 1 →
          (-u - a) ^ 2 + (-v - b) ^ 2 > 1 := by
        intro a b h
        have h2 := hsep (-a) (-b) (by
          simp only [Int.cast_neg]
          have e1 : (p - -((a : ℤ) : ℝ)) ^ 2 = (-p - (a : ℝ)) ^ 2 := by ring
          have e2 : (q - -((b : ℤ) : ℝ)) ^ 2 = (-q - (b : ℝ)) ^ 2 := by ring
          rw [e1, e2]
          exact h)
        simp only [Int.cast_neg] at h2
        have e1 : (-u - (a : ℝ)) ^ 2 = (u - -((a : ℤ) : ℝ)) ^ 2 := by ring
        have e2 : (-v - (b : ℝ)) ^ 2 = (v - -((b : ℤ) : ℝ)) ^ 2 := by ring
        rw [e1, e2]; exact h2
      have h := geom_aux (-p) (-q) (-u) (-v) hp0' (by linarith) hq0' (by linarith) hsep'
      have e1 : (p - u) ^ 2 + (q - v) ^ 2 ≥ (-p - -u) ^ 2 + (-q - -v) ^ 2 := by
        have e1' : (p - u) ^ 2 = (-p - -u) ^ 2 := by ring
        have e2' : (q - v) ^ 2 = (-q - -v) ^ 2 := by ring
        rw [e1', e2']
      linarith [h, e1]

private theorem one_le_normSq_inv_sub {s t : ℂ}
    (hs : |s.re| ≤ 1 / 2 ∧ |s.im| ≤ 1 / 2)
    (hsep : ∀ a b : ℤ, normSq (s - ((a : ℂ) + (b : ℂ) * I)) < 1 →
      1 < normSq (t - ((a : ℂ) + (b : ℂ) * I)))
    (hs0 : s ≠ 0) (ht : 1 < normSq t) :
    1 ≤ normSq (s⁻¹ - t⁻¹) := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [normSq_zero] at ht
    norm_num at ht
  have hpos : (0 : ℝ) < normSq s * normSq t :=
    mul_pos (normSq_pos.mpr hs0) (by linarith [normSq_pos.mpr ht0])
  have h1 : normSq (s⁻¹ - t⁻¹) = normSq (s - t) / (normSq s * normSq t) := by
    have e : s⁻¹ - t⁻¹ = (t - s) / (s * t) := by
      field_simp
    rw [e, normSq_div, normSq_mul, show t - s = -(s - t) by ring, normSq_neg]
  rw [h1, le_div_iff₀ hpos, one_mul]
  have hsep' : ∀ a b : ℤ, (s.re - a) ^ 2 + (s.im - b) ^ 2 < 1 →
      (t.re - a) ^ 2 + (t.im - b) ^ 2 > 1 := by
    intro a b hab
    have h := hsep a b (by rw [normSq_sub_gaussian]; exact hab)
    rw [normSq_sub_gaussian] at h
    exact h
  have h2 := geom_general s.re s.im t.re t.im hs.1 hs.2 hsep'
  rw [normSq_apply, normSq_apply, normSq_apply]
  simp only [sub_re, sub_im, pow_two] at h2 ⊢
  exact h2

private theorem one_le_norm_of_one_le_normSq {x : ℂ} (hx : 1 ≤ normSq x) :
    1 ≤ ‖x‖ := by
  rw [normSq_eq_norm_sq] at hx
  by_contra hlt
  rw [not_le] at hlt
  have hsq : ‖x‖ ^ 2 < (1 : ℝ) ^ 2 :=
    (sq_lt_sq₀ (norm_nonneg x) zero_le_one).mpr hlt
  nlinarith [hsq, hx]

private theorem prod_eq_denom (z : ℂ) (n : ℕ) (hn : HurwitzLegal z (n + 1)) :
    ∏ j ∈ Finset.range (n + 1), hurwitzIter z (j + 1) =
      hurwitzIter z (n + 1) * hurwitzQ z n + (hurwitzPQ z n).1.2 := by
  induction n with
  | zero => simp [hurwitzQ, hurwitzPQ]
  | succ n ih =>
    have hn' : HurwitzLegal z (n + 1) := fun j hj => hn j (Nat.lt_succ_of_lt hj)
    have hprod := ih hn'
    rw [Finset.prod_range_succ _ (n + 1), hprod]
    have hne : hurwitzIter z (n + 1) - hurwitzDigit z (n + 1) ≠ 0 :=
      sub_ne_zero.mpr (hn (n + 1) (Nat.lt_succ_self _))
    have hpair : (hurwitzPQ z (n + 1)).1.2 = hurwitzQ z n := rfl
    have hQ : hurwitzQ z (n + 1) =
        hurwitzDigit z (n + 1) * hurwitzQ z n + (hurwitzPQ z n).1.2 := by
      simp [hurwitzQ, hurwitzPQ]
    have hiter : hurwitzIter z (n + 2) =
        (hurwitzIter z (n + 1) - hurwitzDigit z (n + 1))⁻¹ := rfl
    rw [hpair, hQ, hiter]
    field_simp
    ring

private theorem separated_dist (z : ℂ) (n : ℕ) (hn : HurwitzLegal z (n + 1)) :
    ∃ w, w * hurwitzQ z n = -(hurwitzPQ z n).1.2 ∧ hurwitzQ z n ≠ 0 ∧
      norm_hurwitzQ_lt_succ.Separated (hurwitzIter z (n + 1)) w ∧
      1 ≤ ‖hurwitzIter z (n + 1) - w‖ := by
  induction n with
  | zero =>
    obtain ⟨w, hw, hq, hsep⟩ := norm_hurwitzQ_lt_succ.denominator_state z 0 hn
    have hw0 : w = 0 := by
      have h0 : w * hurwitzQ z 0 = 0 := by
        rw [hw]
        simp [hurwitzPQ]
      have hQ0 : hurwitzQ z 0 = 1 := rfl
      rw [hQ0, mul_one] at h0
      exact h0
    refine ⟨w, hw, hq, hsep, ?_⟩
    rw [hw0, sub_zero]
    have hne : hurwitzIter z 0 ≠ hurwitzDigit z 0 := hn 0 Nat.zero_lt_one
    have hsq : normSq (hurwitzIter z 0 - hurwitzDigit z 0) ≤ 1 / 2 := by
      have hb := abs_re_sub_hurwitzRound_le (hurwitzIter z 0)
      have e : hurwitzIter z 0 - hurwitzDigit z 0 =
          hurwitzIter z 0 - hurwitzRound (hurwitzIter z 0) := rfl
      rw [e]
      rw [normSq_apply]
      obtain ⟨hr₁, hr₂⟩ := abs_le.mp hb.1
      obtain ⟨hi₁, hi₂⟩ := abs_le.mp hb.2
      nlinarith [mul_nonneg (sub_nonneg.mpr hr₂) (sub_nonneg.mpr hr₁),
        mul_nonneg (sub_nonneg.mpr hi₂) (sub_nonneg.mpr hi₁)]
    have hnorm : ‖hurwitzIter z 0 - hurwitzDigit z 0‖ ≤ 1 := by
      have h1 : ‖hurwitzIter z 0 - hurwitzDigit z 0‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
        rw [← normSq_eq_norm_sq]
        nlinarith [hsq]
      have h2 : ‖hurwitzIter z 0 - hurwitzDigit z 0‖ ≤ (1 : ℝ) :=
        (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa using h1)
      exact h2
    have hiter : hurwitzIter z 1 = (hurwitzIter z 0 - hurwitzDigit z 0)⁻¹ := rfl
    rw [hiter, norm_inv]
    have hpos : (0 : ℝ) < ‖hurwitzIter z 0 - hurwitzDigit z 0‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    exact one_le_inv₀ hpos |>.mpr hnorm
  | succ n ih =>
    have hn' : HurwitzLegal z (n + 1) := fun j hj => hn j (Nat.lt_succ_of_lt hj)
    obtain ⟨w, hw, hq, hsep, -⟩ := ih hn'
    obtain ⟨w', hw', hq', hsep'⟩ := norm_hurwitzQ_lt_succ.denominator_state z (n + 1) hn
    have hne : hurwitzIter z (n + 1) - hurwitzDigit z (n + 1) ≠ 0 :=
      sub_ne_zero.mpr (hn (n + 1) (Nat.lt_succ_self _))
    have hfar : 1 < normSq (w - hurwitzDigit z (n + 1)) := norm_hurwitzQ_lt_succ.digit_far hsep
    have ht0 : w - hurwitzDigit z (n + 1) ≠ 0 := by
      rintro h
      rw [h, normSq_zero] at hfar
      norm_num at hfar
    have hweq : w' = (w - hurwitzDigit z (n + 1))⁻¹ := by
      have hrec := norm_hurwitzQ_lt_succ.denominator_step hw
      have hpair : (hurwitzPQ z (n + 1)).1.2 = hurwitzQ z n := rfl
      have heq : (w - hurwitzDigit z (n + 1))⁻¹ * hurwitzQ z (n + 1) =
          -(hurwitzPQ z (n + 1)).1.2 := by
        rw [hpair, hrec]
        have hneg : hurwitzDigit z (n + 1) - w = -(w - hurwitzDigit z (n + 1)) := by ring
        rw [hneg, neg_mul, mul_neg, ← mul_assoc, inv_mul_cancel₀ ht0, one_mul]
      exact (mul_left_inj' hq').mp (by rw [hw', heq])
    refine ⟨w', hw', hq', hsep', ?_⟩
    have hgeom := one_le_normSq_inv_sub
      (s := hurwitzIter z (n + 1) - hurwitzDigit z (n + 1)) (t := w - hurwitzDigit z (n + 1))
      (by
        have hb := abs_re_sub_hurwitzRound_le (hurwitzIter z (n + 1))
        have e : hurwitzIter z (n + 1) - hurwitzDigit z (n + 1) =
            hurwitzIter z (n + 1) - hurwitzRound (hurwitzIter z (n + 1)) := rfl
        rw [e]
        exact hb)
      (by
        intro p q hab
        have hAq : hurwitzDigit z (n + 1) = norm_hurwitzQ_lt_succ.gaussian
            ⌊(hurwitzIter z (n + 1)).re + 1 / 2⌋
            ⌊(hurwitzIter z (n + 1)).im + 1 / 2⌋ := rfl
        have key := hsep (p + ⌊(hurwitzIter z (n + 1)).re + 1 / 2⌋)
          (q + ⌊(hurwitzIter z (n + 1)).im + 1 / 2⌋) (by
          have hg : norm_hurwitzQ_lt_succ.gaussian (p + ⌊(hurwitzIter z (n + 1)).re + 1 / 2⌋)
                (q + ⌊(hurwitzIter z (n + 1)).im + 1 / 2⌋) =
              norm_hurwitzQ_lt_succ.gaussian p q + hurwitzDigit z (n + 1) := by
            rw [hAq, norm_hurwitzQ_lt_succ.gaussian_add]
          rw [hg]
          have e : hurwitzIter z (n + 1) -
              (norm_hurwitzQ_lt_succ.gaussian p q + hurwitzDigit z (n + 1)) =
              (hurwitzIter z (n + 1) - hurwitzDigit z (n + 1)) -
                ((p : ℂ) + (q : ℂ) * I) := by
            have hgg : norm_hurwitzQ_lt_succ.gaussian p q = (p : ℂ) + (q : ℂ) * I := rfl
            rw [hgg]; ring
          rw [e]
          exact hab)
        have hg : norm_hurwitzQ_lt_succ.gaussian (p + ⌊(hurwitzIter z (n + 1)).re + 1 / 2⌋)
              (q + ⌊(hurwitzIter z (n + 1)).im + 1 / 2⌋) =
            norm_hurwitzQ_lt_succ.gaussian p q + hurwitzDigit z (n + 1) := by
          rw [hAq, norm_hurwitzQ_lt_succ.gaussian_add]
        rw [hg] at key
        have e : w - (norm_hurwitzQ_lt_succ.gaussian p q + hurwitzDigit z (n + 1)) =
            (w - hurwitzDigit z (n + 1)) - ((p : ℂ) + (q : ℂ) * I) := by
          have hgg : norm_hurwitzQ_lt_succ.gaussian p q = (p : ℂ) + (q : ℂ) * I := rfl
          rw [hgg]; ring
        rw [e] at key
        exact key)
      (by
        have : hurwitzIter z (n + 1) - hurwitzDigit z (n + 1) ≠ 0 := hne
        exact this)
      hfar
    have hiter : hurwitzIter z (n + 2) = (hurwitzIter z (n + 1) - hurwitzDigit z (n + 1))⁻¹ := rfl
    rw [hweq, hiter]
    exact one_le_norm_of_one_le_normSq hgeom

end norm_sub_hurwitz_convergent_le

/-- **Hurwitz's theorem: the convergent denominators grow in absolute value.** Let $z$ be a
complex number and let $Q_0, Q_1, \dots$ be the convergent denominators of its Hurwitz continued
fraction expansion. For every $n \ge 0$ such that $n + 1$ is a legal index for $z$ (the
expansion has not terminated before step $n + 1$), $|Q_n| < |Q_{n+1}|$.

Since $Q_0 = 1$, this gives $1 = |Q_0| < |Q_1| < \cdots < |Q_m|$ for every legal index $m$.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Lemma 1 (`integers-2024-A25-lem-1`). -/
theorem norm_hurwitzQ_lt_succ (z : ℂ) (n : ℕ) (hn : HurwitzLegal z (n + 1)) :
    ‖hurwitzQ z n‖ < ‖hurwitzQ z (n + 1)‖ := by
  obtain ⟨w, hw, hq, hsep⟩ := norm_hurwitzQ_lt_succ.denominator_state z n hn
  have hfar : 1 < normSq (w - hurwitzDigit z (n + 1)) :=
    norm_hurwitzQ_lt_succ.digit_far hsep
  rw [normSq_eq_norm_sq] at hfar
  have hnorm : 1 < ‖w - hurwitzDigit z (n + 1)‖ :=
    (sq_lt_sq₀ zero_le_one (norm_nonneg _)).1 (by simpa using hfar)
  rw [norm_hurwitzQ_lt_succ.denominator_step hw, norm_mul, norm_sub_rev]
  simpa only [one_mul] using mul_lt_mul_of_pos_right hnorm (norm_pos_iff.mpr hq)

/-- **Lakein's first theorem on Hurwitz convergents.** Let $z$ be a complex number and let $P_k$
and $Q_k$ be the convergent numerators and denominators of its Hurwitz continued fraction
expansion. For every legal index $k$ for $z$ (the expansion has not terminated before step $k$),
$|z - P_k / Q_k| \le 1 / |Q_k|^2$.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Lemma 2 (`integers-2024-A25-lem-2`). -/
theorem norm_sub_hurwitz_convergent_le (z : ℂ) (k : ℕ) (hk : HurwitzLegal z k) :
    ‖z - hurwitzP z k / hurwitzQ z k‖ ≤ 1 / ‖hurwitzQ z k‖ ^ 2 := by
  have hQ : hurwitzQ z k ≠ 0 := by
    cases k with
    | zero => simp [hurwitzQ, hurwitzPQ]
    | succ k =>
      have hlt := norm_hurwitzQ_lt_succ z k hk
      exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_le_of_lt (norm_nonneg _) hlt))
  have hQpos : (0 : ℝ) < ‖hurwitzQ z k‖ := norm_pos_iff.mpr hQ
  obtain ⟨herr, -⟩ := hurwitzQ_mul_sub_hurwitzP z k hk
  have hdiv : z - hurwitzP z k / hurwitzQ z k =
      (hurwitzQ z k * z - hurwitzP z k) / hurwitzQ z k := by
    rw [eq_div_iff hQ, sub_mul, div_mul_cancel₀ _ hQ]
    ring
  rw [hdiv, herr, norm_div, norm_mul]
  simp only [norm_pow, norm_neg, norm_one, one_pow, one_mul]
  by_cases hprod : (∏ j ∈ Finset.range (k + 1), hurwitzIter z (j + 1)) = 0
  · simp only [hprod, inv_zero, norm_zero, zero_div]
    exact one_div_nonneg.mpr (pow_nonneg (norm_nonneg _) 2)
  · have hlegal : HurwitzLegal z (k + 1) := by
      intro j hj
      by_cases hjk : j < k
      · exact hk j hjk
      · have hjk' : k = j := by omega
        subst hjk'
        intro heq
        have hz : hurwitzIter z (k + 1) = 0 := by
          have hrfl : hurwitzIter z (k + 1) =
              (hurwitzIter z k - hurwitzDigit z k)⁻¹ := rfl
          rw [hrfl, heq, sub_self, inv_zero]
        have hmem : k ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_self k)
        exact hprod (Finset.prod_eq_zero hmem hz)
    obtain ⟨w, hw, -, -, hdist⟩ :=
      norm_sub_hurwitz_convergent_le.separated_dist z k hlegal
    have hprod_eq := norm_sub_hurwitz_convergent_le.prod_eq_denom z k hlegal
    have hdenom : hurwitzIter z (k + 1) * hurwitzQ z k + (hurwitzPQ z k).1.2 =
        hurwitzQ z k * (hurwitzIter z (k + 1) - w) := by
      rw [mul_sub, mul_comm (hurwitzQ z k) w, hw]
      ring
    have hnormprod : ‖hurwitzQ z k‖ ≤
        ‖∏ j ∈ Finset.range (k + 1), hurwitzIter z (j + 1)‖ := by
      rw [hprod_eq, hdenom, norm_mul]
      exact le_mul_of_one_le_right (norm_nonneg _) hdist
    have hle : ‖(∏ j ∈ Finset.range (k + 1), hurwitzIter z (j + 1))⁻¹‖ ≤
        1 / ‖hurwitzQ z k‖ := by
      rw [norm_inv, inv_eq_one_div]
      exact one_div_le_one_div_of_le hQpos hnormprod
    have hrhs : (1 : ℝ) / ‖hurwitzQ z k‖ ^ 2 =
        (1 / ‖hurwitzQ z k‖) / ‖hurwitzQ z k‖ := by
      rw [div_div, sq]
    rw [hrhs, div_le_div_iff_of_pos_right hQpos]
    exact hle

end


end MetaMathlibExt
