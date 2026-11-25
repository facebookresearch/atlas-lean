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

end

end MetaMathlibExt
