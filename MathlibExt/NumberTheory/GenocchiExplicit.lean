/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Group.ForwardDiff
import MathlibExt.Combinatorics.Enumerative.GarabedianBernoulliStirling
import MathlibExt.Combinatorics.Enumerative.SuccPowStirlingSecond
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The Zerroukhat–Khaldi sums

The recurrence for the sum $U$ follows by applying the Stirling recurrence to its defining sum
and shifting the summation index. Pairing this recurrence with a row of Stirling numbers gives
the step identity for $H$ and the formulas for Bernoulli numbers in terms of forward differences
at one and at zero.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.GenocchiExplicitWanted

/-- **The Zerroukhat–Khaldi sum $U(m, k)$.** For natural numbers $m$ and $k$, define the rational
number
$$U(m, k) = \sum_{j=0}^{m} (-1)^{k+j+m} \frac{(k+j-1)!}{2^{k+j-1}} S(m, j),$$
where $S(m, j)$ is the Stirling number of the second kind and, in the term with $k = j = 0$,
$k + j - 1$ is read as $0$, so that this term is $(-1)^m S(m, 0)$. -/
def zerroU (m k : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (m + 1),
    (-1 : ℚ) ^ (k + j + m) * ((k + j - 1).factorial : ℚ) /
      2 ^ (k + j - 1) * (Nat.stirlingSecond m j : ℚ)

private theorem sum_stirlingSecond_succ (r : ℕ) (f : ℕ → ℚ) :
    ∑ j ∈ Finset.range (r + 1 + 1), f j * Nat.stirlingSecond (r + 1) j =
      ∑ j ∈ Finset.range (r + 1), (f j * j + f (j + 1)) * Nat.stirlingSecond r j := by
  -- The shifted sum agrees with the unshifted one because both boundary terms vanish.
  have shift :
      ∑ j ∈ Finset.range (r + 1), f (j + 1) * (j + 1 : ℕ) * Nat.stirlingSecond r (j + 1) =
        ∑ j ∈ Finset.range (r + 1), f j * j * Nat.stirlingSecond r j := by
    rw [Finset.sum_range_succ _ r,
      Finset.sum_range_succ' (fun j ↦ f j * j * Nat.stirlingSecond r j)]
    simp [Nat.stirlingSecond_eq_zero_of_lt r.lt_succ_self]
  rw [Finset.sum_range_succ' _ (r + 1)]
  simp only [Nat.stirlingSecond_succ_zero, Nat.cast_zero, mul_zero, add_zero,
    Nat.stirlingSecond_succ_succ, Nat.cast_add _ (Nat.stirlingSecond r _), Nat.cast_mul]
  simp only [mul_add, add_mul, ← mul_assoc, Finset.sum_add_distrib, shift]

/-- **Recurrence for the Zerroukhat–Khaldi sums $U$.** Let $U(m, k)$ be the Zerroukhat–Khaldi
sum. For all natural numbers $r$ and $k$ with $k \ge 1$,
$U(r+1, k) = U(r, k+1) + k \, U(r, k)$.

Source: Schehrazade Zerroukhat and Laala Khaldi, "A Note
on Explicit Formulas for Bernoulli and Genocchi Numbers",
Lemma 3. -/
theorem zerroU_succ (r k : ℕ) (hk : 1 ≤ k) :
    zerroU (r + 1) k = zerroU r (k + 1) + (k : ℚ) * zerroU r k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  unfold zerroU
  rw [sum_stirlingSecond_succ, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  -- Expand the next factorial and the next powers of −1 and 2 in the coefficient of S(r,j).
  simp only [Nat.succ_add, Nat.add_succ, Nat.succ_sub_one,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, Nat.cast_add, pow_succ, div_eq_mul_inv,
    mul_inv_rev]
  ring

/-- **Iterated forward differences of a power on $\mathbb{Q}$.** For a rational number $x$ and
natural numbers $k$ and $n$, $\Delta^k x^n$ denotes the value at $x$ of the $k$-th iterate of the
forward difference operator applied to the function $y \mapsto y^n$ on $\mathbb{Q}$, where the
forward difference of $f \colon \mathbb{Q} \to \mathbb{Q}$ is the function
$y \mapsto f(y + 1) - f(y)$. -/
noncomputable def diffPowEval (x : ℚ) (k n : ℕ) : ℚ :=
  ((fun f : ℚ → ℚ => fun y => f (y + 1) - f y)^[k]
    (fun y => y ^ n)) x

private theorem diffPowEval_one (m k : ℕ) :
    diffPowEval 1 k m = k.factorial * (Nat.stirlingSecond (m + 1) (k + 1) : ℚ) := by
  -- Compare the coefficients of the two Newton expansions of (k + 1) ^ m.
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    have h := shift_eq_sum_fwdDiff_iter (1 : ℚ) (fun y : ℚ ↦ y ^ m) k 1
    have hs := congrArg (Nat.cast : ℕ → ℚ) (MetaMathlibExt.succ_pow_eq_sum_stirlingSecond k m)
    push_cast at hs
    change (1 + k • (1 : ℚ)) ^ m =
      ∑ j ∈ Finset.range (k + 1), k.choose j • diffPowEval 1 j m at h
    simp only [nsmul_eq_mul, mul_one, add_comm (1 : ℚ), hs] at h
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at h
    simp only [Nat.choose_self, Nat.cast_one, one_mul] at h
    have hlower := Finset.sum_congr (s₁ := Finset.range k) rfl fun j hj ↦
      congrArg (fun z : ℚ ↦ (k.choose j : ℚ) * z) (ih j (Finset.mem_range.mp hj))
    simp only [← mul_assoc] at hlower
    simpa only [hlower, add_right_inj] using h.symm

/-- **The Zerroukhat–Khaldi sum $H_{n,m}$.** For natural numbers $n$ and $m$, define the rational
number
$$H_{n,m} = (-1)^n \, n \sum_{k=1}^{n-m} U(m+1, k) \, S(n-m, k),$$
where $U(m+1, k)$ is the Zerroukhat–Khaldi sum $U$, $S(n-m, k)$ is the Stirling number of the
second kind, and $n - m$ is truncated at $0$, so that $H_{n,m} = 0$ when $m \ge n$. -/
def zerroH (n m : ℕ) : ℚ :=
  (-1 : ℚ) ^ n * (n : ℚ) *
    ∑ k ∈ Finset.Icc 1 (n - m), zerroU (m + 1) k *
      (Nat.stirlingSecond (n - m) k : ℚ)

private def stirlingSum (r m : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (m + 1), zerroU r k * (Nat.stirlingSecond m k : ℚ)

-- The recurrence for U transfers one unit of the first index to the Stirling row.
private theorem stirlingSum_succ (r m : ℕ) (hm : 0 < m) :
    stirlingSum (r + 1) m = stirlingSum r (m + 1) := by
  unfold stirlingSum
  rw [sum_stirlingSecond_succ]
  apply Finset.sum_congr rfl
  intro k _
  cases k with
  | zero =>
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    simp
  | succ k =>
    rw [zerroU_succ r (k + 1) (by omega)]
    ring

private theorem zerroH_eq_mul_stirlingSum (n m : ℕ) (hm : m < n) :
    zerroH n m = (-1 : ℚ) ^ n * (n : ℚ) * stirlingSum (m + 1) (n - m) := by
  unfold zerroH stirlingSum
  congr 1
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢
    omega
  · intro k hk hk'
    have hk0 : k = 0 := by
      simp only [Finset.mem_Icc, Finset.mem_range] at hk hk'
      omega
    obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n - m ≠ 0)
    simp [hk0, hl]

/-- **A step identity for the Zerroukhat–Khaldi sums $H_{n,m}$.** Let $H_{n,m}$ denote the
Zerroukhat–Khaldi sum. For all natural numbers $n$ and $r$ with $r \ge 1$ and $n \ge r + 1$,
$H_{n,r} = H_{n,r-1}$.

Source: Schehrazade Zerroukhat and Laala Khaldi, "A Note
on Explicit Formulas for Bernoulli and Genocchi Numbers",
Lemma 3. -/
theorem zerroH_eq (n r : ℕ) (hr : 1 ≤ r)
    (hnr : r + 1 ≤ n) :
    zerroH n r = zerroH n (r - 1) := by
  rw [zerroH_eq_mul_stirlingSum n r (by omega),
    zerroH_eq_mul_stirlingSum n (r - 1) (by omega),
    show r - 1 + 1 = r by omega,
    show n - (r - 1) = (n - r) + 1 by omega,
    stirlingSum_succ r (n - r) (by omega)]

private theorem stirlingSum_eq_base (r m : ℕ) (hm : 0 < m) :
    stirlingSum r m = stirlingSum 0 (m + r) := by
  induction r generalizing m with
  | zero => simp
  | succ r ih =>
    rw [show m + (r + 1) = (m + 1) + r by omega, ← ih (m + 1) (by omega),
      stirlingSum_succ r m hm]

-- At r = 0 the only term of U is the signed factorial in Garabedian’s formula.
private theorem signed_bernoulli_eq_base (n : ℕ) (hn : 1 ≤ n) :
    (-1 : ℚ) ^ n * bernoulli n = (n : ℚ) / (2 ^ n - 1) * (-stirlingSum 0 n / 2) := by
  have hbase : stirlingSum 0 n = (-1 : ℚ) ^ n * ∑ k ∈ Finset.Icc 1 n,
      ((-1 : ℚ) ^ (n - k) * (k - 1).factorial * Nat.stirlingSecond n k) / 2 ^ (k - 1) := by
    unfold stirlingSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr_of_eq_on_inter
    · intro k hk hkn
      have hk0 : k = 0 := by
        simp only [Finset.mem_range, Finset.mem_Icc] at hk hkn
        omega
      obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      simp [hk0]
    · intro k hk hkn
      simp only [Finset.mem_range, Finset.mem_Icc] at hk hkn
      omega
    · intro k _ hk
      have hk' := (Finset.mem_Icc.mp hk).2
      have hsign : (-1 : ℚ) ^ n * (-1) ^ (n - k) = (-1) ^ k := by
        rw [← pow_add, show n + (n - k) = 2 * (n - k) + k by omega, pow_add, pow_mul]
        simp
      simp only [zerroU, zero_add, add_zero, Finset.sum_range_one,
        Nat.stirlingSecond_zero, Nat.cast_one, mul_one]
      rw [← hsign]
      ring
  have h := MetaMathlibExt.garabedian_genocchi_formula_general n
  have hnz : (2 : ℚ) ^ n - 1 ≠ 0 := sub_ne_zero.mpr (one_lt_pow₀ (by norm_num) (by omega)).ne'
  rw [hbase]
  field_simp [hnz]
  linear_combination -h

private theorem weighted_diff_eq (r k m : ℕ) :
    (∑ j ∈ Finset.range (r + 1),
        (-1 : ℚ) ^ (k + j + r) * 2 ^ (r - j) * ((k + j).factorial : ℚ) /
          k.factorial * (Nat.stirlingSecond r j : ℚ)) *
        (diffPowEval 1 k m / 2 ^ (k + 1 + r)) =
      -(zerroU r (k + 1) * Nat.stirlingSecond (m + 1) (k + 1)) / 2 := by
  simp only [diffPowEval_one, zerroU, Finset.sum_mul, ← Finset.sum_neg_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hjr := Finset.mem_range.mp hj
  simp only [Nat.succ_add, Nat.succ_sub_one, pow_succ]
  rw [show k + r = (r - j) + (k + j) by omega, pow_add (2 : ℚ) (r - j)]
  field_simp

set_option linter.unusedVariables false in
/-- **Bernoulli numbers via forward differences at $1$.** Let $n$ and $r$ be positive integers
with $n \ge r + 1$, let $B_n$ be the $n$-th Bernoulli number, let $S(a, b)$ denote the Stirling
numbers of the second kind and let $\Delta^k 1^m$ be the $k$-th forward difference of
$y \mapsto y^m$ at $1$. For $k \ge 0$ write
$e_k = \sum_{j=0}^{r} (-1)^{k+j+r} \, 2^{r-j} \, \frac{(k+j)!}{k!} \, S(r, j)$. Then
$(-1)^n B_n = \frac{n}{2^n - 1} \sum_{k=0}^{n-1-r} e_k \, \frac{\Delta^k 1^{n-1-r}}{2^{k+1+r}}$.

Source: Schehrazade Zerroukhat and Laala Khaldi, "A Note
on Explicit Formulas for Bernoulli and Genocchi Numbers",
Corollary 2. -/
theorem neg_one_pow_mul_bernoulli_eq_sum_one
    (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) (hnr : r + 1 ≤ n) :
    (-1 : ℚ) ^ n * bernoulli n =
      (n : ℚ) / (2 ^ n - 1) *
        ∑ k ∈ Finset.range (n - r),
          (∑ j ∈ Finset.range (r + 1),
            (-1 : ℚ) ^ (k + j + r) * 2 ^ (r - j) *
              ((k + j).factorial : ℚ) / k.factorial *
              (Nat.stirlingSecond r j : ℚ)) *
          (diffPowEval 1 k (n - 1 - r) / 2 ^ (k + 1 + r)) := by
  have hrow := stirlingSum_eq_base r (n - r) (by omega)
  rw [Nat.sub_add_cancel (by omega : r ≤ n)] at hrow
  rw [signed_bernoulli_eq_base n hn, ← hrow]
  congr 1
  rw [show n - r = n - 1 - r + 1 by omega]
  simp only [weighted_diff_eq, stirlingSum, Finset.sum_range_succ' _ (n - 1 - r + 1),
    Nat.stirlingSecond_succ_zero, Nat.cast_zero, mul_zero, add_zero,
    ← Finset.sum_div, Finset.sum_neg_distrib]

-- One more difference at zero is the difference at one minus the difference at zero, and the
-- Stirling recurrence matches this step.
private theorem diffPowEval_zero (m k : ℕ) :
    diffPowEval 0 k m = k.factorial * (Nat.stirlingSecond m k : ℚ) := by
  induction k with
  | zero => cases m <;> simp [diffPowEval]
  | succ k ih =>
    have hstep : diffPowEval 0 (k + 1) m = diffPowEval 1 k m - diffPowEval 0 k m := by
      simp only [diffPowEval, Function.iterate_succ_apply', zero_add]
    rw [hstep, diffPowEval_one, ih, Nat.stirlingSecond_succ_succ, Nat.factorial_succ]
    push_cast
    ring

-- For k ≥ 1 the k-th weighted difference at zero is minus half the k-th term of a Stirling row.
private theorem weighted_diff_zero_eq (r k m : ℕ) (hk : 1 ≤ k) :
    (∑ j ∈ Finset.range (r + 1),
        (-1 : ℚ) ^ (k + j + r + 1) * 2 ^ (r - j) * ((k + j - 1).factorial : ℚ) /
          k.factorial * (Nat.stirlingSecond r j : ℚ)) *
        (diffPowEval 0 k m / 2 ^ (k + r)) =
      -(zerroU r k * Nat.stirlingSecond m k) / 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
  simp only [diffPowEval_zero, zerroU, Finset.sum_mul, ← Finset.sum_neg_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hjr := Finset.mem_range.mp hj
  simp only [Nat.add_right_comm k 1 j, Nat.add_sub_cancel, pow_succ]
  rw [show k + 1 + r = (r - j) + (k + j) + 1 by omega, pow_succ, pow_add (2 : ℚ) (r - j)]
  field_simp

set_option linter.unusedVariables false in
/-- **Bernoulli numbers via forward differences at $0$.** Let $n$ and $r$ be positive integers
with $n \ge r + 1$, let $B_n$ be the $n$-th Bernoulli number, let $S(a, b)$ denote the Stirling
numbers of the second kind and let $\Delta^k 0^m$ be the $k$-th forward difference of
$y \mapsto y^m$ at $0$. For $k \ge 1$ write
$d_k = \sum_{j=0}^{r} (-1)^{k+j+r+1} \, 2^{r-j} \, \frac{(k+j-1)!}{k!} \, S(r, j)$. Then
$(-1)^n B_n = \frac{n}{2^n - 1} \sum_{k=1}^{n-r} d_k \, \frac{\Delta^k 0^{n-r}}{2^{k+r}}$.

Source: Schehrazade Zerroukhat and Laala Khaldi, "A Note
on Explicit Formulas for Bernoulli and Genocchi Numbers",
Corollary 2. -/
theorem neg_one_pow_mul_bernoulli_eq_sum_zero
    (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) (hnr : r + 1 ≤ n) :
    (-1 : ℚ) ^ n * bernoulli n =
      (n : ℚ) / (2 ^ n - 1) *
        ∑ k ∈ Finset.Icc 1 (n - r),
          (∑ j ∈ Finset.range (r + 1),
            (-1 : ℚ) ^ (k + j + r + 1) * 2 ^ (r - j) *
              ((k + j - 1).factorial : ℚ) / k.factorial *
              (Nat.stirlingSecond r j : ℚ)) *
          (diffPowEval 0 k (n - r) / 2 ^ (k + r)) := by
  have hrow := stirlingSum_eq_base r (n - r) (by omega)
  rw [Nat.sub_add_cancel (by omega : r ≤ n)] at hrow
  rw [signed_bernoulli_eq_base n hn, ← hrow]
  congr 1
  -- The row sum starts at k = 0, where the Stirling number S(n - r, 0) vanishes.
  obtain ⟨m, hm⟩ : ∃ m, n - r = m + 1 := ⟨n - r - 1, by omega⟩
  rw [Finset.sum_congr rfl fun k hk ↦
      weighted_diff_zero_eq r k (n - r) (Finset.mem_Icc.mp hk).1,
    Finset.sum_subset (s₂ := Finset.range (n - r + 1))]
  · simp only [stirlingSum, ← Finset.sum_div, Finset.sum_neg_distrib]
  · intro k hk
    simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢
    omega
  · intro k hk hk'
    have hk0 : k = 0 := by
      simp only [Finset.mem_Icc, Finset.mem_range, not_and_or, not_le] at hk hk'
      omega
    simp [hk0, hm, Nat.stirlingSecond_succ_zero]

end MathlibExt.NumberTheory.GenocchiExplicitWanted
