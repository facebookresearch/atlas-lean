/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Bernoulli.PolyBernoulliDuality
public import MathlibExt.NumberTheory.Bernoulli.StirlingHarmonic
public import MathlibExt.NumberTheory.Bernoulli.SumModPrime
public import MathlibExt.NumberTheory.Bernoulli.TruncatedSumModPrime
public import MathlibExt.NumberTheory.Bernoulli.WeightedSum
public import Mathlib.NumberTheory.Harmonic.Defs
import MathlibExt.Combinatorics.Enumerative.StirlingDescPochhammer

/-!
# A Bernoulli–harmonic power-sum identity

We prove Kargın and Mutluer's Bernoulli–harmonic power-sum identity: the left-hand side
is rewritten with their Stirling–harmonic expression for the Bernoulli numbers
(`sum_stirling_harmonic_eq_bernoulli`), and both sides are identified with a
Stirling-weighted sum of falling factorials via a harmonic-weighted evaluation identity.

Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, Corollary 1,
equation (11).
-/

namespace MetaMathlibExt

open Finset

/-- Falling factorials expand in powers with signed Stirling coefficients. -/
private theorem descFactorial_eq_sum_stirlingFirst (m k n : ℕ) (hkn : k ≤ n) :
    ((Nat.descFactorial m k : ℕ) : ℚ) =
      ∑ r ∈ range (n + 1),
        (-1 : ℚ) ^ (k - r) * (Nat.stirlingFirst k r : ℚ) * (m : ℚ) ^ r := by
  have hexpand : ((Nat.descFactorial m k : ℕ) : ℚ) =
      ∑ r ∈ range (k + 1),
        (-1 : ℚ) ^ (k - r) * (Nat.stirlingFirst k r : ℚ) * (m : ℚ) ^ r := by
    have hZ : (descPochhammer ℤ k).eval (m : ℤ) =
        ∑ r ∈ range (k + 1), signedStirlingFirst k r * (m : ℤ) ^ r := by
      rw [descPochhammer_eq_sum_signedStirlingFirst]
      simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
    have hcast : ((((descPochhammer ℤ k).eval (m : ℤ) : ℤ)) : ℚ) =
        ∑ r ∈ range (k + 1),
          (-1 : ℚ) ^ (k - r) * (Nat.stirlingFirst k r : ℚ) * (m : ℚ) ^ r := by
      have h2 : ((((descPochhammer ℤ k).eval (m : ℤ) : ℤ)) : ℚ) =
          (((∑ r ∈ range (k + 1), signedStirlingFirst k r * (m : ℤ) ^ r : ℤ)) : ℚ) := by
        exact_mod_cast hZ
      rw [h2, Int.cast_sum]
      refine sum_congr rfl fun r _ => ?_
      rw [signedStirlingFirst_apply]
      push_cast
      ring
    have heval : (descPochhammer ℚ k).eval (m : ℚ) = ((Nat.descFactorial m k : ℕ) : ℚ) :=
      descPochhammer_eval_eq_descFactorial ℚ m k
    have hmap : ((((descPochhammer ℤ k).eval (m : ℤ) : ℤ)) : ℚ) =
        (descPochhammer ℚ k).eval (m : ℚ) := by
      have h := Polynomial.eval_map_apply (p := descPochhammer ℤ k)
        (Int.castRingHom ℚ) (m : ℤ)
      rw [descPochhammer_map, map_natCast] at h
      exact h.symm
    rw [← heval, ← hmap]
    exact hcast
  rw [hexpand]
  refine sum_subset (range_subset_range.mpr (by omega)) fun r _ hkr => ?_
  simp only [mem_range, not_lt] at hkr
  rw [Nat.stirlingFirst_eq_zero_of_lt (show k < r by omega)]
  simp

/-- The Stirling–harmonic sum over a full range agrees with the interval sum. -/
private theorem sum_range_stirling_harmonic (n j : ℕ) (_hj : j ≤ n) :
    (∑ k ∈ range (n + 1), (-1 : ℚ) ^ (k - j) * (Nat.stirlingSecond n k : ℚ) *
      (Nat.stirlingFirst k j : ℚ) * harmonic k) =
    ∑ k ∈ Icc j n, (-1 : ℚ) ^ (k - j) * (Nat.stirlingSecond n k : ℚ) *
      (Nat.stirlingFirst k j : ℚ) * harmonic k := by
  symm
  refine sum_subset ?_ ?_
  · intro k hk
    obtain ⟨_, hkn⟩ := mem_Icc.mp hk
    exact mem_range.mpr (by omega)
  · intro k hk hkj
    simp only [mem_range] at hk
    simp only [mem_Icc] at hkj
    have hkj' : k < j := by omega
    rw [Nat.stirlingFirst_eq_zero_of_lt hkj']
    simp

/-- The diagonal Stirling–harmonic sum equals the harmonic number. -/
private theorem sum_range_stirling_harmonic_diag (n : ℕ) :
    (∑ k ∈ range (n + 1), (-1 : ℚ) ^ (k - n) * (Nat.stirlingSecond n k : ℚ) *
      (Nat.stirlingFirst k n : ℚ) * harmonic k) = harmonic n := by
  rw [sum_eq_single n]
  · rw [Nat.sub_self, pow_zero, Nat.stirlingSecond_self, Nat.stirlingFirst_self]
    simp
  · intro k hk hkn
    simp only [mem_range] at hk
    have hkn' : k < n := by omega
    rw [Nat.stirlingFirst_eq_zero_of_lt hkn']
    simp
  · simp

/-- Each left-hand summand is a Stirling–harmonic sum weighted by a power of `m`. -/
private theorem lhs_term_eq (n m i : ℕ) (hi : i ∈ Icc 1 n) :
    ((n.choose i : ℚ) - 1) * (bernoulli i / (i : ℚ)) * (m : ℚ) ^ (n - i) =
      (m : ℚ) ^ (n - i) * ∑ k ∈ range (n + 1),
        (-1 : ℚ) ^ (k - (n - i)) * (Nat.stirlingSecond n k : ℚ) *
          (Nat.stirlingFirst k (n - i) : ℚ) * harmonic k := by
  obtain ⟨hi1, hin⟩ := mem_Icc.mp hi
  have hlt : n - i < n := by omega
  have hle : n - i ≤ n := Nat.sub_le n i
  rw [sum_range_stirling_harmonic n (n - i) hle,
    sum_stirling_harmonic_eq_bernoulli n (n - i) hlt]
  have hsub : n - (n - i) = i := Nat.sub_sub_self hin
  have hchoose : n.choose (n - i) = n.choose i := Nat.choose_symm hin
  have hden : (n : ℚ) - ((n - i : ℕ) : ℚ) = (i : ℚ) := by
    rw [Nat.cast_sub hin]
    ring
  rw [hsub, hchoose, hden]
  ring

/-- Reindex a sum over `Icc 1 n` as a sum over `range n`. -/
private theorem sum_Icc_one_eq_sum_range (f : ℕ → ℚ) (n : ℕ) :
    (∑ i ∈ Icc 1 n, f i) = ∑ i ∈ range n, f (i + 1) := by
  induction n with
  | zero =>
    rw [Icc_eq_empty (by omega : ¬ (1:ℕ) ≤ 0)]
    simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega), sum_range_succ, ih]

/-- The inner Stirling sum over `i` evaluates to a falling factorial. -/
private theorem inner_sum_eq (n m k : ℕ) (hkn : k ≤ n) :
    (∑ i ∈ range (n + 1),
      (m : ℚ) ^ (n - i) * ((-1 : ℚ) ^ (k - (n - i)) * (Nat.stirlingFirst k (n - i) : ℚ))) =
      ((Nat.descFactorial m k : ℕ) : ℚ) := by
  have hreflect : (∑ i ∈ range (n + 1),
      (m : ℚ) ^ (n - i) * ((-1 : ℚ) ^ (k - (n - i)) * (Nat.stirlingFirst k (n - i) : ℚ))) =
      ∑ r ∈ range (n + 1),
        (m : ℚ) ^ r * ((-1 : ℚ) ^ (k - r) * (Nat.stirlingFirst k r : ℚ)) := by
    have h := sum_range_reflect
      (fun r => (m : ℚ) ^ r * ((-1 : ℚ) ^ (k - r) * (Nat.stirlingFirst k r : ℚ))) (n + 1)
    simpa only [Nat.add_sub_cancel] using h
  rw [hreflect]
  have h := descFactorial_eq_sum_stirlingFirst m k n hkn
  rw [h]
  refine sum_congr rfl fun r _ => ?_
  ring

/-- The double Stirling–harmonic sum collapses to falling factorials. -/
private theorem range_sum_eq (n m : ℕ) :
    (∑ i ∈ range (n + 1),
      (m : ℚ) ^ (n - i) * ∑ k ∈ range (n + 1),
        (-1 : ℚ) ^ (k - (n - i)) * (Nat.stirlingSecond n k : ℚ) *
          (Nat.stirlingFirst k (n - i) : ℚ) * harmonic k) =
    ∑ k ∈ range (n + 1),
      (Nat.stirlingSecond n k : ℚ) * harmonic k * ((Nat.descFactorial m k : ℕ) : ℚ) := by
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := by
    simp only [mem_range] at hk
    omega
  have hfactor : ∀ i ∈ range (n + 1),
      (m : ℚ) ^ (n - i) * ((-1 : ℚ) ^ (k - (n - i)) * (Nat.stirlingSecond n k : ℚ) *
        (Nat.stirlingFirst k (n - i) : ℚ) * harmonic k) =
      (Nat.stirlingSecond n k : ℚ) * harmonic k *
        ((m : ℚ) ^ (n - i) * ((-1 : ℚ) ^ (k - (n - i)) * (Nat.stirlingFirst k (n - i) : ℚ))) := by
    intro i _
    ring
  rw [sum_congr rfl hfactor, ← mul_sum, inner_sum_eq n m k hkn]

/-- The left-hand side as a Stirling-weighted sum of falling factorials. -/
private theorem lhs_eq_sum_descFactorial (n m : ℕ) :
    (∑ j ∈ Icc 1 n, ((n.choose j : ℚ) - 1) * (bernoulli j / (j : ℚ)) * (m : ℚ) ^ (n - j)) =
      (∑ k ∈ range (n + 1),
        (Nat.stirlingSecond n k : ℚ) * harmonic k * ((Nat.descFactorial m k : ℕ) : ℚ)) -
        (m : ℚ) ^ n * harmonic n := by
  set g' : ℕ → ℚ := fun i => (m : ℚ) ^ (n - i) * ∑ k ∈ range (n + 1),
    (-1 : ℚ) ^ (k - (n - i)) * (Nat.stirlingSecond n k : ℚ) *
      (Nat.stirlingFirst k (n - i) : ℚ) * harmonic k with hg'
  have hterm : ∀ j ∈ Icc 1 n,
      ((n.choose j : ℚ) - 1) * (bernoulli j / (j : ℚ)) * (m : ℚ) ^ (n - j) = g' j :=
    fun j hj => lhs_term_eq n m j hj
  rw [sum_congr rfl hterm]
  have hbridge := sum_Icc_one_eq_sum_range g' n
  have hsplit := sum_range_succ' g' n
  have hswap : (∑ i ∈ range (n + 1), g' i) =
      ∑ k ∈ range (n + 1),
        (Nat.stirlingSecond n k : ℚ) * harmonic k * ((Nat.descFactorial m k : ℕ) : ℚ) := by
    simp only [hg']
    exact range_sum_eq n m
  have hdiag : g' 0 = (m : ℚ) ^ n * harmonic n := by
    simp only [hg', Nat.sub_zero]
    rw [sum_range_stirling_harmonic_diag]
  linear_combination hbridge - hsplit + hswap - hdiag

/-- Successor recurrence for descending factorials. -/
private theorem succ_descFactorial (a k : ℕ) :
    Nat.descFactorial (a + 1) (k + 1) = (a + 1) * Nat.descFactorial a k := by
  induction k with
  | zero =>
    change Nat.descFactorial (a + 1) 1 = (a + 1) * Nat.descFactorial a 0
    rw [Nat.descFactorial_one, Nat.descFactorial_zero, mul_one]
  | succ k ih =>
    have h1 := Nat.descFactorial_succ (a + 1) (k + 1)
    have h3 : (a + 1) - (k + 1) = a - k := by omega
    rw [h1, h3, ih, Nat.descFactorial_succ]
    ring

/-- Successive falling factorials differ by a multiple of the lower one. -/
private theorem succ_descFactorial_diff (a k : ℕ) :
    ((Nat.descFactorial (a + 1) (k + 1) : ℕ) : ℚ) - ((Nat.descFactorial a (k + 1) : ℕ) : ℚ) =
      ((k : ℚ) + 1) * ((Nat.descFactorial a k : ℕ) : ℚ) := by
  by_cases hka : k ≤ a
  · have h1 : Nat.descFactorial (a + 1) (k + 1) = (a + 1) * Nat.descFactorial a k :=
      succ_descFactorial a k
    have h2 : Nat.descFactorial a (k + 1) = (a - k) * Nat.descFactorial a k :=
      Nat.descFactorial_succ a k
    have e1 : ((Nat.descFactorial (a + 1) (k + 1) : ℕ) : ℚ) =
        ((a : ℚ) + 1) * ((Nat.descFactorial a k : ℕ) : ℚ) := by
      rw [h1]
      push_cast
      ring
    have e2 : ((Nat.descFactorial a (k + 1) : ℕ) : ℚ) =
        ((a : ℚ) - (k : ℚ)) * ((Nat.descFactorial a k : ℕ) : ℚ) := by
      have hcast : ((Nat.descFactorial a (k + 1) : ℕ) : ℚ) =
          ((((a - k) * Nat.descFactorial a k : ℕ)) : ℚ) := by
        exact_mod_cast h2
      rw [hcast, Nat.cast_mul, Nat.cast_sub hka]
    rw [e1, e2]
    ring
  · have hlt : a < k := by omega
    have hz1 : Nat.descFactorial (a + 1) (k + 1) = 0 :=
      Nat.descFactorial_of_lt (by omega)
    have hz2 : Nat.descFactorial a (k + 1) = 0 := Nat.descFactorial_of_lt (by omega)
    have hz3 : Nat.descFactorial a k = 0 := Nat.descFactorial_of_lt hlt
    rw [hz1, hz2, hz3]
    simp

/-- A harmonic-weighted sum of falling factorials. -/
private theorem sum_descFactorial_div_eq (k : ℕ) : ∀ m : ℕ,
    (∑ j ∈ Icc 1 m, ((Nat.descFactorial (m - j) k : ℕ) : ℚ) / (j : ℚ)) =
      (harmonic m - harmonic k) * ((Nat.descFactorial m k : ℕ) : ℚ) := by
  induction k with
  | zero =>
    intro m
    simp only [Nat.descFactorial_zero, Nat.cast_one]
    rw [harmonic_zero, sub_zero, mul_one]
    induction m with
    | zero =>
      rw [Icc_eq_empty (by omega : ¬ (1:ℕ) ≤ 0)]
      simp
    | succ m ihm =>
      rw [sum_Icc_succ_top (by omega : 1 ≤ m + 1), harmonic_succ, ihm, one_div]
  | succ k ih =>
    intro m
    induction m with
    | zero =>
      rw [Icc_eq_empty (by omega : ¬ (1:ℕ) ≤ 0)]
      simp only [sum_empty]
      have h0 : Nat.descFactorial 0 (k + 1) = 0 := Nat.descFactorial_of_lt (by omega)
      rw [h0, Nat.cast_zero, mul_zero]
    | succ m ihm =>
      by_cases hkm : k + 1 ≤ m + 1
      · have hkm' : k ≤ m := by omega
        have hpeel : (∑ j ∈ Icc 1 (m + 1),
            ((Nat.descFactorial (m + 1 - j) (k + 1) : ℕ) : ℚ) / (j : ℚ)) =
            (∑ j ∈ Icc 1 m, ((Nat.descFactorial (m + 1 - j) (k + 1) : ℕ) : ℚ) / (j : ℚ)) := by
          rw [sum_Icc_succ_top (by omega)]
          have htop : ((Nat.descFactorial (m + 1 - (m + 1)) (k + 1) : ℕ) : ℚ) /
              ((m + 1 : ℕ) : ℚ) = 0 := by
            rw [Nat.sub_self, Nat.descFactorial_of_lt (by omega : 0 < k + 1),
              Nat.cast_zero, zero_div]
          rw [htop, add_zero]
        rw [hpeel]
        have hdiff : ∀ j ∈ Icc 1 m,
            ((Nat.descFactorial (m + 1 - j) (k + 1) : ℕ) : ℚ) / (j : ℚ) =
              ((Nat.descFactorial (m - j) (k + 1) : ℕ) : ℚ) / (j : ℚ) +
                ((k : ℚ) + 1) * ((((Nat.descFactorial (m - j) k : ℕ) : ℚ)) / (j : ℚ)) := by
          intro j hj
          have hjle : j ≤ m := (mem_Icc.mp hj).2
          have hrewrite : m + 1 - j = (m - j) + 1 := by omega
          rw [hrewrite]
          have hdesc := succ_descFactorial_diff (m - j) k
          have hsum : ((Nat.descFactorial ((m - j) + 1) (k + 1) : ℕ) : ℚ) =
              ((Nat.descFactorial (m - j) (k + 1) : ℕ) : ℚ) +
                ((k : ℚ) + 1) * ((Nat.descFactorial (m - j) k : ℕ) : ℚ) := by
            linear_combination hdesc
          rw [hsum, add_div, mul_div_assoc]
        rw [sum_congr rfl hdiff, sum_add_distrib, ← mul_sum, ihm, ih m]
        rw [harmonic_succ m, harmonic_succ k]
        have hD1 : ((Nat.descFactorial (m + 1) (k + 1) : ℕ) : ℚ) =
            (((m + 1 : ℕ)) : ℚ) * ((Nat.descFactorial m k : ℕ) : ℚ) := by
          have h1 : Nat.descFactorial (m + 1) (k + 1) = (m + 1) * Nat.descFactorial m k :=
            succ_descFactorial m k
          have hcast : ((Nat.descFactorial (m + 1) (k + 1) : ℕ) : ℚ) =
              ((((m + 1) * Nat.descFactorial m k : ℕ)) : ℚ) := by
            exact_mod_cast h1
          rw [hcast, Nat.cast_mul]
        have hD2 : ((Nat.descFactorial m (k + 1) : ℕ) : ℚ) =
            ((m : ℚ) - (k : ℚ)) * ((Nat.descFactorial m k : ℕ) : ℚ) := by
          have h2 : Nat.descFactorial m (k + 1) = (m - k) * Nat.descFactorial m k :=
            Nat.descFactorial_succ m k
          have hcast : ((Nat.descFactorial m (k + 1) : ℕ) : ℚ) =
              ((((m - k) * Nat.descFactorial m k : ℕ)) : ℚ) := by
            exact_mod_cast h2
          rw [hcast, Nat.cast_mul, Nat.cast_sub hkm']
        rw [hD1, hD2]
        push_cast
        have hk1 : (k : ℚ) + 1 ≠ 0 := by positivity
        have hm1 : (m : ℚ) + 1 ≠ 0 := by positivity
        field_simp
        ring
      · have hkm'' : m + 1 < k + 1 := by omega
        have hLHS : (∑ j ∈ Icc 1 (m + 1),
            ((Nat.descFactorial (m + 1 - j) (k + 1) : ℕ) : ℚ) / (j : ℚ)) = 0 := by
          refine sum_eq_zero fun j hj => ?_
          obtain ⟨hj1, hjle⟩ := mem_Icc.mp hj
          have hlt : m + 1 - j < k + 1 := by omega
          rw [Nat.descFactorial_of_lt hlt, Nat.cast_zero, zero_div]
        have hRHS : (harmonic (m + 1) - harmonic (k + 1)) *
            ((Nat.descFactorial (m + 1) (k + 1) : ℕ) : ℚ) = 0 := by
          have h0 : Nat.descFactorial (m + 1) (k + 1) = 0 :=
            Nat.descFactorial_of_lt hkm''
          rw [h0, Nat.cast_zero, mul_zero]
        rw [hLHS, hRHS]

/-- Powers expand in falling factorials with Stirling coefficients of the second kind. -/
private theorem pow_eq_sum_stirlingSecond (a n : ℕ) :
    ((a : ℕ) : ℚ) ^ n =
      ∑ k ∈ range (n + 1),
        (Nat.stirlingSecond n k : ℚ) * ((Nat.descFactorial a k : ℕ) : ℚ) := by
  have h := Nat.pow_eq_sum_stirlingSecond_mul_descFactorial a n
  have hcast : ((a ^ n : ℕ) : ℚ) = ((∑ j ∈ range (n + 1),
      n.stirlingSecond j * a.descFactorial j : ℕ) : ℚ) := by exact_mod_cast h
  rw [Nat.cast_pow, Nat.cast_sum] at hcast
  simpa only [Nat.cast_mul] using hcast

/-- The Stirling-weighted sum of falling factorials equals the right-hand side. -/
private theorem sum_descFactorial_eq (n m : ℕ) :
    (∑ k ∈ range (n + 1),
      (Nat.stirlingSecond n k : ℚ) * harmonic k * ((Nat.descFactorial m k : ℕ) : ℚ)) =
      (m : ℚ) ^ n * harmonic m -
        ∑ j ∈ Icc 1 m, (((m - j : ℕ)) : ℚ) ^ n / (j : ℚ) := by
  have hpow : ∀ j ∈ Icc 1 m,
      (((m - j : ℕ)) : ℚ) ^ n / (j : ℚ) =
        (∑ k ∈ range (n + 1),
          (Nat.stirlingSecond n k : ℚ) * ((Nat.descFactorial (m - j) k : ℕ) : ℚ)) / (j : ℚ) := by
    intro j _
    rw [pow_eq_sum_stirlingSecond (m - j) n]
  rw [sum_congr rfl hpow]
  have hdiv : ∀ j ∈ Icc 1 m,
      (∑ k ∈ range (n + 1),
        (Nat.stirlingSecond n k : ℚ) * ((Nat.descFactorial (m - j) k : ℕ) : ℚ)) / (j : ℚ) =
        ∑ k ∈ range (n + 1),
          (Nat.stirlingSecond n k : ℚ) * ((Nat.descFactorial (m - j) k : ℕ) : ℚ) / (j : ℚ) := by
    intro j _
    rw [sum_div]
  rw [sum_congr rfl hdiv, sum_comm]
  have hfactor : ∀ k ∈ range (n + 1),
      (∑ j ∈ Icc 1 m,
        (Nat.stirlingSecond n k : ℚ) * ((Nat.descFactorial (m - j) k : ℕ) : ℚ) / (j : ℚ)) =
        (Nat.stirlingSecond n k : ℚ) *
          ∑ j ∈ Icc 1 m, ((Nat.descFactorial (m - j) k : ℕ) : ℚ) / (j : ℚ) := by
    intro k _
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    ring
  rw [sum_congr rfl hfactor]
  simp only [sum_descFactorial_div_eq]
  have hmpow := pow_eq_sum_stirlingSecond m n
  have hexpand : (∑ k ∈ range (n + 1),
        (Nat.stirlingSecond n k : ℚ) * ((harmonic m - harmonic k) *
          ((Nat.descFactorial m k : ℕ) : ℚ))) =
      harmonic m * (m : ℚ) ^ n -
        ∑ k ∈ range (n + 1),
          (Nat.stirlingSecond n k : ℚ) * harmonic k * ((Nat.descFactorial m k : ℕ) : ℚ) := by
    have hterm : ∀ k ∈ range (n + 1),
        (Nat.stirlingSecond n k : ℚ) * ((harmonic m - harmonic k) *
          ((Nat.descFactorial m k : ℕ) : ℚ)) =
          harmonic m * ((Nat.stirlingSecond n k : ℚ) * ((Nat.descFactorial m k : ℕ) : ℚ)) -
            (Nat.stirlingSecond n k : ℚ) * harmonic k * ((Nat.descFactorial m k : ℕ) : ℚ) := by
      intro k _
      ring
    rw [sum_congr rfl hterm, sum_sub_distrib, ← mul_sum, hmpow]
  rw [hexpand]
  ring

-- The positivity hypotheses are part of the interface; the argument is uniform in `n`, `m`.
set_option linter.unusedVariables false in
/--
**A Bernoulli–harmonic power-sum identity.** Let $B_j$ denote the Bernoulli numbers with
$B_1 = -\tfrac12$, and let $H_m = \sum_{i=1}^{m} 1/i$ denote the harmonic numbers. For all
positive integers $n$ and $m$,
$$\sum_{j=1}^{n} \left(\binom{n}{j} - 1\right) \frac{B_j}{j} m^{n-j} =
m^n (H_m - H_n) - \sum_{j=1}^{m} \frac{(m-j)^n}{j}.$$

Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, Corollary 1,
equation (11).
-/
public theorem sum_bernoulli_harmonic_power_identity (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) :
    (∑ j ∈ Finset.Icc 1 n,
      ((n.choose j : ℚ) - 1) * (bernoulli j / (j : ℚ)) * (m : ℚ) ^ (n - j)) =
      (m : ℚ) ^ n * (harmonic m - harmonic n) -
        ∑ j ∈ Finset.Icc 1 m, ((m - j : ℕ) : ℚ) ^ n / (j : ℚ) := by
  have hA := lhs_eq_sum_descFactorial n m
  have hB := sum_descFactorial_eq n m
  linear_combination hA + hB

end MetaMathlibExt
