/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.ContinuedFractions.Computation.Approximations
public import Mathlib.Algebra.ContinuedFractions.Computation.Basic
public import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
public import Mathlib.Algebra.ContinuedFractions.Determinant
public import Mathlib.NumberTheory.Real.Irrational

/-!
# Alternating series with a two-step continued fraction pattern

The convergent denominators of the continued fraction of an irrational number
are positive integers, and the determinant formula for consecutive convergents
identifies the denominators of the terms of an alternating series whose partial
sums are those convergents. The divisibility and recurrence hypotheses then
force the even-indexed partial quotients after the first to be one, and the
odd-indexed ones to be multiples of the preceding convergent denominator.
-/

namespace MetaMathlibExt

namespace alternatingSeries_contFract_twoStepPattern

open GenContFract

private theorem notTerminated (x : ℝ) (hirr : Irrational x) (n : ℕ) :
    ¬ (GenContFract.of x).TerminatedAt n := by
  intro hterm
  have hterm2 : (GenContFract.of x).Terminates := ⟨n, hterm⟩
  rw [GenContFract.terminates_iff_rat] at hterm2
  obtain ⟨q, hq⟩ := hterm2
  exact hirr ⟨q, hq.symm⟩

private theorem stream_some (x : ℝ) (hirr : Irrational x) (n : ℕ) :
    ∃ gp, (GenContFract.of x).s.get? n = some gp :=
  Option.ne_none_iff_exists'.mp fun hnone =>
    notTerminated x hirr n (GenContFract.terminatedAt_iff_s_none.mpr hnone)

private theorem partDenNat (x : ℝ) (hirr : Irrational x) (n : ℕ) :
    ∃ k : ℕ, 1 ≤ k ∧ (GenContFract.of x).partDens.get? n = some (k : ℝ) := by
  obtain ⟨gp, hgp⟩ := stream_some x hirr n
  have hpd := GenContFract.partDen_eq_s_b hgp
  obtain ⟨z, hz⟩ := GenContFract.exists_int_eq_of_partDen hpd
  have h1 : (1 : ℝ) ≤ gp.b := GenContFract.of_one_le_get?_partDen hpd
  rw [hz] at h1
  have hz0 : 0 ≤ z := by exact_mod_cast (zero_le_one.trans h1)
  have hz1 : (1 : ℤ) ≤ z := by exact_mod_cast h1
  have htn : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
  have hcast : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by exact_mod_cast htn
  refine ⟨z.toNat, by omega, ?_⟩
  rw [hpd, hz, hcast]

private theorem denNat (x : ℝ) (hirr : Irrational x) (n : ℕ) :
    ∃ k : ℕ, 0 < k ∧ (GenContFract.of x).dens n = (k : ℝ) := by
  have hA := partDenNat x hirr
  induction n using Nat.twoStepInduction with
  | zero => exact ⟨1, one_pos, by simp⟩
  | one =>
    obtain ⟨gp, hgp⟩ := stream_some x hirr 0
    obtain ⟨k, _, hkeq⟩ := hA 0
    have hpd := GenContFract.partDen_eq_s_b hgp
    refine ⟨k, by omega, ?_⟩
    rw [GenContFract.first_den_eq hgp]
    exact Option.some.inj (hpd.symm.trans hkeq)
  | more n ih0 ih1 =>
    obtain ⟨k0, hk0, h0⟩ := ih0
    obtain ⟨k1, hk1, h1⟩ := ih1
    obtain ⟨gp, hgp⟩ := stream_some x hirr (n + 1)
    obtain ⟨a, _, haeq⟩ := hA (n + 1)
    have ha1 : gp.a = 1 :=
      GenContFract.of_partNum_eq_one (GenContFract.partNum_eq_s_a hgp)
    have hpd := GenContFract.partDen_eq_s_b hgp
    have hb : gp.b = (a : ℝ) := Option.some.inj (hpd.symm.trans haeq)
    refine ⟨a * k1 + k0, by positivity, ?_⟩
    rw [GenContFract.dens_recurrence hgp h0 h1, ha1, hb]
    push_cast
    ring

private theorem numInt (x : ℝ) (hirr : Irrational x) (n : ℕ) :
    ∃ z : ℤ, (GenContFract.of x).nums n = (z : ℝ) := by
  have hA : ∀ n, ∃ z : ℤ, (GenContFract.of x).partDens.get? n = some (z : ℝ) := by
    intro n
    obtain ⟨gp, hgp⟩ := stream_some x hirr n
    obtain ⟨z, hz⟩ :=
      GenContFract.exists_int_eq_of_partDen (GenContFract.partDen_eq_s_b hgp)
    exact ⟨z, (GenContFract.partDen_eq_s_b hgp).trans (congrArg some hz)⟩
  induction n using Nat.twoStepInduction with
  | zero =>
    exact ⟨⌊x⌋, by
      rw [GenContFract.num_eq_conts_a, GenContFract.nth_cont_eq_succ_nth_contAux]
      rfl⟩
  | one =>
    obtain ⟨gp, hgp⟩ := stream_some x hirr 0
    obtain ⟨z, hz⟩ := hA 0
    have hpd := GenContFract.partDen_eq_s_b hgp
    have hb : gp.b = (z : ℝ) := Option.some.inj (hpd.symm.trans hz)
    have ha1 : gp.a = 1 :=
      GenContFract.of_partNum_eq_one (GenContFract.partNum_eq_s_a hgp)
    refine ⟨z * ⌊x⌋ + 1, ?_⟩
    rw [GenContFract.first_num_eq hgp, ha1, hb, GenContFract.of_h_eq_floor]
    push_cast
    ring
  | more n ih0 ih1 =>
    obtain ⟨z0, h0⟩ := ih0
    obtain ⟨z1, h1⟩ := ih1
    obtain ⟨gp, hgp⟩ := stream_some x hirr (n + 1)
    obtain ⟨z, hz⟩ := hA (n + 1)
    have hpd := GenContFract.partDen_eq_s_b hgp
    have hb : gp.b = (z : ℝ) := Option.some.inj (hpd.symm.trans hz)
    have ha1 : gp.a = 1 :=
      GenContFract.of_partNum_eq_one (GenContFract.partNum_eq_s_a hgp)
    refine ⟨z * z1 + z0, ?_⟩
    rw [GenContFract.nums_recurrence hgp h0 h1, ha1, hb]
    push_cast
    ring

end alternatingSeries_contFract_twoStepPattern

set_option linter.unusedVariables false in
/-- **Alternating series with a two-step continued fraction pattern.** Let $(u_i)_{i \ge 0}$ be
positive integers with $u_0 = 1$, and let $x$ be an irrational real number with
$\sum_{i \ge 0} (-1)^i / u_i = x$. Write $x = [a_0; a_1, a_2, \dots]$ for its continued fraction
expansion and $p_n / q_n = [a_0; a_1, \dots, a_n]$ for its convergents, with $q_0 = 1$ and
$q_1 = a_1$. Suppose that for every $n \ge 0$ we have
$\sum_{i=0}^{n} (-1)^i / u_i = p_{n+1} / q_{n+1}$, $u_{2n+1} \mid u_{2n+2}$ and
$u_{2n+3} = \bigl(\prod_{j=0}^{n} u_{2j+2} / u_{2j+1}\bigr)^2 + u_{2n+2}$. Then
(i) $u_n = q_n q_{n+1}$ for every $n \ge 0$, (ii) for every $n \ge 0$ there is a natural number
$m$ with $a_{2n+3} = m \, q_{2n+1}$, and (iii) $a_{2n+2} = 1$ for every $n \ge 1$.

Part (iii) is stated only for $n \ge 1$, because it can fail at $n = 0$: the continued fraction
$[0; 1, 2, 1, 1, 4, 1, 32, 1, 1280, \dots]$, continued by $a_{2n+4} = 1$ and
$a_{2n+3} = q_{2n+1}$, with $u_n = q_n q_{n+1}$ (here $q = 1, 1, 3, 4, 7, 32, 39, 1280, \dots$)
satisfies every hypothesis and has $a_2 = 2$.

Source: Khalil Ayadi, Chiheb Ben Bechir, and Maher Saadaoui, *Continued Fractions with
Predictable Patterns and Transcendental Numbers*, Journal of Integer Sequences 28 (2025),
Article 25.1.4, Theorem 4 (`jis-2025-25.1.4-thm-4`). -/
public theorem alternatingSeries_contFract_twoStepPattern (x : ℝ) (hirr : Irrational x)
    (u : ℕ → ℕ) (hu : ∀ i, 0 < u i) (hu₀ : u 0 = 1)
    (hsum : HasSum (fun i : ℕ => (-1 : ℝ) ^ i / u i) x)
    (hconv : ∀ n : ℕ, ∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ i / u i =
      (GenContFract.of x).nums (n + 1) / (GenContFract.of x).dens (n + 1))
    (hdvd : ∀ n : ℕ, u (2 * n + 1) ∣ u (2 * n + 2))
    (hrec : ∀ n : ℕ, (u (2 * n + 3) : ℚ) =
      (∏ j ∈ Finset.range (n + 1), (u (2 * j + 2) : ℚ) / u (2 * j + 1)) ^ 2 + u (2 * n + 2)) :
    (∀ n : ℕ, (u n : ℝ) = (GenContFract.of x).dens n * (GenContFract.of x).dens (n + 1)) ∧
      (∀ n : ℕ, ∃ m : ℕ, (GenContFract.of x).partDens.get? (2 * n + 2) =
        some ((GenContFract.of x).dens (2 * n + 1) * m)) ∧
      ∀ n : ℕ, 1 ≤ n → (GenContFract.of x).partDens.get? (2 * n + 1) = some 1 := by
  have hnot := alternatingSeries_contFract_twoStepPattern.notTerminated x hirr
  have hstream := alternatingSeries_contFract_twoStepPattern.stream_some x hirr
  choose Q hQ using alternatingSeries_contFract_twoStepPattern.denNat x hirr
  have hQpos : ∀ n, 0 < Q n := fun n => (hQ n).1
  have hQeq : ∀ n, (GenContFract.of x).dens n = (Q n : ℝ) := fun n => (hQ n).2
  choose A hA using alternatingSeries_contFract_twoStepPattern.partDenNat x hirr
  have hApos : ∀ n, 1 ≤ A n := fun n => (hA n).1
  have hAeq : ∀ n, (GenContFract.of x).partDens.get? n = some (A n : ℝ) :=
    fun n => (hA n).2
  choose P hP using alternatingSeries_contFract_twoStepPattern.numInt x hirr
  have hQ0 : Q 0 = 1 := by
    have h := hQeq 0
    rw [GenContFract.zeroth_den_eq_one] at h
    exact_mod_cast h.symm
  have hQposR : ∀ n, (0 : ℝ) < (Q n : ℝ) := fun n => by exact_mod_cast hQpos n
  have hQmono : ∀ n, Q n ≤ Q (n + 1) := by
    intro n
    have h := GenContFract.of_den_mono (v := x) (n := n)
    rw [hQeq n, hQeq (n + 1)] at h
    exact_mod_cast h
  have hQle : ∀ m n, m ≤ n → Q m ≤ Q n := fun _ _ h => monotone_nat_of_le_succ hQmono h
  -- The denominator recurrence, in natural numbers.
  have hdenRecNat : ∀ n, Q (n + 2) = A (n + 1) * Q (n + 1) + Q n := by
    intro n
    obtain ⟨gp, hgp⟩ := hstream (n + 1)
    have ha1 : gp.a = 1 :=
      GenContFract.of_partNum_eq_one (GenContFract.partNum_eq_s_a hgp)
    have hpd := GenContFract.partDen_eq_s_b hgp
    have hb : gp.b = (A (n + 1) : ℝ) :=
      Option.some.inj (hpd.symm.trans (hAeq (n + 1)))
    have hR : ((Q (n + 2) : ℕ) : ℝ) =
        (A (n + 1) : ℝ) * (Q (n + 1) : ℝ) + (Q n : ℝ) := by
      rw [← hQeq (n + 2), ← hQeq (n + 1), ← hQeq n,
        GenContFract.dens_recurrence hgp rfl rfl, hb, ha1, one_mul]
    exact_mod_cast hR
  -- The determinant formula, in integers.
  have hdetInt : ∀ n, P n * (Q (n + 1) : ℤ) - (Q n : ℤ) * P (n + 1) =
      (-1 : ℤ) ^ (n + 1) := by
    intro n
    have hdet := (SimpContFract.of x).determinant (hnot n)
    change (GenContFract.of x).nums n * (GenContFract.of x).dens (n + 1) -
        (GenContFract.of x).dens n * (GenContFract.of x).nums (n + 1) =
        (-1 : ℝ) ^ (n + 1) at hdet
    rw [hP n, hP (n + 1), hQeq n, hQeq (n + 1)] at hdet
    exact_mod_cast hdet
  have hdetR : ∀ n, (GenContFract.of x).nums n * (GenContFract.of x).dens (n + 1) -
      (GenContFract.of x).dens n * (GenContFract.of x).nums (n + 1) =
      (-1 : ℝ) ^ (n + 1) := by
    intro n
    have hdet := (SimpContFract.of x).determinant (hnot n)
    change (GenContFract.of x).nums n * (GenContFract.of x).dens (n + 1) -
        (GenContFract.of x).dens n * (GenContFract.of x).nums (n + 1) =
        (-1 : ℝ) ^ (n + 1) at hdet
    exact hdet
  -- Consecutive denominators are coprime.
  have hcoprime : ∀ n, Nat.Coprime (Q n) (Q (n + 1)) := by
    intro n
    have hdet := hdetInt n
    have hdvd : (Nat.gcd (Q n) (Q (n + 1)) : ℤ) ∣ (-1 : ℤ) ^ (n + 1) := by
      have hleft : (Nat.gcd (Q n) (Q (n + 1)) : ℤ) ∣ (Q n : ℤ) :=
        Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)
      have hright : (Nat.gcd (Q n) (Q (n + 1)) : ℤ) ∣ (Q (n + 1) : ℤ) :=
        Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)
      rw [← hdet]
      exact dvd_sub (dvd_mul_of_dvd_right hright _) (dvd_mul_of_dvd_left hleft _)
    have hone : (Nat.gcd (Q n) (Q (n + 1)) : ℤ) ∣ (1 : ℤ) := by
      rcases neg_one_pow_eq_or (R := ℤ) (n + 1) with h | h <;> rw [h] at hdvd
      · exact hdvd
      · exact dvd_neg.mp hdvd
    have honeN : Nat.gcd (Q n) (Q (n + 1)) ∣ 1 := by exact_mod_cast hone
    exact Nat.dvd_one.mp honeN
  -- The first denominator is one, from the first partial sum.
  have hQ1 : Q 1 = 1 := by
    obtain ⟨gp, hgp⟩ := hstream 0
    have ha1 : gp.a = 1 :=
      GenContFract.of_partNum_eq_one (GenContFract.partNum_eq_s_a hgp)
    have hpd := GenContFract.partDen_eq_s_b hgp
    have hb : gp.b = (A 0 : ℝ) := Option.some.inj (hpd.symm.trans (hAeq 0))
    have hQ1A : Q 1 = A 0 := by
      have h := hQeq 1
      rw [GenContFract.first_den_eq hgp, hb] at h
      exact_mod_cast h.symm
    have hP1 : P 1 = (A 0 : ℤ) * ⌊x⌋ + 1 := by
      have hR : (P 1 : ℝ) = (A 0 : ℝ) * (⌊x⌋ : ℝ) + 1 := by
        rw [← hP 1, GenContFract.first_num_eq hgp, ha1, hb,
          GenContFract.of_h_eq_floor]
      exact_mod_cast hR
    have hS0 : (GenContFract.of x).nums 1 / (GenContFract.of x).dens 1 = 1 := by
      have h := hconv 0
      simp [hu₀] at h
      exact h.symm
    have hPQ : P 1 = (Q 1 : ℤ) := by
      rw [hP 1, hQeq 1] at hS0
      have hne : ((Q 1 : ℕ) : ℝ) ≠ 0 := (hQposR 1).ne'
      rw [div_eq_one_iff_eq hne] at hS0
      exact_mod_cast hS0
    have hdvd1 : (A 0 : ℤ) ∣ 1 := ⟨1 - ⌊x⌋, by
      rw [hQ1A] at hPQ; rw [mul_sub, mul_one]; linarith [hP1, hPQ]⟩
    have hdvd1N : A 0 ∣ 1 := by exact_mod_cast hdvd1
    rw [hQ1A]
    exact Nat.dvd_one.mp hdvd1N
  -- The product formula for `u`, as reals.
  have huR : ∀ n, (u n : ℝ) = (Q n : ℝ) * (Q (n + 1) : ℝ) := by
    intro n
    cases n with
    | zero =>
      rw [hu₀, hQ0, hQ1]
      simp
    | succ k =>
      have hq1ne : (GenContFract.of x).dens (k + 1) ≠ 0 := by
        rw [hQeq]; exact (hQposR _).ne'
      have hq2ne : (GenContFract.of x).dens (k + 2) ≠ 0 := by
        rw [hQeq]; exact (hQposR _).ne'
      have hsum1 := hconv (k + 1)
      have hsum0 := hconv k
      rw [Finset.sum_range_succ] at hsum1
      rw [hsum0] at hsum1
      have e : k + 1 + 1 = k + 2 := by omega
      rw [e] at hsum1
      have hF : (-1 : ℝ) ^ (k + 1) / (u (k + 1)) =
          (GenContFract.of x).nums (k + 2) / (GenContFract.of x).dens (k + 2) -
            (GenContFract.of x).nums (k + 1) / (GenContFract.of x).dens (k + 1) := by
        linarith [hsum1]
      have hnum : (GenContFract.of x).nums (k + 2) * (GenContFract.of x).dens (k + 1) -
          (GenContFract.of x).nums (k + 1) * (GenContFract.of x).dens (k + 2) =
          (-1 : ℝ) ^ (k + 1) := by
        have hdet := hdetR (k + 1)
        have hpow : (-1 : ℝ) ^ (k + 2) = -(-1 : ℝ) ^ (k + 1) := by
          rw [pow_succ]; ring
        rw [hpow] at hdet
        linarith [hdet]
      have hRHS : (GenContFract.of x).nums (k + 2) / (GenContFract.of x).dens (k + 2) -
          (GenContFract.of x).nums (k + 1) / (GenContFract.of x).dens (k + 1) =
          (-1 : ℝ) ^ (k + 1) /
            ((GenContFract.of x).dens (k + 1) * (GenContFract.of x).dens (k + 2)) := by
        rw [div_sub_div _ _ hq2ne hq1ne,
          mul_comm ((GenContFract.of x).dens (k + 2)) ((GenContFract.of x).nums (k + 1)), hnum,
          mul_comm ((GenContFract.of x).dens (k + 2)) ((GenContFract.of x).dens (k + 1))]
      have hdiff : (-1 : ℝ) ^ (k + 1) / (u (k + 1)) =
          (-1 : ℝ) ^ (k + 1) /
            ((GenContFract.of x).dens (k + 1) * (GenContFract.of x).dens (k + 2)) :=
        hF.trans hRHS
      have hune : ((u (k + 1) : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (hu (k + 1)).ne'
      have hprodne : (GenContFract.of x).dens (k + 1) * (GenContFract.of x).dens (k + 2) ≠ 0 :=
        mul_ne_zero hq1ne hq2ne
      have hcancel := (div_eq_div_iff hune hprodne).mp hdiff
      have hpowne : (-1 : ℝ) ^ (k + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
      have hEq := mul_left_cancel₀ hpowne hcancel
      rw [hQeq (k + 1), hQeq (k + 2)] at hEq
      change (u (k + 1) : ℝ) = (Q (k + 1) : ℝ) * (Q (k + 2) : ℝ)
      exact hEq.symm
  have huQNat : ∀ n, u n = Q n * Q (n + 1) := by
    intro n
    have h := huR n
    exact_mod_cast h
  have hprod : ∀ n : ℕ, (u n : ℝ) =
      (GenContFract.of x).dens n * (GenContFract.of x).dens (n + 1) := by
    intro n
    rw [huR n, hQeq n, hQeq (n + 1)]
  -- The telescoping product in the recurrence.
  have hprodReal : ∀ n, ∏ j ∈ Finset.range (n + 1),
      (u (2 * j + 2) : ℝ) / (u (2 * j + 1) : ℝ) = (Q (2 * n + 3) : ℝ) := by
    intro n
    induction n with
    | zero =>
      have hne : (Q 2 : ℝ) ≠ 0 := (hQposR 2).ne'
      rw [Finset.prod_range_one]
      norm_num only [Nat.reduceMul, Nat.reduceAdd]
      rw [huR 2, huR 1, hQ1]
      norm_num only [Nat.reduceAdd, Nat.cast_one, one_mul]
      exact mul_div_cancel_left₀ _ hne
    | succ n ih =>
      have e3 : 2 * (n + 1) + 3 = 2 * n + 5 := by ring
      rw [Finset.prod_range_succ, ih, e3]
      have hratio : (u (2 * (n + 1) + 2) : ℝ) / (u (2 * (n + 1) + 1) : ℝ) =
          (Q (2 * n + 5) : ℝ) / (Q (2 * n + 3) : ℝ) := by
        have e1 : 2 * (n + 1) + 2 = 2 * n + 4 := by ring
        have e2 : 2 * (n + 1) + 1 = 2 * n + 3 := by ring
        rw [e1, e2, huR (2 * n + 4), huR (2 * n + 3)]
        have e4 : 2 * n + 3 + 1 = 2 * n + 4 := by ring
        have e5 : 2 * n + 4 + 1 = 2 * n + 5 := by ring
        rw [e4, e5, mul_comm ((Q (2 * n + 3) : ℝ)) ((Q (2 * n + 4) : ℝ))]
        exact mul_div_mul_left _ _ (hQposR (2 * n + 4)).ne'
      rw [hratio, ← mul_div_assoc, mul_div_cancel_left₀ _ (hQposR (2 * n + 3)).ne']
  have hrecR : ∀ n, (u (2 * n + 3) : ℝ) =
      (∏ j ∈ Finset.range (n + 1), (u (2 * j + 2) : ℝ) / (u (2 * j + 1) : ℝ)) ^ 2 +
        (u (2 * n + 2) : ℝ) := by
    intro n
    have h := hrec n
    have h2 := congrArg (fun q : ℚ => (q : ℝ)) h
    push_cast at h2
    exact h2
  have hQ4 : ∀ n, Q (2 * n + 4) = Q (2 * n + 3) + Q (2 * n + 2) := by
    intro n
    have h := hrecR n
    rw [hprodReal n, huR (2 * n + 3), huR (2 * n + 2)] at h
    have e : 2 * n + 3 + 1 = 2 * n + 4 := by ring
    rw [e] at h
    have hR : ((Q (2 * n + 4) : ℕ) : ℝ) =
        (Q (2 * n + 3) : ℝ) + (Q (2 * n + 2) : ℝ) := by
      apply mul_left_cancel₀ (hQposR (2 * n + 3)).ne'
      calc ((Q (2 * n + 3) : ℕ) : ℝ) * (Q (2 * n + 4) : ℝ)
          = (Q (2 * n + 3) : ℝ) ^ 2 + (Q (2 * n + 2) : ℝ) * (Q (2 * n + 3) : ℝ) := h
        _ = (Q (2 * n + 3) : ℝ) * ((Q (2 * n + 3) : ℝ) + (Q (2 * n + 2) : ℝ)) := by ring
    exact_mod_cast hR
  have hA3 : ∀ n, A (2 * n + 3) = 1 := by
    intro n
    have hrecN := hdenRecNat (2 * n + 2)
    have e1 : 2 * n + 2 + 2 = 2 * n + 4 := by ring
    have e2 : 2 * n + 2 + 1 = 2 * n + 3 := by ring
    rw [e1, e2] at hrecN
    have h4 := hQ4 n
    have hEqN : A (2 * n + 3) * Q (2 * n + 3) = Q (2 * n + 3) := by omega
    have hR : ((A (2 * n + 3) : ℕ) : ℝ) * (Q (2 * n + 3) : ℝ) =
        1 * (Q (2 * n + 3) : ℝ) := by rw [one_mul]; exact_mod_cast hEqN
    have h := mul_right_cancel₀ (hQposR (2 * n + 3)).ne' hR
    exact_mod_cast h
  refine ⟨hprod, ?_, ?_⟩
  · intro n
    have hdiv : Q (2 * n + 1) ∣ Q (2 * n + 3) := by
      have h := hdvd n
      rw [huQNat (2 * n + 1), huQNat (2 * n + 2)] at h
      have e : 2 * n + 2 + 1 = 2 * n + 3 := by ring
      rw [e, mul_comm (Q (2 * n + 1)) (Q (2 * n + 2))] at h
      exact (Nat.mul_dvd_mul_iff_left (hQpos _)).mp h
    obtain ⟨t, ht⟩ := hdiv
    have htpos : 1 ≤ t := by
      rcases t with _ | s
      · rw [Nat.mul_zero] at ht
        exact absurd ht (hQpos _).ne'
      · omega
    obtain ⟨s, hs⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    rw [hs] at ht
    have hrecN := hdenRecNat (2 * n + 1)
    have e1 : 2 * n + 1 + 2 = 2 * n + 3 := by ring
    have e2 : 2 * n + 1 + 1 = 2 * n + 2 := by ring
    rw [e1, e2] at hrecN
    have hAeqN : A (2 * n + 2) * Q (2 * n + 2) = Q (2 * n + 1) * s := by
      rw [mul_add, mul_one] at ht
      omega
    have hdvdA : Q (2 * n + 1) ∣ A (2 * n + 2) := by
      apply (hcoprime (2 * n + 1)).dvd_of_dvd_mul_left
      rw [show 2 * n + 1 + 1 = 2 * n + 2 from by ring,
        mul_comm (Q (2 * n + 2)) (A (2 * n + 2))]
      exact ⟨s, hAeqN⟩
    obtain ⟨m, hm⟩ := hdvdA
    refine ⟨m, ?_⟩
    rw [hAeq (2 * n + 2), hQeq (2 * n + 1), hm]
    simp only [Nat.cast_mul]
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have e : 2 * (m + 1) + 1 = 2 * m + 3 := by ring
    rw [e, hAeq (2 * m + 3), hA3 m]
    simp

end MetaMathlibExt
