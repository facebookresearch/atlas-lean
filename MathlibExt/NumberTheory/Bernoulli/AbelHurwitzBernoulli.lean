/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

section
namespace MetaMathlibExt

open scoped BigOperators

-- Step 0: factorial ratio equals rising factorial, over ℚ.
private lemma factorial_div_eq_ascFactorial (m l : ℕ) (hm : 2 ≤ m) :
    ((Nat.factorial (m + l - 2) : ℚ) / (Nat.factorial (m - 2) : ℚ)) =
      ((Nat.ascFactorial (m - 1) l : ℕ) : ℚ) := by
  have h1 : m - 2 + 1 = m - 1 := by omega
  have h2 : m - 2 + l = m + l - 2 := by omega
  have h3 := Nat.factorial_mul_ascFactorial (m - 2) l
  rw [h1, h2] at h3
  have h3Q : ((Nat.factorial (m - 2) : ℚ)) * ((Nat.ascFactorial (m - 1) l : ℕ) : ℚ)
      = ((Nat.factorial (m + l - 2) : ℕ) : ℚ) := by
    exact_mod_cast h3
  have hne : (Nat.factorial (m - 2) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  linarith [h3Q]

-- Step 1: the filtered piFinset equals the piAntidiag.
private lemma filter_piFinset_eq_piAntidiag (m n : ℕ) :
    (Fintype.piFinset (fun _ : Fin m => Finset.range (n + 1))).filter
      (fun l => ∑ i, l i = n) = Finset.univ.piAntidiag n := by
  ext f
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_piAntidiag]
  constructor
  · rintro ⟨hmem, hsum⟩
    refine ⟨hsum, ?_⟩
    intro i _
    exact Finset.mem_univ i
  · rintro ⟨hsum, -⟩
    refine ⟨?_, hsum⟩
    intro i
    simp only [Finset.mem_range]
    have hi : f i ≤ ∑ j, f j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [hsum] at hi
    omega

-- Step 3 key Nat identity: (k+1)^(j+1) = (j+1) * (k+1)^(j) + k^(j+1).
private lemma asc_key (k j : ℕ) :
    (k + 1).ascFactorial (j + 1)
      = (j + 1) * (k + 1).ascFactorial j + k.ascFactorial (j + 1) := by
  rw [Nat.ascFactorial_succ, Nat.ascFactorial_succ]
  have e3 := Nat.succ_ascFactorial k j
  have hr : (k + 1 + j) * (k + 1).ascFactorial j
      = (j + 1) * (k + 1).ascFactorial j + k * (k + 1).ascFactorial j := by ring
  rw [hr, e3]

-- Step 3 divided form over ℚ, by induction on j.
private lemma asc_div_sum (k : ℕ) (j : ℕ) :
    ∑ l ∈ Finset.range (j + 1),
        ((Nat.ascFactorial k l : ℕ) : ℚ) / ((Nat.factorial l : ℕ) : ℚ)
      = ((Nat.ascFactorial (k + 1) j : ℕ) : ℚ) / ((Nat.factorial j : ℕ) : ℚ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, ih]
    have hkey := asc_key k j
    have hkeyQ : ((Nat.ascFactorial (k + 1) (j + 1) : ℕ) : ℚ)
        = ((j + 1 : ℕ) : ℚ) * ((Nat.ascFactorial (k + 1) j : ℕ) : ℚ)
          + ((Nat.ascFactorial k (j + 1) : ℕ) : ℚ) := by
      exact_mod_cast hkey
    have hfact : Nat.factorial (j + 1) = (j + 1) * Nat.factorial j := Nat.factorial_succ j
    have hfactQ : ((Nat.factorial (j + 1) : ℕ) : ℚ)
        = ((j + 1 : ℕ) : ℚ) * ((Nat.factorial j : ℕ) : ℚ) := by
      exact_mod_cast hfact
    have hj1 : ((j + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    have hjF : ((Nat.factorial j : ℕ) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [hkeyQ, hfactQ]
    field_simp

-- Step 3 full form: ∑_{l ≤ j} C(j,l) k^(l) (j-l)! = (k+1)^(j) over ℚ.
private lemma asc_sum_mul (k j : ℕ) :
    ∑ l ∈ Finset.range (j + 1),
        ((Nat.choose j l : ℕ) : ℚ) * ((Nat.ascFactorial k l : ℕ) : ℚ)
          * ((Nat.factorial (j - l) : ℕ) : ℚ)
      = ((Nat.ascFactorial (k + 1) j : ℕ) : ℚ) := by
  have hdiv := asc_div_sum k j
  have hterm : ∀ l ∈ Finset.range (j + 1),
      ((Nat.choose j l : ℕ) : ℚ) * ((Nat.ascFactorial k l : ℕ) : ℚ)
        * ((Nat.factorial (j - l) : ℕ) : ℚ)
      = ((Nat.factorial j : ℕ) : ℚ)
        * (((Nat.ascFactorial k l : ℕ) : ℚ) / ((Nat.factorial l : ℕ) : ℚ)) := by
    intro l hl
    have hle : l ≤ j := by
      have := Finset.mem_range.mp hl
      omega
    have hcc := Nat.choose_mul_factorial_mul_factorial hle
    have hccQ : ((Nat.choose j l : ℕ) : ℚ) * ((Nat.factorial l : ℕ) : ℚ)
          * ((Nat.factorial (j - l) : ℕ) : ℚ) = ((Nat.factorial j : ℕ) : ℚ) := by
      exact_mod_cast hcc
    have hlF : ((Nat.factorial l : ℕ) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
    linear_combination ((Nat.ascFactorial k l : ℕ) : ℚ) * hccQ
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hdiv]
  field_simp

-- Step 2: the two polynomials whose equality encodes the Hurwitz identity.
private noncomputable def hurwitzP (u : ℚ) (N : ℕ) : Polynomial ℚ :=
  ∑ a ∈ Finset.range (N + 1),
    Polynomial.C (((Nat.choose N a : ℕ) : ℚ) * (u + (a : ℚ)) ^ a) *
      ((Polynomial.X - Polynomial.C (a : ℚ)) ^ (N - a))

private noncomputable def hurwitzQ (u : ℚ) (N : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (N + 1),
    Polynomial.C (((Nat.choose N i : ℕ) : ℚ) * ((Nat.factorial i : ℕ) : ℚ)) *
      ((Polynomial.X + Polynomial.C u) ^ (N - i))

-- Derivative of each summand of P.
private lemma deriv_hurwitzP_term (u : ℚ) (N a : ℕ) (ha : a ≤ N) :
    Polynomial.derivative
        (Polynomial.C (((Nat.choose (N + 1) a : ℕ) : ℚ) * (u + (a : ℚ)) ^ a) *
          ((Polynomial.X - Polynomial.C (a : ℚ)) ^ (N + 1 - a)))
      = Polynomial.C (((N + 1 : ℕ) : ℚ)) *
        (Polynomial.C (((Nat.choose N a : ℕ) : ℚ) * (u + (a : ℚ)) ^ a) *
          ((Polynomial.X - Polynomial.C (a : ℚ)) ^ (N - a))) := by
  rw [Polynomial.derivative_C_mul, Polynomial.derivative_X_sub_C_pow]
  have hchoose := Nat.choose_mul_succ_eq N a
  have hexp : N + 1 - a - 1 = N - a := by omega
  rw [hexp]
  have hcast : (((Nat.choose (N + 1) a : ℕ) : ℚ)) * (((N + 1 - a : ℕ)) : ℚ)
      = ((N + 1 : ℕ) : ℚ) * (((Nat.choose N a : ℕ) : ℚ)) := by
    have h2 : (((Nat.choose (N + 1) a : ℕ) : ℚ)) * (((N + 1 - a : ℕ)) : ℚ)
        = (((Nat.choose N a : ℕ) : ℚ)) * (((N + 1 : ℕ)) : ℚ) := by
      exact_mod_cast hchoose.symm
    rw [h2]; ring
  have hC : Polynomial.C (((Nat.choose (N + 1) a : ℕ) : ℚ) * (u + (a : ℚ)) ^ a)
        * (Polynomial.C (((N + 1 - a : ℕ)) : ℚ))
      = Polynomial.C (((N + 1 : ℕ) : ℚ)) *
        Polynomial.C (((Nat.choose N a : ℕ) : ℚ) * (u + (a : ℚ)) ^ a) := by
    rw [← Polynomial.C_mul, ← Polynomial.C_mul]
    congr 1
    linear_combination ((u + (a : ℚ)) ^ a) * hcast
  have hrw : Polynomial.C (((Nat.choose (N + 1) a : ℕ) : ℚ) * (u + (a : ℚ)) ^ a)
        * (Polynomial.C (((N + 1 - a : ℕ)) : ℚ) *
          ((Polynomial.X - Polynomial.C (a : ℚ)) ^ (N - a)))
      = (Polynomial.C (((Nat.choose (N + 1) a : ℕ) : ℚ) * (u + (a : ℚ)) ^ a)
        * (Polynomial.C (((N + 1 - a : ℕ)) : ℚ))) *
          ((Polynomial.X - Polynomial.C (a : ℚ)) ^ (N - a)) := by ring
  rw [hrw, hC]
  ring

-- Derivative of each summand of Q.
private lemma deriv_hurwitzQ_term (u : ℚ) (N i : ℕ) (hi : i ≤ N) :
    Polynomial.derivative
        (Polynomial.C (((Nat.choose (N + 1) i : ℕ) : ℚ) * ((Nat.factorial i : ℕ) : ℚ)) *
          ((Polynomial.X + Polynomial.C u) ^ (N + 1 - i)))
      = Polynomial.C (((N + 1 : ℕ) : ℚ)) *
        (Polynomial.C (((Nat.choose N i : ℕ) : ℚ) * ((Nat.factorial i : ℕ) : ℚ)) *
          ((Polynomial.X + Polynomial.C u) ^ (N - i))) := by
  rw [Polynomial.derivative_C_mul, Polynomial.derivative_X_add_C_pow]
  have hchoose := Nat.choose_mul_succ_eq N i
  have hexp : N + 1 - i - 1 = N - i := by omega
  rw [hexp]
  have hcast : (((Nat.choose (N + 1) i : ℕ) : ℚ)) * (((N + 1 - i : ℕ)) : ℚ)
      = ((N + 1 : ℕ) : ℚ) * (((Nat.choose N i : ℕ) : ℚ)) := by
    have h2 : (((Nat.choose (N + 1) i : ℕ) : ℚ)) * (((N + 1 - i : ℕ)) : ℚ)
        = (((Nat.choose N i : ℕ) : ℚ)) * (((N + 1 : ℕ)) : ℚ) := by
      exact_mod_cast hchoose.symm
    rw [h2]; ring
  have hC : Polynomial.C (((Nat.choose (N + 1) i : ℕ) : ℚ) * ((Nat.factorial i : ℕ) : ℚ))
        * (Polynomial.C (((N + 1 - i : ℕ)) : ℚ))
      = Polynomial.C (((N + 1 : ℕ) : ℚ)) *
        Polynomial.C (((Nat.choose N i : ℕ) : ℚ) * ((Nat.factorial i : ℕ) : ℚ)) := by
    rw [← Polynomial.C_mul, ← Polynomial.C_mul]
    congr 1
    linear_combination ((Nat.factorial i : ℕ) : ℚ) * hcast
  have hrw : Polynomial.C (((Nat.choose (N + 1) i : ℕ) : ℚ) * ((Nat.factorial i : ℕ) : ℚ))
        * (Polynomial.C (((N + 1 - i : ℕ)) : ℚ) *
          ((Polynomial.X + Polynomial.C u) ^ (N - i)))
      = (Polynomial.C (((Nat.choose (N + 1) i : ℕ) : ℚ) * ((Nat.factorial i : ℕ) : ℚ))
        * (Polynomial.C (((N + 1 - i : ℕ)) : ℚ))) *
          ((Polynomial.X + Polynomial.C u) ^ (N - i)) := by ring
  rw [hrw, hC]
  ring

-- Full derivative laws, peeling off the top (constant) term.
private lemma deriv_hurwitzP (u : ℚ) (N : ℕ) :
    Polynomial.derivative (hurwitzP u (N + 1))
      = Polynomial.C (((N + 1 : ℕ) : ℚ)) * hurwitzP u N := by
  simp only [hurwitzP]
  rw [Polynomial.derivative_sum, Finset.sum_range_succ]
  have htop : Polynomial.derivative
        (Polynomial.C (((Nat.choose (N + 1) (N + 1) : ℕ) : ℚ) *
            (u + ((N + 1 : ℕ) : ℚ)) ^ (N + 1)) *
          ((Polynomial.X - Polynomial.C (((N + 1 : ℕ) : ℚ))) ^ (N + 1 - (N + 1))))
        = 0 := by
    have h0 : N + 1 - (N + 1) = 0 := by omega
    rw [h0, pow_zero, mul_one, Polynomial.derivative_C]
  rw [htop, add_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have ha' : a ≤ N := by
    have := Finset.mem_range.mp ha
    omega
  exact deriv_hurwitzP_term u N a ha'

private lemma deriv_hurwitzQ (u : ℚ) (N : ℕ) :
    Polynomial.derivative (hurwitzQ u (N + 1))
      = Polynomial.C (((N + 1 : ℕ) : ℚ)) * hurwitzQ u N := by
  simp only [hurwitzQ]
  rw [Polynomial.derivative_sum, Finset.sum_range_succ]
  have htop : Polynomial.derivative
        (Polynomial.C (((Nat.choose (N + 1) (N + 1) : ℕ) : ℚ) *
            ((Nat.factorial (N + 1) : ℕ) : ℚ)) *
          ((Polynomial.X + Polynomial.C u) ^ (N + 1 - (N + 1))))
        = 0 := by
    have h0 : N + 1 - (N + 1) = 0 := by omega
    rw [h0, pow_zero, mul_one, Polynomial.derivative_C]
  rw [htop, add_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ N := by
    have := Finset.mem_range.mp hi
    omega
  exact deriv_hurwitzQ_term u N i hi'

-- Eval of Q at Y = -u: only the i = N term survives, giving N!.
private lemma eval_neg_hurwitzQ (u : ℚ) (N : ℕ) :
    Polynomial.eval (-u) (hurwitzQ u N) = ((Nat.factorial N : ℕ) : ℚ) := by
  have hpush : ∀ i ∈ Finset.range (N + 1),
      Polynomial.eval (-u)
        (Polynomial.C (((Nat.choose N i : ℕ) : ℚ) * ((Nat.factorial i : ℕ) : ℚ)) *
          ((Polynomial.X + Polynomial.C u) ^ (N - i)))
      = (((Nat.choose N i : ℕ) : ℚ) * ((Nat.factorial i : ℕ) : ℚ)) * (-u + u) ^ (N - i) := by
    intro i _
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C]
  simp only [hurwitzQ, Polynomial.eval_finsetSum]
  rw [Finset.sum_congr rfl hpush, Finset.sum_eq_single N]
  · rw [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, pow_zero, mul_one]
  · intro i hi hne
    have hlt : i < N := by
      have hmem := Finset.mem_range.mp hi
      omega
    have hexp : N - i ≠ 0 := by omega
    rw [neg_add_cancel, zero_pow hexp, mul_zero]
  · intro hN
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self N)) hN

-- Eval of P at Y = -u, via the N-th forward difference of t^N.
private lemma eval_neg_hurwitzP (u : ℚ) (N : ℕ) :
    Polynomial.eval (-u) (hurwitzP u N) = ((Nat.factorial N : ℕ) : ℚ) := by
  have hpush : ∀ a ∈ Finset.range (N + 1),
      Polynomial.eval (-u)
        (Polynomial.C (((Nat.choose N a : ℕ) : ℚ) * (u + (a : ℚ)) ^ a) *
          ((Polynomial.X - Polynomial.C (a : ℚ)) ^ (N - a)))
      = (((-1 : ℚ) ^ (N - a) * ((Nat.choose N a : ℕ) : ℚ)) * (u + (a : ℚ)) ^ N) := by
    intro a ha
    have hle : a ≤ N := by
      have := Finset.mem_range.mp ha
      omega
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    have hneg : (-u - (a : ℚ)) ^ (N - a)
        = (-1) ^ (N - a) * (u + (a : ℚ)) ^ (N - a) := by
      have h1 : (-u - (a : ℚ)) = (-1) * (u + (a : ℚ)) := by ring
      rw [h1, mul_pow]
    rw [hneg]
    have hpow : (u + (a : ℚ)) ^ a * (u + (a : ℚ)) ^ (N - a) = (u + (a : ℚ)) ^ N := by
      rw [← pow_add, Nat.add_sub_cancel' hle]
    calc (((Nat.choose N a : ℕ) : ℚ) * (u + (a : ℚ)) ^ a)
            * ((-1) ^ (N - a) * (u + (a : ℚ)) ^ (N - a))
          = (((-1) ^ (N - a) * ((Nat.choose N a : ℕ) : ℚ)))
            * ((u + (a : ℚ)) ^ a * (u + (a : ℚ)) ^ (N - a)) := by ring
        _ = (((-1) ^ (N - a) * ((Nat.choose N a : ℕ) : ℚ))) * (u + (a : ℚ)) ^ N := by
            rw [hpow]
  have hshift := fwdDiff_iter_eq_sum_shift (1 : ℚ) (fun r : ℚ => r ^ N) N u
  simp only [nsmul_eq_mul, mul_one, zsmul_eq_mul] at hshift
  push_cast at hshift
  have hfact : ((fwdDiff (1 : ℚ))^[N] (fun r : ℚ => r ^ N)) u
      = ((Nat.factorial N : ℕ) : ℚ) := by
    have h := fwdDiff_iter_eq_factorial (R := ℚ) (n := N)
    have h2 := congrFun h u
    simpa using h2
  simp only [hurwitzP, Polynomial.eval_finsetSum]
  rw [Finset.sum_congr rfl hpush, ← hshift, hfact]

-- The two polynomials agree, by induction using the derivative laws.
private lemma hurwitz_poly_eq (u : ℚ) (N : ℕ) : hurwitzP u N = hurwitzQ u N := by
  induction N with
  | zero =>
    simp only [hurwitzP, hurwitzQ]
    rw [Finset.sum_range_one, Finset.sum_range_one]
    simp
  | succ N ih =>
    have hder : Polynomial.derivative (hurwitzP u (N + 1) - hurwitzQ u (N + 1)) = 0 := by
      rw [Polynomial.derivative_sub, deriv_hurwitzP, deriv_hurwitzQ, ih]
      ring
    have hC := Polynomial.eq_C_of_derivative_eq_zero hder
    have heval : Polynomial.eval (-u) (hurwitzP u (N + 1))
        = Polynomial.eval (-u) (hurwitzQ u (N + 1)) := by
      rw [eval_neg_hurwitzP, eval_neg_hurwitzQ]
    have h0 : Polynomial.eval (-u) (hurwitzP u (N + 1) - hurwitzQ u (N + 1)) = 0 := by
      rw [Polynomial.eval_sub, heval, sub_self]
    rw [hC] at h0
    simp only [Polynomial.eval_C] at h0
    have hzero : hurwitzP u (N + 1) - hurwitzQ u (N + 1) = 0 := by
      rw [hC, h0, Polynomial.C_0]
    exact sub_eq_zero.mp hzero

-- Step 2 numeric identity: evaluate the polynomial identity at Y.
private lemma hurwitz_id (u Y : ℚ) (N : ℕ) :
    ∑ a ∈ Finset.range (N + 1),
      (((Nat.choose N a : ℕ) : ℚ) * (u + (a : ℚ)) ^ a * (Y - (a : ℚ)) ^ (N - a))
    = ∑ i ∈ Finset.range (N + 1),
      (((Nat.choose N i : ℕ) : ℚ) * ((Nat.factorial i : ℕ) : ℚ) * (Y + u) ^ (N - i)) := by
  have h := congrArg (Polynomial.eval Y) (hurwitz_poly_eq u N)
  simp only [hurwitzP, hurwitzQ, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_X] at h
  exact h

-- Trinomial identity: C(n,a) C(n-a,l) = C(n,l) C(n-l,a).
private lemma choose_trinomial_swap (n a l : ℕ) :
    n.choose a * (n - a).choose l = n.choose l * (n - l).choose a := by
  by_cases ha : a ≤ n
  · by_cases hl : l ≤ n - a
    · have hsym : n.choose a = n.choose (n - a) := (Nat.choose_symm ha).symm
      have hmul := Nat.choose_mul (n := n) (k := n - a) (s := l) hl
      have hal : a ≤ n - l := by omega
      have hsub : n - a - l = n - l - a := by omega
      have hsub2 : n - a - l = (n - l) - a := by omega
      have hsym2 : (n - l).choose (n - a - l) = (n - l).choose a := by
        have hthis := Nat.choose_symm hal
        rw [← hsub2] at hthis
        exact hthis
      rw [hsym2] at hmul
      rw [← hsym] at hmul
      exact hmul
    · have hlt : n - a < l := by omega
      have h1 : (n - a).choose l = 0 := Nat.choose_eq_zero_of_lt hlt
      rw [h1, Nat.mul_zero]
      by_cases hln : l ≤ n
      · have h2 : n - l < a := by omega
        have h3 : (n - l).choose a = 0 := Nat.choose_eq_zero_of_lt h2
        rw [h3, Nat.mul_zero]
      · have hln' : n < l := by omega
        have h3 : n.choose l = 0 := Nat.choose_eq_zero_of_lt hln'
        rw [h3, Nat.zero_mul]
  · have ha' : n < a := by omega
    have h1 : n.choose a = 0 := Nat.choose_eq_zero_of_lt ha'
    have h2 : n - l ≤ n := Nat.sub_le n l
    have h3 : n - l < a := by omega
    have h4 : (n - l).choose a = 0 := Nat.choose_eq_zero_of_lt h3
    rw [h1, h4, Nat.zero_mul, Nat.mul_zero]

-- Trinomial reindex: C(n,l) C(n-l,i) = C(n,l+i) C(l+i,l).
private lemma choose_trinomial_reindex (n l i : ℕ) :
    n.choose l * (n - l).choose i = n.choose (l + i) * (l + i).choose l := by
  have hle : l ≤ l + i := Nat.le_add_right l i
  have h := Nat.choose_mul (n := n) (k := l + i) (s := l) hle
  have hsub : l + i - l = i := by omega
  rw [hsub] at h
  exact h.symm

-- Filter description of triangular ranges.
private lemma filter_range_add_le (n a : ℕ) (ha : a ≤ n) :
    (Finset.range (n + 1)).filter (fun l => a + l ≤ n) = Finset.range (n - a + 1) := by
  ext l
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

-- Triangle swap: double sums over a+l ≤ n commute.
private lemma sum_triangle_swap (n : ℕ) {M : Type*} [AddCommMonoid M]
    (f : ℕ → ℕ → M) :
    ∑ a ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n - a + 1), f a l
      = ∑ l ∈ Finset.range (n + 1), ∑ a ∈ Finset.range (n - l + 1), f a l := by
  have h1 : ∀ a ∈ Finset.range (n + 1),
      ∑ l ∈ Finset.range (n - a + 1), f a l
        = ∑ l ∈ Finset.range (n + 1), (if a + l ≤ n then f a l else 0) := by
    intro a ha
    have ham : a ≤ n := by
      have := Finset.mem_range.mp ha
      omega
    have hfilt := filter_range_add_le n a ham
    rw [← hfilt, Finset.sum_filter]
  have h2 : ∀ l ∈ Finset.range (n + 1),
      ∑ a ∈ Finset.range (n - l + 1), f a l
        = ∑ a ∈ Finset.range (n + 1), (if a + l ≤ n then f a l else 0) := by
    intro l hl
    have hlm : l ≤ n := by
      have := Finset.mem_range.mp hl
      omega
    have hfilt : (Finset.range (n + 1)).filter (fun a => a + l ≤ n)
        = Finset.range (n - l + 1) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [← hfilt, Finset.sum_filter]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_comm]

-- Triangle reindex: (l,i) with l+i ≤ n ↔ (j,l) with l ≤ j ≤ n, i = j-l.
private lemma sum_triangle_reindex (n : ℕ) {M : Type*} [AddCommMonoid M]
    (F : ℕ → ℕ → M) :
    ∑ l ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n - l + 1), F l i
      = ∑ j ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (j + 1), F l (j - l) := by
  induction n generalizing F with
  | zero =>
    simp
  | succ n ih =>
    have hLHS : ∑ l ∈ Finset.range (n + 1 + 1), ∑ i ∈ Finset.range (n + 1 - l + 1), F l i
        = (∑ l ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n - l + 1), F l i)
          + ∑ l ∈ Finset.range (n + 1 + 1), F l (n + 1 - l) := by
      rw [Finset.sum_range_succ]
      have hsplit : ∀ l ∈ Finset.range (n + 1),
          ∑ i ∈ Finset.range (n + 1 - l + 1), F l i
            = (∑ i ∈ Finset.range (n - l + 1), F l i) + F l (n + 1 - l) := by
        intro l hl
        have hlm : l ≤ n := by
          have := Finset.mem_range.mp hl
          omega
        have heq : n + 1 - l + 1 = (n - l + 1) + 1 := by omega
        have heq2 : n - l + 1 = n + 1 - l := by omega
        rw [heq, Finset.sum_range_succ, heq2]
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
      have htop : ∑ i ∈ Finset.range (n + 1 - (n + 1) + 1), F (n + 1) i
          = F (n + 1) (n + 1 - (n + 1)) := by
        have heq0 : n + 1 - (n + 1) + 1 = 1 := by omega
        rw [heq0]
        simp
      rw [htop]
      have hlast : ∑ l ∈ Finset.range (n + 1 + 1), F l (n + 1 - l)
          = (∑ l ∈ Finset.range (n + 1), F l (n + 1 - l)) + F (n + 1) (n + 1 - (n + 1)) := by
        rw [Finset.sum_range_succ]
      rw [hlast]
      abel
    have hRHS : ∑ j ∈ Finset.range (n + 1 + 1), ∑ l ∈ Finset.range (j + 1), F l (j - l)
        = (∑ j ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (j + 1), F l (j - l))
          + ∑ l ∈ Finset.range (n + 1 + 1), F l (n + 1 - l) := by
      rw [Finset.sum_range_succ]
    rw [hLHS, hRHS, ih]

-- Step 4 statement (full Hurwitz identity over ℚ for a nonempty index finset).
-- Base case: singleton.
private lemma hurwitz_singleton (ι : Type*) [DecidableEq ι] (a : ι) (y : ι → ℚ) (n : ℕ) :
    ∑ f ∈ ({a} : Finset ι).piAntidiag n,
      (((Nat.multinomial ({a} : Finset ι) f : ℕ)) : ℚ)
        * ∏ i ∈ ({a} : Finset ι), (y i + ((f i : ℕ) : ℚ)) ^ f i
    = ∑ l ∈ Finset.range (n + 1),
      (((Nat.choose n l : ℕ) : ℚ) * (((Nat.ascFactorial (({a} : Finset ι).card - 1) l : ℕ)) : ℚ)
        * ((∑ i ∈ ({a} : Finset ι), y i) + (n : ℚ)) ^ (n - l)) := by
  have hmem : ∀ f : ι → ℕ,
      f ∈ ({a} : Finset ι).piAntidiag n ↔ f = Function.update (0 : ι → ℕ) a n := by
    intro f
    constructor
    · intro hf
      rw [Finset.mem_piAntidiag] at hf
      obtain ⟨hsum, hsupp⟩ := hf
      have hfa : f a = n := by simpa using hsum
      funext j
      by_cases hj : j = a
      · subst hj
        rw [hfa]
        simp
      · have h0 : f j = 0 := by
          by_contra hne
          have hja := hsupp j hne
          rw [Finset.mem_singleton] at hja
          exact hj hja
        simp [h0, hj]
    · intro hf
      rw [hf, Finset.mem_piAntidiag]
      constructor
      · simp
      · intro i hi
        by_cases hi2 : i = a
        · rw [hi2]; exact Finset.mem_singleton_self a
        · simp [hi2] at hi
  have hset : ({a} : Finset ι).piAntidiag n = {Function.update (0 : ι → ℕ) a n} := by
    ext f
    rw [hmem, Finset.mem_singleton]
  rw [hset, Finset.sum_singleton]
  have hmult : Nat.multinomial ({a} : Finset ι) (Function.update (0 : ι → ℕ) a n) = 1 :=
    Nat.multinomial_singleton a _
  have hprod : ∏ i ∈ ({a} : Finset ι),
        (y i + (((Function.update (0 : ι → ℕ) a n i : ℕ)) : ℚ))
          ^ Function.update (0 : ι → ℕ) a n i
      = (y a + (n : ℚ)) ^ n := by
    rw [Finset.prod_singleton]
    simp
  rw [hmult, Nat.cast_one, one_mul, hprod, Finset.card_singleton, Finset.sum_singleton]
  rw [show (1 - 1 : ℕ) = 0 from rfl]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro l hl hne
    have hle : l ≤ n := by
      have := Finset.mem_range.mp hl
      omega
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
    rw [Nat.zero_ascFactorial]
    simp
  · intro h0
    exact absurd (Finset.mem_range.mpr (Nat.zero_lt_succ n)) h0

-- Step 4 (full): Hurwitz multinomial identity over ℚ, by finset induction.
-- Helper: term simplification for the cons step.
private lemma hurwitz_cons_term_eq (ι : Type*) [DecidableEq ι] (a : ι) (s : Finset ι)
    (h : a ∉ s) (y : ι → ℚ) (n pa pb : ℕ) (hpn : pa + pb = n)
    (g : ι → ℕ) (hg : g ∈ s.piAntidiag pb) :
    let d : ι → ℕ := fun t => if t = a then pa else 0
    let f := g + d
    (((Nat.multinomial (Finset.cons a s h) f : ℕ)) : ℚ)
        * ∏ i ∈ Finset.cons a s h, (y i + ((f i : ℕ) : ℚ)) ^ f i
      = ((((Nat.choose n pa : ℕ)) : ℚ) * (y a + (pa : ℚ)) ^ pa)
        * ((((Nat.multinomial s g : ℕ)) : ℚ)
          * ∏ i ∈ s, (y i + ((g i : ℕ) : ℚ)) ^ g i) := by
  intro d f
  have hgmem := Finset.mem_piAntidiag.mp hg
  obtain ⟨hsumg, hsuppg⟩ := hgmem
  have hga : g a = 0 := by
    by_contra hne
    exact h (hsuppg a hne)
  have hfa : f a = pa := by
    simp only [f, d, Pi.add_apply, hga]
    simp
  have hfg : ∀ t ∈ s, f t = g t := by
    intro t ht
    have hne : t ≠ a := ne_of_mem_of_not_mem ht h
    simp only [f, d, Pi.add_apply, hne, ite_false, Nat.add_zero]
  have hsumf : ∑ i ∈ s, f i = pb := by
    have hcongr : ∑ i ∈ s, f i = ∑ i ∈ s, g i :=
      Finset.sum_congr rfl (fun t ht => hfg t ht)
    rw [hcongr, hsumg]
  have hmult : Nat.multinomial (Finset.cons a s h) f
      = (f a + ∑ i ∈ s, f i).choose (f a) * Nat.multinomial s f :=
    Nat.multinomial_cons h f
  have hmultf : Nat.multinomial s f = Nat.multinomial s g :=
    Nat.multinomial_congr hfg
  have hchoose : (f a + ∑ i ∈ s, f i).choose (f a) = n.choose pa := by
    rw [hfa, hsumf, hpn]
  have hmultQ : ((Nat.multinomial (Finset.cons a s h) f : ℕ) : ℚ)
      = ((Nat.choose n pa : ℕ) : ℚ) * ((Nat.multinomial s g : ℕ) : ℚ) := by
    rw [hmult, hchoose, hmultf, Nat.cast_mul]
  have hprod : ∏ i ∈ Finset.cons a s h, (y i + ((f i : ℕ) : ℚ)) ^ f i
      = (y a + (pa : ℚ)) ^ pa * ∏ i ∈ s, (y i + ((g i : ℕ) : ℚ)) ^ g i := by
    rw [Finset.prod_cons h]
    have ha_eq : (y a + ((f a : ℕ) : ℚ)) ^ f a = (y a + (pa : ℚ)) ^ pa := by
      rw [hfa]
    rw [ha_eq]
    congr 1
    apply Finset.prod_congr rfl
    intro t ht
    rw [hfg t ht]
  rw [hmultQ, hprod]
  ring

-- ℚ cast of trinomial swap.
private lemma choose_trinomial_swap_Q (n a l : ℕ) :
    (((n.choose a : ℕ)) : ℚ) * (((n - a).choose l : ℕ) : ℚ)
      = (((n.choose l : ℕ)) : ℚ) * ((((n - l).choose a : ℕ)) : ℚ) := by
  exact_mod_cast choose_trinomial_swap n a l

-- ℚ cast of trinomial reindex.
private lemma choose_trinomial_reindex_Q (n l i : ℕ) :
    (((n.choose l : ℕ)) : ℚ) * ((((n - l).choose i : ℕ)) : ℚ)
      = (((n.choose (l + i) : ℕ)) : ℚ) * ((((l + i).choose l : ℕ)) : ℚ) := by
  exact_mod_cast choose_trinomial_reindex n l i

-- Swap-term equality for fixed a0, l with a0+l ≤ n.
private lemma swap_term_eq (n a0 l : ℕ) (S u : ℚ) (c : ℕ)
    (ha : a0 ≤ n) (hal : a0 + l ≤ n) :
    ((((Nat.choose n a0 : ℕ)) : ℚ) * (u + (a0 : ℚ)) ^ a0
      * ((((Nat.choose (n - a0) l : ℕ)) : ℚ)
        * (((Nat.ascFactorial (c - 1) l : ℕ)) : ℚ)
        * (S + ((n - a0 : ℕ) : ℚ)) ^ (n - a0 - l)))
    = (((Nat.choose n l : ℕ) : ℚ) * (((Nat.ascFactorial (c - 1) l : ℕ)) : ℚ))
      * ((((Nat.choose (n - l) a0 : ℕ)) : ℚ) * (u + (a0 : ℚ)) ^ a0
        * ((S + (n : ℚ)) - (a0 : ℚ)) ^ (n - l - a0)) := by
  have hC := choose_trinomial_swap_Q n a0 l
  have hexp : n - a0 - l = n - l - a0 := by omega
  have hcast : ((n - a0 : ℕ) : ℚ) = (n : ℚ) - (a0 : ℚ) := Nat.cast_sub ha
  have hbase : S + ((n - a0 : ℕ) : ℚ) = (S + (n : ℚ)) - (a0 : ℚ) := by
    rw [hcast]
    ring
  have hpow : (S + ((n - a0 : ℕ) : ℚ)) ^ (n - a0 - l)
      = ((S + (n : ℚ)) - (a0 : ℚ)) ^ (n - l - a0) := by
    rw [hexp, hbase]
  have hLHS : (((Nat.choose n a0 : ℕ) : ℚ) * (u + (a0 : ℚ)) ^ a0
        * (((Nat.choose (n - a0) l : ℕ) : ℚ)
          * ((Nat.ascFactorial (c - 1) l : ℕ) : ℚ)
          * (S + ((n - a0 : ℕ) : ℚ)) ^ (n - a0 - l)))
      = (((Nat.choose n a0 : ℕ) : ℚ) * ((Nat.choose (n - a0) l : ℕ) : ℚ))
        * ((u + (a0 : ℚ)) ^ a0 * ((Nat.ascFactorial (c - 1) l : ℕ) : ℚ)
          * (S + ((n - a0 : ℕ) : ℚ)) ^ (n - a0 - l)) := by
    ring
  have hRHS : (((Nat.choose n l : ℕ) : ℚ) * ((Nat.ascFactorial (c - 1) l : ℕ) : ℚ))
        * (((Nat.choose (n - l) a0 : ℕ) : ℚ) * (u + (a0 : ℚ)) ^ a0
          * ((S + (n : ℚ)) - (a0 : ℚ)) ^ (n - l - a0))
      = (((Nat.choose n l : ℕ) : ℚ) * ((Nat.choose (n - l) a0 : ℕ) : ℚ))
        * ((u + (a0 : ℚ)) ^ a0 * ((Nat.ascFactorial (c - 1) l : ℕ) : ℚ)
          * ((S + (n : ℚ)) - (a0 : ℚ)) ^ (n - l - a0)) := by
    ring
  rw [hLHS, hRHS, hC, hpow]

-- Base case is `hurwitz_singleton` above; the cons step (piAntidiag_cons
-- disjiUnion manipulation, trinomial reindexing via `hurwitz_id` and
-- `asc_sum_mul`) is the remaining gap.
private lemma hurwitz_finset (ι : Type*) [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty) :
    ∀ (y : ι → ℚ) (n : ℕ),
    ∑ f ∈ s.piAntidiag n,
      (((Nat.multinomial s f : ℕ)) : ℚ) * ∏ i ∈ s, (y i + ((f i : ℕ) : ℚ)) ^ f i
    = ∑ l ∈ Finset.range (n + 1),
      (((Nat.choose n l : ℕ) : ℚ) * (((Nat.ascFactorial (s.card - 1) l : ℕ)) : ℚ)
        * ((∑ i ∈ s, y i) + (n : ℚ)) ^ (n - l)) := by
  refine Finset.Nonempty.cons_induction ?base ?step hs
  · intro a y n
    exact hurwitz_singleton ι a y n
  · intro a s h hs' ih y n
    have hcard : (Finset.cons a s h).card = s.card + 1 := Finset.card_cons h
    have hsum : ∑ i ∈ Finset.cons a s h, y i = y a + ∑ i ∈ s, y i :=
      Finset.sum_cons h
    -- Unfold LHS via piAntidiag_cons.
    have hLHS : ∑ f ∈ (Finset.cons a s h).piAntidiag n,
          (((Nat.multinomial (Finset.cons a s h) f : ℕ)) : ℚ)
            * ∏ i ∈ Finset.cons a s h, (y i + ((f i : ℕ) : ℚ)) ^ f i
        = ∑ p ∈ Finset.antidiagonal n,
          ((((Nat.choose n p.1 : ℕ)) : ℚ) * (y a + (p.1 : ℚ)) ^ p.1)
            * ∑ l ∈ Finset.range (p.2 + 1),
              (((Nat.choose p.2 l : ℕ) : ℚ)
                * (((Nat.ascFactorial (s.card - 1) l : ℕ)) : ℚ)
                * ((∑ i ∈ s, y i) + (p.2 : ℚ)) ^ (p.2 - l)) := by
      rw [Finset.piAntidiag_cons h n, Finset.sum_disjiUnion]
      simp only [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro p hp
      have hpn : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
      have hterm : ∀ g ∈ s.piAntidiag p.2,
          (((Nat.multinomial (Finset.cons a s h)
                ((addRightEmbedding (fun t => if t = a then p.1 else 0)) g) : ℕ)) : ℚ)
              * ∏ i ∈ Finset.cons a s h,
                (y i + ((((addRightEmbedding
                  (fun t => if t = a then p.1 else 0)) g) i : ℕ) : ℚ))
                  ^ ((addRightEmbedding
                    (fun t => if t = a then p.1 else 0)) g i)
            = ((((Nat.choose n p.1 : ℕ)) : ℚ) * (y a + (p.1 : ℚ)) ^ p.1)
              * ((((Nat.multinomial s g : ℕ)) : ℚ)
                * ∏ i ∈ s, (y i + ((g i : ℕ) : ℚ)) ^ g i) := by
        intro g hg
        have heq : ((addRightEmbedding (fun t => if t = a then p.1 else 0)) g)
            = g + (fun t => if t = a then p.1 else 0) := by
          simp
        rw [heq]
        exact hurwitz_cons_term_eq ι a s h y n p.1 p.2 hpn g hg
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ih y p.2]
    have hcard' : (Finset.cons a s h).card - 1 = s.card := by
      rw [hcard, Nat.add_sub_cancel]
    rw [hLHS, hcard', hsum]
    -- Convert antidiagonal sum to range sum.
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    -- Expand outer constant into inner sum.
    have hexpand : ∀ a0 ∈ Finset.range (n + 1),
        ((((Nat.choose n a0 : ℕ)) : ℚ) * (y a + (a0 : ℚ)) ^ a0)
          * ∑ l ∈ Finset.range (n - a0 + 1),
            (((Nat.choose (n - a0) l : ℕ) : ℚ)
              * (((Nat.ascFactorial (s.card - 1) l : ℕ)) : ℚ)
              * ((∑ i ∈ s, y i) + ((n - a0 : ℕ) : ℚ)) ^ (n - a0 - l))
        = ∑ l ∈ Finset.range (n - a0 + 1),
            ((((Nat.choose n a0 : ℕ)) : ℚ) * (y a + (a0 : ℚ)) ^ a0
              * (((Nat.choose (n - a0) l : ℕ) : ℚ)
                * (((Nat.ascFactorial (s.card - 1) l : ℕ)) : ℚ)
                * ((∑ i ∈ s, y i) + ((n - a0 : ℕ) : ℚ)) ^ (n - a0 - l))) := by
      intro a0 _
      rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl hexpand]
    -- Swap a- and l-sums.
    have hswap := sum_triangle_swap n (M := ℚ) (fun a0 l =>
      (((Nat.choose n a0 : ℕ) : ℚ) * (y a + (a0 : ℚ)) ^ a0
        * (((Nat.choose (n - a0) l : ℕ) : ℚ)
          * ((Nat.ascFactorial (s.card - 1) l : ℕ) : ℚ)
          * ((∑ i ∈ s, y i) + ((n - a0 : ℕ) : ℚ)) ^ (n - a0 - l))))
    rw [hswap]
    -- For fixed l, inner a-sum via Step 2.
    have hstep2 : ∀ l ∈ Finset.range (n + 1),
        ∑ a0 ∈ Finset.range (n - l + 1),
          (((Nat.choose n a0 : ℕ) : ℚ) * (y a + (a0 : ℚ)) ^ a0
            * (((Nat.choose (n - a0) l : ℕ) : ℚ)
              * ((Nat.ascFactorial (s.card - 1) l : ℕ) : ℚ)
              * ((∑ i ∈ s, y i) + ((n - a0 : ℕ) : ℚ)) ^ (n - a0 - l)))
        = (((Nat.choose n l : ℕ) : ℚ) * ((Nat.ascFactorial (s.card - 1) l : ℕ) : ℚ))
          * ∑ i ∈ Finset.range (n - l + 1),
            (((Nat.choose (n - l) i : ℕ) : ℚ) * ((Nat.factorial i : ℕ) : ℚ)
              * (((∑ i ∈ s, y i) + (n : ℚ)) + y a) ^ (n - l - i)) := by
      intro l hl
      have hln : l ≤ n := by
        have := Finset.mem_range.mp hl
        omega
      have hterm : ∀ a0 ∈ Finset.range (n - l + 1),
          (((Nat.choose n a0 : ℕ) : ℚ) * (y a + (a0 : ℚ)) ^ a0
            * (((Nat.choose (n - a0) l : ℕ) : ℚ)
              * ((Nat.ascFactorial (s.card - 1) l : ℕ) : ℚ)
              * ((∑ i ∈ s, y i) + ((n - a0 : ℕ) : ℚ)) ^ (n - a0 - l)))
          = (((Nat.choose n l : ℕ) : ℚ) * ((Nat.ascFactorial (s.card - 1) l : ℕ) : ℚ))
            * ((((Nat.choose (n - l) a0 : ℕ) : ℚ) * (y a + (a0 : ℚ)) ^ a0
              * (((∑ i ∈ s, y i) + (n : ℚ)) - (a0 : ℚ)) ^ (n - l - a0))) := by
        intro a0 ha0
        have ha0le : a0 ≤ n - l := by
          have := Finset.mem_range.mp ha0
          omega
        have ha0n : a0 ≤ n := by omega
        have hall : a0 + l ≤ n := by omega
        exact swap_term_eq n a0 l (∑ i ∈ s, y i) (y a) s.card ha0n hall
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      congr 1
      exact hurwitz_id (y a) ((∑ i ∈ s, y i) + (n : ℚ)) (n - l)
    rw [Finset.sum_congr rfl hstep2]
    -- Normalize W bases: (S+n)+y a = y a+S+n.
    have hW : ∀ k : ℕ, (((∑ i ∈ s, y i) + (n : ℚ)) + y a) ^ k
        = (y a + (∑ i ∈ s, y i) + (n : ℚ)) ^ k := by
      intro k
      congr 1
      ring
    -- Expand to double sum F.
    have hexpand2 : ∀ l ∈ Finset.range (n + 1),
        (((Nat.choose n l : ℕ) : ℚ) * ((Nat.ascFactorial (s.card - 1) l : ℕ) : ℚ))
          * ∑ i ∈ Finset.range (n - l + 1),
            (((Nat.choose (n - l) i : ℕ) : ℚ) * ((Nat.factorial i : ℕ) : ℚ)
              * (((∑ i ∈ s, y i) + (n : ℚ)) + y a) ^ (n - l - i))
        = ∑ i ∈ Finset.range (n - l + 1),
            (((Nat.choose n l : ℕ) : ℚ) * ((Nat.ascFactorial (s.card - 1) l : ℕ) : ℚ)
              * (((Nat.choose (n - l) i : ℕ) : ℚ) * ((Nat.factorial i : ℕ) : ℚ)
                * (y a + (∑ i ∈ s, y i) + (n : ℚ)) ^ (n - l - i))) := by
      intro l _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hW]
    rw [Finset.sum_congr rfl hexpand2]
    -- Reindex by j = l+i.
    have hreindex := sum_triangle_reindex n (M := ℚ) (fun l i =>
      (((Nat.choose n l : ℕ) : ℚ) * ((Nat.ascFactorial (s.card - 1) l : ℕ) : ℚ)
        * (((Nat.choose (n - l) i : ℕ) : ℚ) * ((Nat.factorial i : ℕ) : ℚ)
          * (y a + (∑ i ∈ s, y i) + (n : ℚ)) ^ (n - l - i))))
    rw [hreindex]
    -- Each j-sum collapses via Step 3.
    have hcardpos : 1 ≤ s.card := Finset.card_pos.mpr hs'
    have hcard1 : s.card - 1 + 1 = s.card := Nat.sub_add_cancel hcardpos
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := by
      have := Finset.mem_range.mp hj
      omega
    have hterm2 : ∀ l ∈ Finset.range (j + 1),
        (((Nat.choose n l : ℕ) : ℚ) * ((Nat.ascFactorial (s.card - 1) l : ℕ) : ℚ)
          * (((Nat.choose (n - l) (j - l) : ℕ) : ℚ)
            * ((Nat.factorial (j - l) : ℕ) : ℚ)
            * (y a + (∑ i ∈ s, y i) + (n : ℚ)) ^ (n - l - (j - l))))
        = (((Nat.choose n j : ℕ) : ℚ)
            * ((((Nat.choose j l : ℕ) : ℚ)
              * ((Nat.ascFactorial (s.card - 1) l : ℕ) : ℚ)
              * ((Nat.factorial (j - l) : ℕ) : ℚ)))
            * (y a + (∑ i ∈ s, y i) + (n : ℚ)) ^ (n - j)) := by
      intro l hl
      have hlj : l ≤ j := by
        have := Finset.mem_range.mp hl
        omega
      have hexp : n - l - (j - l) = n - j := by omega
      have hadd : l + (j - l) = j := Nat.add_sub_cancel' hlj
      have htri := choose_trinomial_reindex_Q n l (j - l)
      rw [hadd] at htri
      -- htri : C(n,l)*C(n-l,j-l) = C(n,j)*C(j,l)
      have hpow : (y a + (∑ i ∈ s, y i) + (n : ℚ)) ^ (n - l - (j - l))
          = (y a + (∑ i ∈ s, y i) + (n : ℚ)) ^ (n - j) := by
        rw [hexp]
      -- Combine via ring + htri.
      have hLHS : (((Nat.choose n l : ℕ) : ℚ)
            * ((Nat.ascFactorial (s.card - 1) l : ℕ) : ℚ)
            * (((Nat.choose (n - l) (j - l) : ℕ) : ℚ)
              * ((Nat.factorial (j - l) : ℕ) : ℚ)
              * (y a + (∑ i ∈ s, y i) + (n : ℚ)) ^ (n - l - (j - l))))
          = ((((Nat.choose n l : ℕ) : ℚ)
            * ((Nat.choose (n - l) (j - l) : ℕ) : ℚ)))
            * (((Nat.ascFactorial (s.card - 1) l : ℕ) : ℚ)
              * ((Nat.factorial (j - l) : ℕ) : ℚ)
              * (y a + (∑ i ∈ s, y i) + (n : ℚ)) ^ (n - l - (j - l))) := by
        ring
      have hRHS : (((Nat.choose n j : ℕ) : ℚ)
            * ((((Nat.choose j l : ℕ) : ℚ)
              * ((Nat.ascFactorial (s.card - 1) l : ℕ) : ℚ)
              * ((Nat.factorial (j - l) : ℕ) : ℚ)))
            * (y a + (∑ i ∈ s, y i) + (n : ℚ)) ^ (n - j))
          = ((((Nat.choose n j : ℕ) : ℚ) * ((Nat.choose j l : ℕ) : ℚ)))
            * (((Nat.ascFactorial (s.card - 1) l : ℕ) : ℚ)
              * ((Nat.factorial (j - l) : ℕ) : ℚ)
              * (y a + (∑ i ∈ s, y i) + (n : ℚ)) ^ (n - j)) := by
        ring
      rw [hLHS, hRHS, htri, hpow]
    rw [Finset.sum_congr rfl hterm2]
    have hfactor : ∑ l ∈ Finset.range (j + 1),
          (((Nat.choose n j : ℕ) : ℚ)
            * ((((Nat.choose j l : ℕ) : ℚ)
              * ((Nat.ascFactorial (s.card - 1) l : ℕ) : ℚ)
              * ((Nat.factorial (j - l) : ℕ) : ℚ)))
            * (y a + (∑ i ∈ s, y i) + (n : ℚ)) ^ (n - j))
        = (((Nat.choose n j : ℕ) : ℚ)
            * (y a + (∑ i ∈ s, y i) + (n : ℚ)) ^ (n - j))
          * ∑ l ∈ Finset.range (j + 1),
            (((Nat.choose j l : ℕ) : ℚ)
              * ((Nat.ascFactorial (s.card - 1) l : ℕ) : ℚ)
              * ((Nat.factorial (j - l) : ℕ) : ℚ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [hfactor, asc_sum_mul (s.card - 1) j, hcard1]
    ring

-- Umbral linear functional X^i ↦ B_i.
private noncomputable def umbral : Polynomial ℚ →ₗ[ℚ] ℚ :=
  Polynomial.lsum (fun i => LinearMap.mulRight ℚ (_root_.bernoulli i))

private lemma umbral_monomial (m : ℕ) (a : ℚ) :
    umbral (Polynomial.monomial m a) = a * _root_.bernoulli m := by
  unfold umbral
  rw [Polynomial.lsum_apply,
    Polynomial.sum_monomial_index _ _ (by simp [LinearMap.mulRight_apply]),
    LinearMap.mulRight_apply]

-- Expansion of (X + C t)^k as monomials.
private lemma X_add_C_pow_eq_sum (t : ℚ) (k : ℕ) :
    (Polynomial.X + Polynomial.C t) ^ k
      = ∑ m ∈ Finset.range (k + 1),
        Polynomial.monomial m (((Nat.choose k m : ℕ) : ℚ) * t ^ (k - m)) := by
  have hpow := add_pow Polynomial.X (Polynomial.C t) k
  rw [hpow]
  apply Finset.sum_congr rfl
  intro m hm
  have hC1 : (Polynomial.C t) ^ (k - m)
      = Polynomial.C (t ^ (k - m)) := by
    rw [← map_pow]
  have hC2 : ((Nat.choose k m : Polynomial ℚ))
      = Polynomial.C (((Nat.choose k m : ℕ) : ℚ)) := by
    exact (map_natCast _ _).symm
  -- Original term: X^m * (C t)^(k-m) * ↑choose
  rw [hC1, hC2]
  have hmul : Polynomial.X ^ m * Polynomial.C (t ^ (k - m))
        * Polynomial.C (((Nat.choose k m : ℕ) : ℚ))
      = Polynomial.C (((Nat.choose k m : ℕ) : ℚ) * t ^ (k - m))
        * Polynomial.X ^ m := by
    calc Polynomial.X ^ m * Polynomial.C (t ^ (k - m))
            * Polynomial.C (((Nat.choose k m : ℕ) : ℚ))
          = Polynomial.X ^ m
            * (Polynomial.C (t ^ (k - m))
              * Polynomial.C (((Nat.choose k m : ℕ) : ℚ))) := by
            rw [mul_assoc]
        _ = Polynomial.X ^ m
            * Polynomial.C ((t ^ (k - m)) * ((Nat.choose k m : ℕ) : ℚ)) := by
            rw [← Polynomial.C_mul]
        _ = Polynomial.X ^ m
            * Polynomial.C (((Nat.choose k m : ℕ) : ℚ) * t ^ (k - m)) := by
            rw [mul_comm (t ^ (k - m)) (((Nat.choose k m : ℕ) : ℚ))]
        _ = Polynomial.C (((Nat.choose k m : ℕ) : ℚ) * t ^ (k - m))
            * Polynomial.X ^ m := by
            rw [mul_comm]
  rw [hmul, Polynomial.C_mul_X_pow_eq_monomial]

-- Umbral evaluation gives Bernoulli polynomials.
private lemma umbral_X_add_C_pow (t : ℚ) (k : ℕ) :
    umbral ((Polynomial.X + Polynomial.C t) ^ k)
      = Polynomial.eval t (Polynomial.bernoulli k) := by
  rw [X_add_C_pow_eq_sum, map_sum]
  have hLHS : ∑ m ∈ Finset.range (k + 1),
        umbral (Polynomial.monomial m (((Nat.choose k m : ℕ) : ℚ) * t ^ (k - m)))
      = ∑ m ∈ Finset.range (k + 1),
        (((Nat.choose k m : ℕ) : ℚ) * t ^ (k - m) * _root_.bernoulli m) := by
    apply Finset.sum_congr rfl
    intro m _
    rw [umbral_monomial]
  rw [hLHS]
  have hbern := Polynomial.bernoulli_def k
  have hRHS : Polynomial.eval t (Polynomial.bernoulli k)
      = ∑ i ∈ Finset.range (k + 1),
        (_root_.bernoulli (k - i) * ((Nat.choose k i : ℕ) : ℚ) * t ^ i) := by
    rw [hbern, Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Polynomial.eval_monomial]
  rw [hRHS]
  -- Reindex LHS by m ↦ k-m via reflection.
  have hreflect := Finset.sum_range_reflect
    (fun m : ℕ => ((Nat.choose k m : ℕ) : ℚ) * t ^ (k - m) * _root_.bernoulli m)
    (k + 1)
  simp only [Nat.add_sub_cancel] at hreflect
  rw [← hreflect]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := by
    have := Finset.mem_range.mp hi
    omega
  have hchoose : ((Nat.choose k (k - i) : ℕ) : ℚ)
      = ((Nat.choose k i : ℕ) : ℚ) := by
    have h := Nat.choose_symm hik
    rw [← h]
  have hexp : k - (k - i) = i := Nat.sub_sub_self hik
  have hterm : ((Nat.choose k (k - i) : ℕ) : ℚ) * t ^ (k - (k - i))
        * _root_.bernoulli (k - i)
      = _root_.bernoulli (k - i) * ((Nat.choose k i : ℕ) : ℚ) * t ^ i := by
    rw [hchoose, hexp]
    ring
  exact hterm

private lemma umbral_C_mul (a : ℚ) (p : Polynomial ℚ) :
    umbral (Polynomial.C a * p) = a * umbral p := by
  rw [Polynomial.C_mul', map_smul, smul_eq_mul]

/--
**Abel–Hurwitz–Bernoulli multinomial identity.** Let $B_k(t)$ denote the $k$-th Bernoulli
polynomial. Let $m \ge 2$ and $n$ be natural numbers, let $x_1, \dots, x_m$ be rational numbers,
and let $r$ be an index with $1 \le r \le m$. Then
$$\sum_{l} \binom{n}{l_1, \dots, l_m} B_{l_r}(x_r + l_r) \prod_{j \neq r} (x_j + l_j)^{l_j} =
\sum_{k=0}^{n} \binom{n}{k} \frac{(m + k - 2)!}{(m - 2)!} B_{n-k}(x_1 + \dots + x_m + n),$$
where the sum on the left runs over all $l = (l_1, \dots, l_m) \in \mathbb{N}^m$ with
$l_1 + \dots + l_m = n$, and $\binom{n}{l_1, \dots, l_m}$ is the multinomial coefficient.

The source states the identity for arbitrary real or complex parameters; this statement records
its specialization to rational $x_1, \dots, x_m$.

Proves `Wanted` entry `abel_hurwitz_bernoulli_multinomial`.

Source: Claudio de J. Pita Ruiz V., "Carlitz-Type and Other Bernoulli
Identities," Journal of Integer Sequences 19 (2016), Article 16.1.8,
Proposition [Abel-Hurwitz-Bernoulli identity] (a), equation (5.16),
lines 821–829,
https://cs.uwaterloo.ca/journals/JIS/VOL19/Pita/pita23.tex
-/
theorem abel_hurwitz_bernoulli_multinomial
    (m n : ℕ) (x : Fin m → ℚ) (r : Fin m) (hm : 2 ≤ m) :
    ∑ l ∈ (Fintype.piFinset (fun _ : Fin m => Finset.range (n + 1))).filter
      (fun l => ∑ i, l i = n),
      (Nat.multinomial Finset.univ l : ℚ) *
        (Polynomial.eval (x r + (l r : ℚ)) (Polynomial.bernoulli (l r)) *
        ∏ j ∈ Finset.univ.erase r, (x j + (l j : ℚ)) ^ l j) =
    ∑ l ∈ Finset.range (n + 1),
      (Nat.choose n l : ℚ) *
        ((Nat.factorial (m + l - 2) : ℚ) / (Nat.factorial (m - 2) : ℚ)) *
        Polynomial.eval ((∑ i, x i) + (n : ℚ)) (Polynomial.bernoulli (n - l)) := by
  -- Step 5: lift to ℚ[X].
  set y_poly : Fin m → Polynomial ℚ :=
    fun j => if j = r then Polynomial.X + Polynomial.C (x r) else Polynomial.C (x j)
    with hy_def
  have hsum_poly : ∑ j ∈ (Finset.univ : Finset (Fin m)), y_poly j
      = Polynomial.X + Polynomial.C (∑ i, x i) := by
    have h1 : ∀ j ∈ (Finset.univ : Finset (Fin m)),
        y_poly j = Polynomial.C (x j) + (if j = r then Polynomial.X else 0) := by
      intro j _
      simp only [hy_def]
      by_cases hj : j = r
      · simp [hj, add_comm]
      · simp [hj]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
    have hC : ∑ j ∈ (Finset.univ : Finset (Fin m)), Polynomial.C (x j)
        = Polynomial.C (∑ i, x i) := by
      rw [map_sum]
    have hX : ∑ j ∈ (Finset.univ : Finset (Fin m)),
          (if j = r then Polynomial.X else (0 : Polynomial ℚ))
        = Polynomial.X := by
      rw [Finset.sum_ite_eq']
      simp
    rw [hC, hX, add_comm]
  have hsum_poly_add : (∑ j ∈ (Finset.univ : Finset (Fin m)), y_poly j)
        + Polynomial.C ((n : ℚ))
      = Polynomial.X + Polynomial.C ((∑ i, x i) + (n : ℚ)) := by
    rw [hsum_poly, add_assoc, ← Polynomial.C_add]
  -- Polynomial identity.
  set LHS_poly : Polynomial ℚ :=
    ∑ f ∈ (Finset.univ : Finset (Fin m)).piAntidiag n,
      Polynomial.C (((Nat.multinomial Finset.univ f : ℕ)) : ℚ)
        * ∏ i ∈ (Finset.univ : Finset (Fin m)),
          (y_poly i + Polynomial.C (((f i : ℕ)) : ℚ)) ^ f i
    with hLHS_def
  set RHS_poly : Polynomial ℚ :=
    ∑ l ∈ Finset.range (n + 1),
      Polynomial.C ((((Nat.choose n l : ℕ)) : ℚ)
        * (((Nat.ascFactorial (m - 1) l : ℕ)) : ℚ))
        * ((∑ j ∈ (Finset.univ : Finset (Fin m)), y_poly j)
          + Polynomial.C ((n : ℚ))) ^ (n - l)
    with hRHS_def
  have hcard_univ : (Finset.univ : Finset (Fin m)).card = m := by
    simp
  have huniv_ne : (Finset.univ : Finset (Fin m)).Nonempty :=
    ⟨r, Finset.mem_univ r⟩
  have hpoly : LHS_poly = RHS_poly := by
    apply Polynomial.funext
    intro q
    set y_q : Fin m → ℚ := fun j => Polynomial.eval q (y_poly j) with hyq_def
    have hLHS_eval : Polynomial.eval q LHS_poly
        = ∑ f ∈ (Finset.univ : Finset (Fin m)).piAntidiag n,
          (((Nat.multinomial Finset.univ f : ℕ)) : ℚ)
            * ∏ i ∈ (Finset.univ : Finset (Fin m)),
              (y_q i + ((f i : ℕ) : ℚ)) ^ f i := by
      simp only [hLHS_def, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C, hyq_def]
      apply Finset.sum_congr rfl
      intro f _
      congr 1
      rw [Polynomial.eval_prod]
      apply Finset.prod_congr rfl
      intro i _
      simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_C]
    have hRHS_eval : Polynomial.eval q RHS_poly
        = ∑ l ∈ Finset.range (n + 1),
          (((Nat.choose n l : ℕ) : ℚ)
            * (((Nat.ascFactorial
              ((Finset.univ : Finset (Fin m)).card - 1) l : ℕ)) : ℚ)
            * ((∑ i ∈ (Finset.univ : Finset (Fin m)), y_q i)
              + (n : ℚ)) ^ (n - l)) := by
      simp only [hRHS_def, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add, hyq_def,
        hcard_univ]
    have hhur := hurwitz_finset (Fin m) (Finset.univ : Finset (Fin m)) huniv_ne y_q n
    rw [hLHS_eval, hRHS_eval]
    exact hhur
  -- Step 6: apply umbral.
  have humb := congrArg umbral hpoly
  have hLHS_umbral : umbral LHS_poly
      = ∑ f ∈ (Finset.univ : Finset (Fin m)).piAntidiag n,
        (((Nat.multinomial Finset.univ f : ℕ) : ℚ)
          * (∏ j ∈ Finset.univ.erase r, (x j + ((f j : ℕ) : ℚ)) ^ f j)
          * Polynomial.eval (x r + ((f r : ℕ) : ℚ))
            (Polynomial.bernoulli (f r))) := by
    simp only [hLHS_def, map_sum]
    apply Finset.sum_congr rfl
    intro f hf
    -- Split product at r.
    have hr_mem : r ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ r
    have hsplit := Finset.mul_prod_erase (Finset.univ : Finset (Fin m))
      (fun i => (y_poly i + Polynomial.C (((f i : ℕ)) : ℚ)) ^ f i) hr_mem
    -- hsplit : (r-factor) * ∏_erase = ∏_univ
    have hy_r : y_poly r = Polynomial.X + Polynomial.C (x r) := by
      simp [hy_def]
    have hy_ne : ∀ j ∈ Finset.univ.erase r, y_poly j = Polynomial.C (x j) := by
      intro j hj
      have hne : j ≠ r := (Finset.mem_erase.mp hj).1
      simp [hy_def, hne]
    have hr_factor : (y_poly r + Polynomial.C (((f r : ℕ)) : ℚ)) ^ f r
        = (Polynomial.X + Polynomial.C (x r + ((f r : ℕ) : ℚ))) ^ f r := by
      congr 1
      rw [hy_r, add_assoc, ← Polynomial.C_add]
    have h_erase : ∏ j ∈ Finset.univ.erase r,
          (y_poly j + Polynomial.C (((f j : ℕ)) : ℚ)) ^ f j
        = Polynomial.C (∏ j ∈ Finset.univ.erase r,
          (x j + ((f j : ℕ) : ℚ)) ^ f j) := by
      have hterm : ∀ j ∈ Finset.univ.erase r,
          (y_poly j + Polynomial.C (((f j : ℕ)) : ℚ)) ^ f j
            = Polynomial.C ((x j + ((f j : ℕ) : ℚ)) ^ f j) := by
        intro j hj
        rw [hy_ne j hj, ← Polynomial.C_add, ← map_pow]
      rw [Finset.prod_congr rfl hterm, ← map_prod]
    -- Combine C factors.
    have hterm_eq : Polynomial.C (((Nat.multinomial Finset.univ f : ℕ)) : ℚ)
          * ∏ i ∈ (Finset.univ : Finset (Fin m)),
            (y_poly i + Polynomial.C (((f i : ℕ)) : ℚ)) ^ f i
        = Polynomial.C ((((Nat.multinomial Finset.univ f : ℕ)) : ℚ)
            * ∏ j ∈ Finset.univ.erase r, (x j + ((f j : ℕ) : ℚ)) ^ f j)
          * (Polynomial.X + Polynomial.C (x r + ((f r : ℕ) : ℚ))) ^ f r := by
      rw [← hsplit, hr_factor, h_erase]
      have hring : Polynomial.C (((Nat.multinomial Finset.univ f : ℕ)) : ℚ)
            * ((Polynomial.X
              + Polynomial.C (x r + ((f r : ℕ) : ℚ))) ^ f r
              * Polynomial.C (∏ j ∈ Finset.univ.erase r,
                (x j + ((f j : ℕ) : ℚ)) ^ f j))
          = (Polynomial.C (((Nat.multinomial Finset.univ f : ℕ)) : ℚ)
              * Polynomial.C (∏ j ∈ Finset.univ.erase r,
                (x j + ((f j : ℕ) : ℚ)) ^ f j))
            * (Polynomial.X + Polynomial.C (x r + ((f r : ℕ) : ℚ))) ^ f r := by
        ring
      rw [hring, ← Polynomial.C_mul]
    rw [hterm_eq, umbral_C_mul, umbral_X_add_C_pow]
  have hRHS_umbral : umbral RHS_poly
      = ∑ l ∈ Finset.range (n + 1),
        (((Nat.choose n l : ℕ) : ℚ)
          * (((Nat.ascFactorial (m - 1) l : ℕ)) : ℚ)
          * Polynomial.eval ((∑ i, x i) + (n : ℚ))
            (Polynomial.bernoulli (n - l))) := by
    simp only [hRHS_def, map_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [hsum_poly_add, umbral_C_mul, umbral_X_add_C_pow]
  rw [hLHS_umbral, hRHS_umbral] at humb
  -- Convert to target via filter + factorial ratio.
  have hfilter := filter_piFinset_eq_piAntidiag m n
  have hfact : ∀ l ∈ Finset.range (n + 1),
      (((Nat.ascFactorial (m - 1) l : ℕ)) : ℚ)
        = ((Nat.factorial (m + l - 2) : ℚ)
          / (Nat.factorial (m - 2) : ℚ)) := by
    intro l _
    exact (factorial_div_eq_ascFactorial m l hm).symm
  rw [← hfilter] at humb
  -- humb now equates filter sum (with mult*prod*B) to range sum (with choose*asc*B).
  -- Target LHS has mult*(B*prod), target RHS has choose*(fact/fact)*B.
  have hLHS_target : ∑ l ∈ (Fintype.piFinset
          (fun _ : Fin m => Finset.range (n + 1))).filter
          (fun l => ∑ i, l i = n),
          (Nat.multinomial Finset.univ l : ℚ) *
            (Polynomial.eval (x r + (l r : ℚ)) (Polynomial.bernoulli (l r)) *
            ∏ j ∈ Finset.univ.erase r, (x j + (l j : ℚ)) ^ l j)
      = ∑ f ∈ (Fintype.piFinset
          (fun _ : Fin m => Finset.range (n + 1))).filter
          (fun l => ∑ i, l i = n),
        (((Nat.multinomial Finset.univ f : ℕ) : ℚ)
          * (∏ j ∈ Finset.univ.erase r, (x j + ((f j : ℕ) : ℚ)) ^ f j)
          * Polynomial.eval (x r + ((f r : ℕ) : ℚ))
            (Polynomial.bernoulli (f r))) := by
    apply Finset.sum_congr rfl
    intro f _
    ring
  have hRHS_target : ∑ l ∈ Finset.range (n + 1),
        (((Nat.choose n l : ℕ) : ℚ)
          * (((Nat.ascFactorial (m - 1) l : ℕ)) : ℚ)
          * Polynomial.eval ((∑ i, x i) + (n : ℚ))
            (Polynomial.bernoulli (n - l)))
      = ∑ l ∈ Finset.range (n + 1),
        (Nat.choose n l : ℚ) *
          ((Nat.factorial (m + l - 2) : ℚ)
            / (Nat.factorial (m - 2) : ℚ)) *
          Polynomial.eval ((∑ i, x i) + (n : ℚ))
            (Polynomial.bernoulli (n - l)) := by
    apply Finset.sum_congr rfl
    intro l hl
    rw [hfact l hl]
  rw [hLHS_target, ← hRHS_target]
  exact humb

end MetaMathlibExt
end
