/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

private theorem choose_eq_factorial_div_real (n k : ℕ) (h : k ≤ n) :
    (Nat.choose n k : ℝ) = (n.factorial : ℝ) / ((k.factorial : ℝ) * ((n - k).factorial : ℝ)) := by
  have hdvd := Nat.factorial_mul_factorial_dvd_factorial h
  have hne : ((k.factorial * (n - k).factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast mul_ne_zero (Nat.factorial_ne_zero k) (Nat.factorial_ne_zero (n - k))
  rw [Nat.choose_eq_factorial_div_factorial h, Nat.cast_div hdvd hne, Nat.cast_mul]

private theorem catalan_succ_mul_ratio (j : ℕ) :
    ((j : ℝ) + 1 + 1) * (catalan (j + 1) : ℝ)
      = 2 * (2 * (j : ℝ) + 1) * (catalan j : ℝ) := by
  have e1 := succ_mul_catalan_eq_centralBinom (j + 1)
  have e2 := succ_mul_catalan_eq_centralBinom j
  have e3 := Nat.succ_mul_centralBinom_succ j
  have e1r : ((j : ℝ) + 1 + 1) * (catalan (j + 1) : ℝ)
      = (Nat.centralBinom (j + 1) : ℝ) := by
    exact_mod_cast e1
  have e2r : ((j : ℝ) + 1) * (catalan j : ℝ) = (Nat.centralBinom j : ℝ) := by
    exact_mod_cast e2
  have e3r : ((j : ℝ) + 1) * (Nat.centralBinom (j + 1) : ℝ)
      = 2 * (2 * (j : ℝ) + 1) * (Nat.centralBinom j : ℝ) := by
    exact_mod_cast e3
  have hpos : ((j : ℝ) + 1) ≠ 0 := by positivity
  have key : ((j : ℝ) + 1) * ((((j : ℝ) + 1 + 1) * (catalan (j + 1) : ℝ))
      - 2 * (2 * (j : ℝ) + 1) * (catalan j : ℝ)) = 0 := by
    linear_combination ((j : ℝ) + 1) * e1r - 2 * (2 * (j : ℝ) + 1) * e2r + e3r
  have hsub := (mul_eq_zero.mp key).resolve_left hpos
  linarith

private theorem Fterm_rec (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n / 2) :
    (-1 / 4 : ℝ) ^ k * (Nat.choose n (2 * k) : ℝ) * (catalan k : ℝ)
    = (1 + 2 * (k : ℝ) / ((n : ℝ) + 2)) *
        ((-1 / 4 : ℝ) ^ k * (Nat.choose (n - 1) (2 * k) : ℝ) * (catalan k : ℝ))
      + ((2 * (k : ℝ) - (n : ℝ) - 1) / ((n : ℝ) + 2)) *
        ((-1 / 4 : ℝ) ^ (k - 1) * (Nat.choose (n - 1) (2 * (k - 1)) : ℝ) *
          (catalan (k - 1) : ℝ)) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have ejs : j.succ = j + 1 := by omega
  have ems : m.succ = m + 1 := by omega
  rw [ejs, ems]
  have e2k : 2 * (j + 1) = 2 * j + 2 := by ring
  rw [Nat.add_sub_cancel, Nat.add_sub_cancel, e2k, pow_succ]
  have h2k : 2 * (j + 1) ≤ m + 1 := by omega
  have hJ1 : ((j : ℝ) + 1) ≠ 0 := by positivity
  have hJ2 : ((j : ℝ) + 1 + 1) ≠ 0 := by positivity
  have hratio := catalan_succ_mul_ratio j
  by_cases hbound : 2 * (j + 1) = m + 1
  · -- boundary case: 2 * k = n, so A = choose (n-1) (2k) = 0, C = 1
    have hme : m + 1 = 2 * j + 2 := by omega
    have hA0 : Nat.choose m (2 * j + 2) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    have hC1 : Nat.choose (m + 1) (2 * j + 2) = 1 := by
      rw [hme]
      exact Nat.choose_self _
    rw [hA0, hC1]
    simp only [Nat.cast_zero, Nat.cast_one, mul_one, mul_zero, zero_mul]
    rw [hme]
    have hB2 : (Nat.choose m (2 * j) : ℝ) = 2 * (j : ℝ) + 1 := by
      have hBle : 2 * j ≤ m := by omega
      have hB := choose_eq_factorial_div_real m (2 * j) hBle
      have hmj : m - 2 * j = 1 := by omega
      have hmf : (m.factorial : ℝ) = (2 * (j : ℝ) + 1) * ((2 * j).factorial : ℝ) := by
        have hme : m = 2 * j + 1 := by omega
        have hfs := Nat.factorial_succ (2 * j)
        rw [hme]
        exact_mod_cast hfs
      have h2j : (((2 * j).factorial : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (2 * j)
      rw [hB, hmj, Nat.factorial_one, Nat.cast_one, mul_one, hmf]
      field_simp [h2j]
    have key : (-1 / 4 : ℝ) * (catalan (j + 1) : ℝ)
        = ((2 * ((j + 1 : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) - 1) / (((2 * j + 2 : ℕ) : ℝ) + 2))
          * ((Nat.choose m (2 * j) : ℝ) * (catalan j : ℝ)) := by
      rw [hB2]
      have hden : ((((2 * j + 2 : ℕ))) : ℝ) + 2 ≠ 0 := by positivity
      push_cast
      push_cast at hden
      conv_rhs => rw [div_mul_eq_mul_div]
      rw [eq_div_iff hden]
      linear_combination 2 * (-1 / 4 : ℝ) * hratio
    push_cast at key
    push_cast
    linear_combination ((-1 / 4 : ℝ) ^ j) * key
  · -- interior case: all factorial forms valid
    have hint : 2 * (j + 1) ≤ m := by omega
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (show 2 * j + 2 ≤ m by omega)
    have hC := choose_eq_factorial_div_real (((2 * j + 2) + r) + 1) (2 * j + 2) (by omega)
    have hA := choose_eq_factorial_div_real ((2 * j + 2) + r) (2 * j + 2) (by omega)
    have hB := choose_eq_factorial_div_real ((2 * j + 2) + r) (2 * j) (by omega)
    have e1 := succ_mul_catalan_eq_centralBinom (j + 1)
    have e2 := succ_mul_catalan_eq_centralBinom j
    have e1r : ((j : ℝ) + 1 + 1) * (catalan (j + 1) : ℝ)
        = (Nat.centralBinom (j + 1) : ℝ) := by
      exact_mod_cast e1
    have e2r : ((j : ℝ) + 1) * (catalan j : ℝ) = (Nat.centralBinom j : ℝ) := by
      exact_mod_cast e2
    have hc_eq : (catalan (j + 1) : ℝ)
        = (Nat.centralBinom (j + 1) : ℝ) / ((j : ℝ) + 1 + 1) := by
      rw [eq_div_iff hJ2]
      linear_combination e1r
    have hcp_eq : (catalan j : ℝ) = (Nat.centralBinom j : ℝ) / ((j : ℝ) + 1) := by
      rw [eq_div_iff hJ1]
      linear_combination e2r
    have hcb1 := Nat.centralBinom_eq_two_mul_choose (j + 1)
    rw [e2k] at hcb1
    have hCb1 : (Nat.centralBinom (j + 1) : ℝ)
        = ((2 * j + 2).factorial : ℝ)
          / (((j + 1).factorial : ℝ) * (((2 * j + 2) - (j + 1)).factorial : ℝ)) := by
      rw [hcb1]
      exact choose_eq_factorial_div_real (2 * j + 2) (j + 1) (by omega)
    have hcb0 := Nat.centralBinom_eq_two_mul_choose j
    have hCb0 : (Nat.centralBinom j : ℝ)
        = ((2 * j).factorial : ℝ)
          / (((j).factorial : ℝ) * (((2 * j) - j).factorial : ℝ)) := by
      rw [hcb0]
      exact choose_eq_factorial_div_real (2 * j) j (by omega)
    have gC : (((2 * j + 2) + r) + 1) - (2 * j + 2) = r + 1 := by omega
    have gB : ((2 * j + 2) + r) - 2 * j = (r + 1) + 1 := by omega
    have gD : (2 * j + 2) - (j + 1) = j + 1 := by omega
    have gE : (2 * j) - j = j := by omega
    have fN : ((((2 * j + 2) + r) + 1).factorial : ℝ)
        = ((((2 * j + 2) + r) + 1 : ℕ) : ℝ) * ((((2 * j + 2) + r).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_succ ((2 * j + 2) + r)
    have f2a : ((2 * j + 2).factorial : ℝ)
        = ((2 * j + 2 : ℕ) : ℝ) * (((2 * j + 1).factorial : ℕ) : ℝ) := by
      have h := Nat.factorial_succ (2 * j + 1)
      have e : (2 * j + 2 : ℕ) = (2 * j + 1) + 1 := by ring
      rw [e]
      exact_mod_cast h
    have f2b : ((2 * j + 1).factorial : ℝ)
        = ((2 * j + 1 : ℕ) : ℝ) * ((((2 * j).factorial : ℕ)) : ℝ) := by
      exact_mod_cast Nat.factorial_succ (2 * j)
    have fJ : ((j + 1).factorial : ℝ)
        = ((j + 1 : ℕ) : ℝ) * (((j.factorial : ℕ)) : ℝ) := by
      exact_mod_cast Nat.factorial_succ j
    have fR1 : (((r + 1) + 1).factorial : ℝ)
        = ((((r + 1) + 1 : ℕ)) : ℝ) * ((((r + 1).factorial : ℕ)) : ℝ) := by
      exact_mod_cast Nat.factorial_succ (r + 1)
    have fR0 : (((r + 1)).factorial : ℝ)
        = ((((r + 1) : ℕ)) : ℝ) * ((((r).factorial : ℕ)) : ℝ) := by
      exact_mod_cast Nat.factorial_succ r
    rw [hC, hA, hB, hc_eq, hcp_eq, hCb1, hCb0, gC, gB, gD, gE,
      Nat.add_sub_cancel_left, fN, f2a, f2b, fJ, fR1, fR0]
    have hFm : (((((2 * j + 2) + r).factorial : ℕ)) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    have hF2 : ((((2 * j).factorial : ℕ)) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    have hFj : ((j.factorial : ℝ)) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    have hFr : ((r.factorial : ℝ)) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    have hN : (((((2 * j + 2) + r) + 1 : ℕ)) : ℝ) + 2 ≠ 0 := by positivity
    push_cast
    push_cast at hN
    field_simp [hFm, hF2, hFj, hFr, hN, hJ1, hJ2]
    ring

private theorem Fterm_zero (n : ℕ) :
    (-1 / 4 : ℝ) ^ (0 : ℕ) * (Nat.choose n (2 * 0) : ℝ) * (catalan 0 : ℝ) = 1 := by
  simp [catalan_zero]

private theorem Fterm_vanish (t : ℕ) (ht : 1 ≤ t) :
    (-1 / 4 : ℝ) ^ t * (Nat.choose (2 * t - 1) (2 * t) : ℝ) * (catalan t : ℝ) = 0 := by
  have h0 : Nat.choose (2 * t - 1) (2 * t) = 0 :=
    Nat.choose_eq_zero_of_lt (by omega)
  simp [h0]

/--
**Closed form of the Eloe–Kublik gamma array.** Let $\gamma_{n,k}$, for natural numbers $n$ and
$k$, be real numbers such that $\gamma_{n,0} = 1$ for every $n$, $\gamma_{2n-1,n} = 0$ for every
$n \ge 1$, and

$$\gamma_{n,k} = (1 + \frac{2k}{n+2})\,\gamma_{n-1,k} + \frac{2k-n-1}{n+2}\,\gamma_{n-1,k-1}$$

whenever $n \ge 2$ and $1 \le k \le \lfloor n/2 \rfloor$. Then
$\gamma_{n,k} = (-\frac{1}{4})^k \binom{n}{2k} C_k$ for all natural numbers $n$ and $k$ with
$k \le \lfloor n/2 \rfloor$, where $C_k$ is the $k$-th Catalan number.

Proves `Wanted` entry `gamma_closed_form`.

Source: Paul Eloe and Catherine Kublik, "When Numerical Analysis Crosses
Paths with Catalan and Generalized Motzkin Numbers," Journal of Integer
Sequences 21 (2018), Article 18.8.4, Theorem `closedform_thm`, lines 390-396,
<https://cs.uwaterloo.ca/journals/JIS/VOL21/Kublik/kublik2.tex>; the recursion
and initial conditions are equation `gamma_linear_recursion`, lines 87-91.
-/
theorem gamma_closed_form : ∀ (γ : ℕ → ℕ → ℝ),
    (∀ n : ℕ, γ n 0 = 1) →
    (∀ n : ℕ, 1 ≤ n → γ (2 * n - 1) n = 0) →
    (∀ n k : ℕ, 2 ≤ n → 1 ≤ k → k ≤ n / 2 →
      γ n k = (1 + 2 * (k : ℝ) / ((n : ℝ) + 2)) * γ (n - 1) k +
        (2 * (k : ℝ) - (n : ℝ) - 1) / ((n : ℝ) + 2) * γ (n - 1) (k - 1)) →
    ∀ n k : ℕ, k ≤ n / 2 →
      γ n k = (-1 / 4 : ℝ) ^ k * (Nat.choose n (2 * k) : ℝ) * (catalan k : ℝ) := by
  intro γ h0 hvan hrec n
  induction n with
  | zero =>
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    rw [h0 0]
    exact (Fterm_zero 0).symm
  | succ m ih =>
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      rw [h0 (m + 1)]
      exact (Fterm_zero (m + 1)).symm
    · have hk1 : 1 ≤ k := by omega
      have hm2 : 2 ≤ m + 1 := by omega
      have hrec_eq := hrec (m + 1) k hm2 hk1 hk
      have hF := Fterm_rec (m + 1) k hm2 hk1 hk
      simp only [Nat.add_sub_cancel] at hrec_eq hF
      have hkm : k ≤ m / 2 ∨ m + 1 = 2 * k := by omega
      have e1 : γ m k = (-1 / 4 : ℝ) ^ k * (Nat.choose m (2 * k) : ℝ) * (catalan k : ℝ) := by
        rcases hkm with h | h
        · exact ih k h
        · have hmk : m = 2 * k - 1 := by omega
          have hz1 : γ m k = 0 := by
            rw [hmk]
            exact hvan k hk1
          have hz2 : (-1 / 4 : ℝ) ^ k * (Nat.choose m (2 * k) : ℝ) * (catalan k : ℝ) = 0 := by
            rw [hmk]
            exact Fterm_vanish k hk1
          rw [hz1, hz2]
      have hkm1 : k - 1 ≤ m / 2 := by omega
      have e2 : γ m (k - 1)
          = (-1 / 4 : ℝ) ^ (k - 1) * (Nat.choose m (2 * (k - 1)) : ℝ)
            * (catalan (k - 1) : ℝ) :=
        ih (k - 1) hkm1
      rw [hrec_eq, e1, e2]
      exact hF.symm

end MetaMathlibExt
