/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Tactic.NormNum.NatFactorial

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 5, Entry 1

Unique (1-2ⁿ)Bₙ/n! solution of a shift-plus-derivative identity.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch5

namespace Entry1Euleriangf

open scoped Nat Real BigOperators Interval Polynomial
open Filter Finset Complex Topology

noncomputable section

def chapter5DerivativeExpansion {R : Type*} [Semiring R]
    (a : ℕ → R) (h : R) (phi : R[X]) : R[X] :=
  ∑ n ∈ range (phi.natDegree + 1),
    Polynomial.C (a n * h ^ n) * (Polynomial.derivative^[n]) phi

def chapter5Entry1PlusCoeff (n : ℕ) : ℝ :=
  (1 - (2 : ℝ) ^ n) * (bernoulli n : ℝ) / (n.factorial : ℝ)

/-- The source's shift `p(x) ↦ p(x + h)`. It is `Polynomial.taylor h p` (see
`chapter5PolynomialShift_eq_taylor`); the name is kept because the frozen `Wanted` statement uses
it. -/
def chapter5PolynomialShift {R : Type*} [Semiring R]
    (h : R) (p : R[X]) : R[X] :=
  p.comp (Polynomial.X + Polynomial.C h)

theorem chapter5PolynomialShift_eq_taylor {R : Type*} [Semiring R] (h : R) (p : R[X]) :
    chapter5PolynomialShift h p = Polynomial.taylor h p :=
  (Polynomial.taylor_apply h p).symm

private theorem bernoulli_egf :
    (PowerSeries.mk fun n => (bernoulli n : ℚ) / (n.factorial : ℚ)) *
      (PowerSeries.exp ℚ - 1) = PowerSeries.X := by
  have h := Polynomial.bernoulli_generating_function (A := ℚ) (0 : ℚ)
  have hid : algebraMap ℚ ℚ = RingHom.id ℚ := by simp
  have hmk : (PowerSeries.mk fun n => (Polynomial.aeval (0:ℚ))
      ((1/(n.factorial:ℚ)) • Polynomial.bernoulli n))
      = PowerSeries.mk fun n => (bernoulli n : ℚ) / (n.factorial : ℚ) := by
    apply PowerSeries.ext_iff.mpr
    intro n
    simp only [PowerSeries.coeff_mk]
    rw [map_smul, Polynomial.aeval_def, hid, Polynomial.eval₂_id,
      Polynomial.bernoulli_eval_zero]
    simp [smul_eq_mul, div_eq_mul_inv]
    ring
  have hres : (PowerSeries.rescale (0:ℚ)) (PowerSeries.exp ℚ) = 1 := by
    apply PowerSeries.ext_iff.mpr
    intro n
    simp
  rw [hmk, hres, mul_one] at h
  exact h

private theorem hexp_coeff (n : ℕ) :
    (PowerSeries.coeff n) (PowerSeries.exp ℚ) = 1 / ((n.factorial : ℕ) : ℚ) := by
  rw [PowerSeries.coeff_exp]
  have hid : algebraMap ℚ ℚ = RingHom.id ℚ := by simp
  rw [hid, RingHom.id_apply]

private theorem rescale_two_egf :
    (PowerSeries.rescale (2:ℚ))
        (PowerSeries.mk fun n => (bernoulli n : ℚ) / (n.factorial : ℚ)) *
      ((PowerSeries.rescale (2:ℚ)) (PowerSeries.exp ℚ) - 1)
      = PowerSeries.C 2 * PowerSeries.X := by
  have h := congrArg (fun f => (PowerSeries.rescale (2:ℚ)) f) bernoulli_egf
  simp only [map_mul, map_sub, map_one, PowerSeries.rescale_X] at h
  exact h

private theorem rescale_two_exp :
    (PowerSeries.rescale (2:ℚ)) (PowerSeries.exp ℚ) = (PowerSeries.exp ℚ) ^ 2 := by
  apply PowerSeries.ext_iff.mpr
  intro n
  rw [PowerSeries.coeff_rescale, sq, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [hexp_coeff]
  have hfact : (((n.factorial : ℕ)) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hsum : ∑ k ∈ Finset.range (n+1), (1 / ((k.factorial : ℕ) : ℚ)) *
      (1 / (((n-k).factorial : ℕ) : ℚ)) = (2:ℚ)^n / ((n.factorial : ℕ) : ℚ) := by
    rw [eq_div_iff hfact, Finset.sum_mul]
    have h2 : ∑ k ∈ Finset.range (n+1), ((n.choose k : ℕ) : ℚ) = (2:ℚ)^n := by
      exact_mod_cast Nat.sum_range_choose n
    rw [← h2]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have e := Nat.choose_mul_factorial_mul_factorial hkn
    have ecast : ((n.choose k : ℕ) : ℚ) *
        ((((k.factorial : ℕ)) : ℚ) * ((((n-k).factorial : ℕ)) : ℚ)) =
        (((n.factorial : ℕ)) : ℚ) := by
      rw [← mul_assoc]
      exact_mod_cast e
    have hk0 : (((k.factorial : ℕ)) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero k
    have hnk0 : ((((n-k).factorial : ℕ)) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (n-k)
    have hD : (((k.factorial : ℕ)) : ℚ) * ((((n-k).factorial : ℕ)) : ℚ) ≠ 0 :=
      mul_ne_zero hk0 hnk0
    rw [div_mul_div_comm, one_mul, div_mul_eq_mul_div, one_mul, div_eq_iff hD]
    exact ecast.symm
  rw [Nat.succ_eq_add_one]
  have hfin : (2:ℚ)^n * (1/((n.factorial:ℕ):ℚ)) = (2:ℚ)^n / ((n.factorial:ℕ):ℚ) := by
    ring
  rw [hfin, ← hsum]

private theorem rescale_two_exp_sub_one :
    (PowerSeries.rescale (2:ℚ)) (PowerSeries.exp ℚ) - 1
      = (PowerSeries.exp ℚ - 1) * (PowerSeries.exp ℚ + 1) := by
  rw [rescale_two_exp]; ring

private theorem e2_mul_add_one :
    (PowerSeries.rescale (2:ℚ))
        (PowerSeries.mk fun n => (bernoulli n : ℚ) / (n.factorial : ℚ)) *
      (PowerSeries.exp ℚ + 1)
      = PowerSeries.C 2 *
        (PowerSeries.mk fun n => (bernoulli n : ℚ) / (n.factorial : ℚ)) := by
  have hne : PowerSeries.exp ℚ - 1 ≠ 0 := by
    intro hcon
    have h1 := congrArg (PowerSeries.coeff 1) hcon
    simp only [map_sub, hexp_coeff, PowerSeries.coeff_one] at h1
    norm_num at h1
  have hzero : ((PowerSeries.rescale (2:ℚ))
        (PowerSeries.mk fun n => (bernoulli n : ℚ) / (n.factorial : ℚ)) *
      (PowerSeries.exp ℚ + 1)
      - PowerSeries.C 2 *
        (PowerSeries.mk fun n => (bernoulli n : ℚ) / (n.factorial : ℚ))) *
      (PowerSeries.exp ℚ - 1) = 0 := by
    linear_combination rescale_two_egf
      - ((PowerSeries.rescale (2:ℚ))
          (PowerSeries.mk fun n => (bernoulli n : ℚ) / (n.factorial : ℚ))) *
        rescale_two_exp_sub_one
      - (PowerSeries.C 2) * bernoulli_egf
  have hsub := (mul_eq_zero.mp hzero).resolve_right hne
  exact sub_eq_zero.mp hsub

private theorem key_mul :
    (PowerSeries.mk fun n => ((1-(2:ℚ)^n)*(bernoulli n:ℚ))/(n.factorial:ℚ)) *
      (PowerSeries.exp ℚ + 1) = PowerSeries.X := by
  have hA : (PowerSeries.mk fun n => ((1-(2:ℚ)^n)*(bernoulli n:ℚ))/(n.factorial:ℚ))
      = (PowerSeries.mk fun n => (bernoulli n:ℚ)/(n.factorial:ℚ))
        - (PowerSeries.rescale (2:ℚ))
          (PowerSeries.mk fun n => (bernoulli n:ℚ)/(n.factorial:ℚ)) := by
    apply PowerSeries.ext_iff.mpr
    intro n
    simp only [PowerSeries.coeff_mk, map_sub, PowerSeries.coeff_rescale]
    ring
  have hsplit : PowerSeries.exp ℚ + 1 = (PowerSeries.exp ℚ - 1) + 2 := by ring
  have hb2 : (PowerSeries.mk fun n => (bernoulli n:ℚ)/(n.factorial:ℚ)) * 2
      = PowerSeries.C 2 *
        (PowerSeries.mk fun n => (bernoulli n:ℚ)/(n.factorial:ℚ)) := by
    rw [show (2 : PowerSeries ℚ) = PowerSeries.C 2 from (map_ofNat _ _).symm]
    ring
  rw [hA, hsplit, sub_mul, mul_add, bernoulli_egf, ← hsplit, e2_mul_add_one, hb2,
    add_sub_cancel_right]

private theorem bernoulli_weighted_sum (m : ℕ) :
    (∑ n ∈ Finset.range m, ((m.choose n : ℚ) * ((1 - (2:ℚ)^n) * bernoulli n)))
      + 2 * ((1 - (2:ℚ)^m) * bernoulli m)
      = if m = 1 then (1:ℚ) else 0 := by
  have hcoeff : ∀ j : ℕ, (PowerSeries.coeff j) (PowerSeries.exp ℚ + 1)
      = 1/(((j.factorial:ℕ)):ℚ) + (if j = 0 then (1:ℚ) else 0) := by
    intro j
    rw [map_add, hexp_coeff, PowerSeries.coeff_one]
  have hA : ∀ k : ℕ, (PowerSeries.coeff k)
      (PowerSeries.mk fun n => ((1-(2:ℚ)^n)*(bernoulli n:ℚ))/(n.factorial:ℚ))
      = (((1-(2:ℚ)^k)*(bernoulli k:ℚ)))/(((k.factorial:ℕ)):ℚ) :=
    fun k => PowerSeries.coeff_mk k _
  have h := congrArg (PowerSeries.coeff m) key_mul
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, PowerSeries.coeff_X] at h
  simp only [hA, hcoeff] at h
  rw [Nat.succ_eq_add_one, Finset.sum_range_succ] at h
  rw [Nat.sub_self] at h
  simp only [ite_true] at h
  have hfac0 : (1:ℚ) / ((((0:ℕ).factorial : ℕ)) : ℚ) = 1 := by norm_num
  rw [hfac0] at h
  simp only [mul_add, Finset.sum_add_distrib] at h
  have hif : ∀ k ∈ Finset.range m, (if m - k = 0 then (1:ℚ) else 0) = 0 := by
    intro k hk
    have hlt : k < m := Finset.mem_range.mp hk
    have hne : m - k ≠ 0 := by omega
    simp only [hne, ite_false]
  have hzero : ∑ k ∈ Finset.range m,
      ((((1-(2:ℚ)^k)*(bernoulli k:ℚ)))/(((k.factorial:ℕ)):ℚ)) *
        (if m - k = 0 then (1:ℚ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [hif k hk, mul_zero]
  rw [hzero, add_zero] at h
  have hfact : (((m.factorial : ℕ)) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero m
  have hmul := congrArg (fun x : ℚ => x * (((m.factorial : ℕ)) : ℚ)) h
  simp only [add_mul] at hmul
  rw [Finset.sum_mul] at hmul
  have hterm : ∀ k ∈ Finset.range m,
      (((((1-(2:ℚ)^k)*(bernoulli k:ℚ)))/(((k.factorial:ℕ)):ℚ)) *
        (1/((((m-k).factorial:ℕ)):ℚ))) * (((m.factorial : ℕ)) : ℚ)
      = ((m.choose k:ℕ):ℚ) * (((1-(2:ℚ)^k)*(bernoulli k:ℚ))) := by
    intro k hk
    have hkm : k ≤ m := Nat.le_of_lt (Finset.mem_range.mp hk)
    have e := Nat.choose_mul_factorial_mul_factorial hkm
    have ecast : ((m.choose k:ℕ):ℚ) *
        ((((k.factorial:ℕ)):ℚ) * ((((m-k).factorial:ℕ)):ℚ)) =
        (((m.factorial : ℕ)) : ℚ) := by
      rw [← mul_assoc]
      exact_mod_cast e
    have hk0 : ((((k.factorial:ℕ)):ℚ)) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero k
    have hmk0 : ((((m-k).factorial:ℕ)):ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (m-k)
    have hD : ((((k.factorial:ℕ)):ℚ)) * ((((m-k).factorial:ℕ)):ℚ) ≠ 0 :=
      mul_ne_zero hk0 hmk0
    have hX : (((1-(2:ℚ)^k)*(bernoulli k:ℚ))/(((k.factorial:ℕ)):ℚ)) *
        (1/((((m-k).factorial:ℕ)):ℚ))
        = (((1-(2:ℚ)^k)*(bernoulli k:ℚ))) /
          (((((k.factorial:ℕ)):ℚ)) * ((((m-k).factorial:ℕ)):ℚ)) := by
      rw [div_mul_div_comm, mul_one]
    rw [hX, div_mul_eq_mul_div, div_eq_iff hD]
    linear_combination -((((1-(2:ℚ)^k)*(bernoulli k:ℚ)))) * ecast
  rw [Finset.sum_congr rfl hterm] at hmul
  have hAm : ((((1-(2:ℚ)^m)*(bernoulli m:ℚ)))/(((m.factorial:ℕ)):ℚ)) * 1 *
      (((m.factorial : ℕ)) : ℚ)
      + ((((1-(2:ℚ)^m)*(bernoulli m:ℚ)))/(((m.factorial:ℕ)):ℚ)) * 1 *
        (((m.factorial : ℕ)) : ℚ)
      = 2 * (((1-(2:ℚ)^m)*(bernoulli m:ℚ))) := by
    have e1 : ((((1-(2:ℚ)^m)*(bernoulli m:ℚ)))/(((m.factorial:ℕ)):ℚ)) * 1 *
        (((m.factorial : ℕ)) : ℚ)
        = (((1-(2:ℚ)^m)*(bernoulli m:ℚ))) := by
      rw [mul_one, div_mul_cancel₀ _ hfact]
    rw [e1]
    ring
  rw [hAm] at hmul
  have hRHS : (if m = 1 then (1:ℚ) else 0) * (((m.factorial : ℕ)) : ℚ)
      = (if m = 1 then (1:ℚ) else 0) := by
    split_ifs with hm
    · subst hm
      norm_num
    · rw [zero_mul]
  rw [hRHS] at hmul
  exact hmul

private theorem bernoulli_weighted_sum_real (m : ℕ) :
    (∑ n ∈ Finset.range m, ((m.choose n : ℝ) * ((1 - (2:ℝ)^n) * (bernoulli n : ℝ))))
      + 2 * ((1 - (2:ℝ)^m) * (bernoulli m : ℝ))
      = if m = 1 then (1:ℝ) else 0 := by
  have h := bernoulli_weighted_sum m
  have hcast : ((((∑ n ∈ Finset.range m,
      ((m.choose n : ℚ) * ((1 - (2:ℚ)^n) * bernoulli n)))
      + 2 * ((1 - (2:ℚ)^m) * bernoulli m) : ℚ)) : ℝ)
      = (∑ n ∈ Finset.range m, ((m.choose n : ℝ) * ((1 - (2:ℝ)^n) * (bernoulli n : ℝ))))
      + 2 * ((1 - (2:ℝ)^m) * (bernoulli m : ℝ)) := by
    push_cast
    ring
  have hRHS : ((((if m = 1 then (1:ℚ) else 0) : ℚ)) : ℝ)
      = (if m = 1 then (1:ℝ) else 0) := by
    split_ifs with hm
    · subst hm
      norm_num
    · simp
  rw [← hcast, ← hRHS, h]

private theorem iterate_derivative_monomial (c : ℝ) (k n : ℕ) :
    (Polynomial.derivative^[n]) (Polynomial.monomial k c)
      = if n ≤ k then Polynomial.monomial (k-n) (c * (k.descFactorial n : ℝ))
        else 0 := by
  induction n with
  | zero =>
    simp [Nat.descFactorial_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    by_cases h1 : n ≤ k
    · by_cases h2 : n + 1 ≤ k
      · rw [ite_eq_left h1, ite_eq_left h2, Polynomial.derivative_monomial]
        have hsub : k - (n+1) = (k - n) - 1 := by omega
        rw [hsub]
        congr 1
        have hdesc : k.descFactorial (n+1) = (k-n) * k.descFactorial n :=
          Nat.descFactorial_succ k n
        have hcast : ((k.descFactorial (n+1) : ℕ) : ℝ)
            = ((k-n : ℕ):ℝ) * ((k.descFactorial n : ℕ):ℝ) := by
          exact_mod_cast hdesc
        rw [hcast]
        ring
      · have hnk : n = k := by omega
        rw [ite_eq_left h1]
        rw [hnk]
        have h3 : ¬ k + 1 ≤ k := by omega
        rw [ite_eq_right h3]
        have hkk : k - k = 0 := Nat.sub_self k
        rw [hkk, Polynomial.monomial_zero_left, Polynomial.derivative_C]
    · have h3 : ¬ n + 1 ≤ k := by omega
      rw [ite_eq_right h1, ite_eq_right h3, map_zero]

private theorem iterate_derivative_add (p q : ℝ[X]) (n : ℕ) :
    (Polynomial.derivative^[n]) (p + q)
      = (Polynomial.derivative^[n]) p + (Polynomial.derivative^[n]) q := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_add]

private theorem coeff_finset_sum (s : Finset ℕ) (f : ℕ → ℝ[X]) (j : ℕ) :
    (∑ n ∈ s, f n).coeff j = ∑ n ∈ s, (f n).coeff j := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx, Polynomial.coeff_add, ih]

private theorem expansion_eq_sum_range (a : ℕ → ℝ) (h : ℝ) (phi : ℝ[X]) (D : ℕ)
    (hD : phi.natDegree + 1 ≤ D) :
    chapter5DerivativeExpansion a h phi
      = ∑ n ∈ Finset.range D,
        Polynomial.C (a n * h ^ n) * (Polynomial.derivative^[n]) phi := by
  unfold chapter5DerivativeExpansion
  have hsub : Finset.range (phi.natDegree + 1) ⊆ Finset.range D := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  apply Finset.sum_subset hsub
  intro n _ hn
  have hlt : phi.natDegree < n := by
    have hmem : n ∉ Finset.range (phi.natDegree + 1) := hn
    simp only [Finset.mem_range, not_lt] at hmem
    omega
  rw [Polynomial.iterate_derivative_eq_zero hlt, mul_zero]

private theorem expansion_add (a : ℕ → ℝ) (h : ℝ) (p q : ℝ[X]) :
    chapter5DerivativeExpansion a h (p + q)
      = chapter5DerivativeExpansion a h p + chapter5DerivativeExpansion a h q := by
  have hD : (p + q).natDegree + 1 ≤ max (p.natDegree + 1) (q.natDegree + 1) := by
    have hle := Polynomial.natDegree_add_le p q
    omega
  rw [expansion_eq_sum_range a h (p + q) _ hD,
    expansion_eq_sum_range a h p _ (Nat.le_max_left _ _),
    expansion_eq_sum_range a h q _ (Nat.le_max_right _ _),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [iterate_derivative_add, mul_add]

private theorem descFactorial_eq_choose_mul_factorial (k n : ℕ) (h : n ≤ k) :
    k.descFactorial n = k.choose n * n.factorial := by
  have e := Nat.choose_mul_factorial_mul_factorial h
  have ddvd : (k-n).factorial ∣ k.factorial :=
    Nat.factorial_dvd_factorial (Nat.sub_le k n)
  have d : k.descFactorial n * (k-n).factorial = k.factorial := by
    rw [Nat.descFactorial_eq_div h, Nat.div_mul_cancel ddvd]
  have hne : (k-n).factorial ≠ 0 := Nat.factorial_ne_zero _
  exact mul_right_cancel₀ hne (d.trans e.symm)

private theorem choose_mul_choose_eq (k n j : ℕ) (hjn : j + n ≤ k) :
    ((k.choose n : ℕ):ℝ) * (((k-n).choose j : ℕ):ℝ)
      = ((k.choose j : ℕ):ℝ) * ((((k-j).choose n : ℕ)):ℝ) := by
  have hnk : n ≤ k := by omega
  have hjkn : j ≤ k - n := by omega
  have hjk : j ≤ k := by omega
  have hnkj : n ≤ k - j := by omega
  have hG : k - n - j = (k - j) - n := by omega
  have e1 := Nat.choose_mul_factorial_mul_factorial hnk
  have e2 := Nat.choose_mul_factorial_mul_factorial hjkn
  have e3 := Nat.choose_mul_factorial_mul_factorial hjk
  have e4 := Nat.choose_mul_factorial_mul_factorial hnkj
  have g1 : ((k.choose n : ℕ):ℝ) * ((((n.factorial:ℕ)):ℝ)) * ((((k-n).factorial:ℕ)):ℝ)
      = ((((k.factorial:ℕ)):ℝ)) := by
    exact_mod_cast e1
  have g2 : (((k-n).choose j : ℕ):ℝ) *
      (((((j.factorial:ℕ)):ℝ)) * ((((k-n-j).factorial:ℕ)):ℝ))
      = ((((k-n).factorial:ℕ)):ℝ) := by
    rw [← mul_assoc]
    exact_mod_cast e2
  have g3 : ((k.choose j : ℕ):ℝ) * (((((j.factorial:ℕ)):ℝ)) * ((((k-j).factorial:ℕ)):ℝ))
      = ((((k.factorial:ℕ)):ℝ)) := by
    rw [← mul_assoc]
    exact_mod_cast e3
  have g4 : ((((k-j).choose n : ℕ)):ℝ) *
      (((((n.factorial:ℕ)):ℝ)) * ((((k-n-j).factorial:ℕ)):ℝ))
      = ((((k-j).factorial:ℕ)):ℝ) := by
    rw [← mul_assoc, hG]
    exact_mod_cast e4
  have hn1 : ((((n.factorial:ℕ)):ℝ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hj1 : (((((j.factorial:ℕ)):ℝ))) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero j
  have hg1 : ((((k-n-j).factorial:ℕ)):ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  have hN : ((((n.factorial:ℕ)):ℝ)) * (((((j.factorial:ℕ)):ℝ)) *
      ((((k-n-j).factorial:ℕ)):ℝ)) ≠ 0 :=
    mul_ne_zero hn1 (mul_ne_zero hj1 hg1)
  apply mul_right_cancel₀ hN
  have key1 : (((k.choose n : ℕ):ℝ)) * ((((k-n).choose j : ℕ):ℝ)) *
      (((((n.factorial:ℕ)):ℝ)) * (((((j.factorial:ℕ)):ℝ)) *
        ((((k-n-j).factorial:ℕ)):ℝ)))
      = ((((k.factorial:ℕ)):ℝ)) := by
    linear_combination g1 + ((((k.choose n : ℕ):ℝ)) * ((((n.factorial:ℕ)):ℝ))) * g2
  have key2 : ((k.choose j : ℕ):ℝ) * ((((k-j).choose n : ℕ)):ℝ) *
      (((((n.factorial:ℕ)):ℝ)) * (((((j.factorial:ℕ)):ℝ)) *
        ((((k-n-j).factorial:ℕ)):ℝ)))
      = ((((k.factorial:ℕ)):ℝ)) := by
    linear_combination g3 + (((k.choose j : ℕ):ℝ) * ((((j.factorial:ℕ)):ℝ))) * g4
  linear_combination key1 - key2

private theorem descFactorial_mul_choose (k n j : ℕ) (hjn : j + n ≤ k) :
    (((k.descFactorial n : ℕ)):ℝ) * ((((k-n).choose j : ℕ)):ℝ)
      = (((k.choose j : ℕ)):ℝ) * ((((k-j).descFactorial n : ℕ)):ℝ) := by
  have hnk : n ≤ k := by omega
  have hnkj : n ≤ k - j := by omega
  rw [descFactorial_eq_choose_mul_factorial k n hnk,
    descFactorial_eq_choose_mul_factorial (k-j) n hnkj]
  push_cast
  have hne : ((((n.factorial:ℕ)):ℝ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp
  rw [choose_mul_choose_eq k n j hjn]

private theorem a0_mul_descFactorial (m n : ℕ) (h : n ≤ m) :
    chapter5Entry1PlusCoeff n * (((m.descFactorial n : ℕ)):ℝ)
      = (1 - (2:ℝ)^n) * (bernoulli n : ℝ) * (((m.choose n : ℕ)):ℝ) := by
  unfold chapter5Entry1PlusCoeff
  rw [descFactorial_eq_choose_mul_factorial m n h]
  push_cast
  have hne : ((((n.factorial:ℕ)):ℝ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp

private theorem shift_pow_coeff (h : ℝ) (m j : ℕ) :
    ((Polynomial.X + Polynomial.C h : ℝ[X])^m).coeff j
      = if j ≤ m then (((m.choose j : ℕ)):ℝ) * h^(m-j) else 0 := by
  rw [add_pow]
  rw [coeff_finset_sum]
  have hmono : ∀ i : ℕ, Polynomial.X ^ i * Polynomial.C h ^ (m - i) *
      (((m.choose i : ℕ)):ℝ[X])
      = Polynomial.C (h^(m-i) * (((m.choose i : ℕ)):ℝ)) * Polynomial.X ^ i := by
    intro i
    rw [← Polynomial.C_pow, ← map_natCast (Polynomial.C) _, mul_assoc, Polynomial.C_mul,
      mul_comm]
  have hterm : ∀ i ∈ Finset.range (m+1),
      (Polynomial.X ^ i * Polynomial.C h ^ (m - i) * (((m.choose i : ℕ)):ℝ[X])).coeff j
        = (if j = i then (h^(m-i) * (((m.choose i : ℕ)):ℝ)) else 0) := by
    intro i _
    rw [hmono i, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
  have hval : h^(m-j) * (((m.choose j : ℕ)):ℝ) = (((m.choose j : ℕ)):ℝ) * h^(m-j) := by
    ring
  rw [hval]
  by_cases hjm : j ≤ m
  · rw [ite_eq_left hjm, ite_eq_left (Finset.mem_range.mpr (by omega : j < m + 1))]
  · rw [ite_eq_right hjm, ite_eq_right (by
      simp only [Finset.mem_range, not_lt] at hjm ⊢
      omega)]

private theorem ite_deriv_monomial_coeff (c : ℝ) (k j n : ℕ) (hjk : j ≤ k) (hnk : n ≤ k) :
    ((Polynomial.derivative^[n]) (Polynomial.monomial k c)).coeff j
      = if n = k - j then c * (((k.descFactorial (k-j) : ℕ)):ℝ) else 0 := by
  rw [iterate_derivative_monomial c k n]
  by_cases hn : n = k - j
  · subst hn
    rw [ite_eq_left (Nat.sub_le k j), Nat.sub_sub_self hjk, Polynomial.coeff_monomial,
      ite_eq_left (rfl : j = j), ite_eq_left (rfl : k - j = k - j)]
  · rw [ite_eq_right hn, ite_eq_left hnk, Polynomial.coeff_monomial,
      ite_eq_right (by omega : ¬ k - n = j)]

private theorem expansion_monomial_coeff (c h : ℝ) (k j : ℕ) (hjk : j ≤ k) :
    (chapter5DerivativeExpansion chapter5Entry1PlusCoeff h
      (Polynomial.monomial k c)).coeff j
      = chapter5Entry1PlusCoeff (k-j) * h^(k-j) *
        (c * (((k.descFactorial (k-j) : ℕ)):ℝ)) := by
  have hle : (Polynomial.monomial k c).natDegree ≤ k :=
    Polynomial.natDegree_monomial_le c
  have hEform := expansion_eq_sum_range chapter5Entry1PlusCoeff h
    (Polynomial.monomial k c) (k+1) (by omega)
  rw [hEform, coeff_finset_sum]
  have hterm : ∀ n ∈ Finset.range (k+1),
      (Polynomial.C (chapter5Entry1PlusCoeff n * h^n) *
        ((Polynomial.derivative^[n]) (Polynomial.monomial k c))).coeff j
      = (if n = k-j then (chapter5Entry1PlusCoeff n * h^n *
        (c * (((k.descFactorial n : ℕ)):ℝ))) else 0) := by
    intro n hn
    have hnk : n ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    rw [Polynomial.coeff_C_mul, ite_deriv_monomial_coeff c k j n hjk hnk]
    by_cases hn2 : n = k - j
    · subst hn2
      rw [ite_eq_left (rfl : k - j = k - j), ite_eq_left (rfl : k - j = k - j)]
    · rw [ite_eq_right hn2, ite_eq_right hn2, mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq',
    ite_eq_left (Finset.mem_range.mpr (by omega : k - j < k + 1))]

private theorem shift_expansion_form (c h : ℝ) (k : ℕ) :
    chapter5PolynomialShift h (chapter5DerivativeExpansion chapter5Entry1PlusCoeff h
      (Polynomial.monomial k c))
      = ∑ n ∈ Finset.range (k+1), Polynomial.C (chapter5Entry1PlusCoeff n * h^n) *
        (((Polynomial.derivative^[n]) (Polynomial.monomial k c)).comp
          (Polynomial.X + Polynomial.C h)) := by
  have hle : (Polynomial.monomial k c).natDegree ≤ k :=
    Polynomial.natDegree_monomial_le c
  have hEform := expansion_eq_sum_range chapter5Entry1PlusCoeff h
    (Polynomial.monomial k c) (k+1) (by omega)
  rw [chapter5PolynomialShift_eq_taylor, hEform, map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [Polynomial.taylor_apply, Polynomial.C_mul_comp]

private theorem shift_monomial_coeff_term (c h : ℝ) (k j n : ℕ)
    (hnk : n ≤ k) (hjk : j ≤ k) :
    (Polynomial.C (chapter5Entry1PlusCoeff n * h ^ n) *
      (((Polynomial.derivative^[n]) (Polynomial.monomial k c)).comp
        (Polynomial.X + Polynomial.C h))).coeff j
      = if n ≤ k - j then
          (chapter5Entry1PlusCoeff n * h^n * (c * (((k.descFactorial n : ℕ)):ℝ))) *
            (((((k-n).choose j : ℕ)):ℝ) * h^(k-n-j))
        else 0 := by
  rw [iterate_derivative_monomial c k n, ite_eq_left hnk, Polynomial.monomial_comp]
  have hC : Polynomial.C (chapter5Entry1PlusCoeff n * h ^ n) *
      (Polynomial.C (c * (((k.descFactorial n : ℕ)):ℝ)) * (Polynomial.X + Polynomial.C h)^(k-n))
      = Polynomial.C (chapter5Entry1PlusCoeff n * h^n * (c * (((k.descFactorial n : ℕ)):ℝ))) *
        (Polynomial.X + Polynomial.C h)^(k-n) := by
    rw [← mul_assoc, ← Polynomial.C_mul]
  rw [hC, Polynomial.coeff_C_mul, shift_pow_coeff h (k-n) j]
  by_cases hQ : n ≤ k - j
  · have hP : j ≤ k - n := by omega
    rw [ite_eq_left hP, ite_eq_left hQ]
  · have hP : ¬ j ≤ k - n := by omega
    rw [ite_eq_right hP, ite_eq_right hQ, mul_zero]

private theorem shift_expansion_monomial_coeff (c h : ℝ) (k j : ℕ) (hjk : j ≤ k) :
    (chapter5PolynomialShift h (chapter5DerivativeExpansion chapter5Entry1PlusCoeff h
      (Polynomial.monomial k c))).coeff j
      = ∑ n ∈ Finset.range (k-j+1),
        (chapter5Entry1PlusCoeff n * h^n * (c * (((k.descFactorial n : ℕ)):ℝ))) *
          (((((k-n).choose j : ℕ)):ℝ) * h^(k-n-j)) := by
  rw [shift_expansion_form, coeff_finset_sum]
  have hterm : ∀ n ∈ Finset.range (k+1),
      (Polynomial.C (chapter5Entry1PlusCoeff n * h ^ n) *
        (((Polynomial.derivative^[n]) (Polynomial.monomial k c)).comp
          (Polynomial.X + Polynomial.C h))).coeff j
      = if n ≤ k - j then
          (chapter5Entry1PlusCoeff n * h^n * (c * (((k.descFactorial n : ℕ)):ℝ))) *
            (((((k-n).choose j : ℕ)):ℝ) * h^(k-n-j))
        else 0 := by
    intro n hn
    have hnk : n ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    exact shift_monomial_coeff_term c h k j n hnk hjk
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  have hfil : Finset.filter (fun n => n ≤ k - j) (Finset.range (k+1))
      = Finset.range (k-j+1) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hfil]

private theorem shift_term_factor (c h : ℝ) (k j n : ℕ) (hjk : j ≤ k) (hnm : n ≤ k - j) :
    (chapter5Entry1PlusCoeff n * h^n * (c * (((k.descFactorial n : ℕ)):ℝ))) *
        (((((k-n).choose j : ℕ)):ℝ) * h^(k-n-j))
      = c * h^(k-j) * (((k.choose j : ℕ)):ℝ) *
        (((((k-j).choose n : ℕ)):ℝ) * (((1-(2:ℝ)^n) * (bernoulli n : ℝ)))) := by
  have hjn : j + n ≤ k := by omega
  have e1 := descFactorial_mul_choose k n j hjn
  have e2 := a0_mul_descFactorial (k-j) n hnm
  have e3 : h^n * h^(k-n-j) = h^(k-j) := by
    have hnm2 : n + (k - n - j) = k - j := by omega
    rw [← pow_add, hnm2]
  linear_combination
    (c * h^n * h^(k-n-j) * chapter5Entry1PlusCoeff n) * e1 +
    (c * h^n * h^(k-n-j) * (((k.choose j : ℕ)):ℝ)) * e2 +
    (c * (((k.choose j : ℕ)):ℝ) * (((1-(2:ℝ)^n) * (bernoulli n : ℝ)) *
      ((((k-j).choose n : ℕ)):ℝ))) * e3

private theorem expansion_monomial_value (c h : ℝ) (k j : ℕ) (hjk : j ≤ k) :
    chapter5Entry1PlusCoeff (k-j) * h^(k-j) *
        (c * (((k.descFactorial (k-j) : ℕ)):ℝ))
      = c * h^(k-j) * (((k.choose j : ℕ)):ℝ) *
        ((1-(2:ℝ)^(k-j)) * (bernoulli (k-j) : ℝ)) := by
  have hmj : k - j ≤ k := Nat.sub_le k j
  have d1 : (((k.descFactorial (k-j) : ℕ)):ℝ)
      = (((k.choose (k-j) : ℕ)):ℝ) * ((((k-j).factorial : ℕ)):ℝ) := by
    exact_mod_cast descFactorial_eq_choose_mul_factorial k (k-j) hmj
  have d2 : (((k.choose (k-j) : ℕ)):ℝ) = (((k.choose j : ℕ)):ℝ) := by
    have hN : ((((k-j).factorial : ℕ)):ℝ) * ((((j.factorial : ℕ)):ℝ)) ≠ 0 := by
      apply mul_ne_zero <;> exact_mod_cast Nat.factorial_ne_zero _
    apply mul_right_cancel₀ hN
    have f1 := Nat.choose_mul_factorial_mul_factorial (show k - j ≤ k by omega)
    have f2 := Nat.choose_mul_factorial_mul_factorial hjk
    have e1 : ((k.choose (k-j) : ℕ):ℝ) * ((((k-j).factorial : ℕ)):ℝ) *
        ((((j.factorial : ℕ)):ℝ)) = ((((k.factorial : ℕ)):ℝ)) := by
      have hss : k - (k - j) = j := Nat.sub_sub_self hjk
      rw [hss] at f1
      exact_mod_cast f1
    have e2 : ((k.choose j : ℕ):ℝ) * ((((j.factorial : ℕ)):ℝ)) *
        ((((k-j).factorial : ℕ)):ℝ) = ((((k.factorial : ℕ)):ℝ)) := by
      exact_mod_cast f2
    linear_combination e1 - e2
  have hne : ((((k-j).factorial : ℕ)):ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  have d3 : chapter5Entry1PlusCoeff (k-j) * ((((k-j).factorial : ℕ)):ℝ)
      = ((1-(2:ℝ)^(k-j)) * (bernoulli (k-j) : ℝ)) := by
    unfold chapter5Entry1PlusCoeff
    rw [div_mul_cancel₀ _ hne]
  linear_combination (h^(k-j) * c) *
    (((((k.choose (k-j):ℕ)):ℝ)) * d3 + chapter5Entry1PlusCoeff (k-j) * d1 +
      (((1-(2:ℝ)^(k-j)) * (bernoulli (k-j):ℝ))) * d2)

private theorem choose_succ_self_cast (k j : ℕ) (hj1 : j + 1 = k) (hjk : j ≤ k) :
    (((k.choose j : ℕ)):ℝ) = (((k : ℕ)):ℝ) := by
  have hN : ((((j.factorial : ℕ)):ℝ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero j
  apply mul_right_cancel₀ hN
  have f2 := Nat.choose_mul_factorial_mul_factorial hjk
  have e2 : ((k.choose j:ℕ):ℝ) * ((((j.factorial:ℕ)):ℝ)) * ((((k-j).factorial:ℕ)):ℝ)
      = ((((k.factorial:ℕ)):ℝ)) := by
    exact_mod_cast f2
  have hkj1 : k - j = 1 := by omega
  rw [hkj1] at e2
  simp only [Nat.factorial_one, Nat.cast_one, mul_one] at e2
  have hfact : (((k.factorial:ℕ)):ℝ) = ((k:ℕ):ℝ) * ((((j.factorial:ℕ)):ℝ)) := by
    have hfe : k.factorial = k * j.factorial := by
      conv_lhs => rw [← hj1, Nat.factorial_succ]
      rw [hj1]
    exact_mod_cast hfe
  rw [hfact] at e2
  exact e2

private theorem monomial_case (c h : ℝ) (k : ℕ) :
    chapter5PolynomialShift h
        (chapter5DerivativeExpansion chapter5Entry1PlusCoeff h (Polynomial.monomial k c))
      + chapter5DerivativeExpansion chapter5Entry1PlusCoeff h (Polynomial.monomial k c)
      = Polynomial.C h * (Polynomial.monomial k c).derivative := by
  have hle : (Polynomial.monomial k c).natDegree ≤ k :=
    Polynomial.natDegree_monomial_le c
  have hEform := expansion_eq_sum_range chapter5Entry1PlusCoeff h
    (Polynomial.monomial k c) (k+1) (by omega)
  apply Polynomial.ext_iff.mpr
  intro j
  by_cases hjk : j ≤ k
  · have hE := expansion_monomial_coeff c h k j hjk
    have hS := shift_expansion_monomial_coeff c h k j hjk
    have hR : (Polynomial.C h * (Polynomial.monomial k c).derivative).coeff j
        = h * (if k - 1 = j then c * ((k:ℕ):ℝ) else 0) := by
      rw [Polynomial.derivative_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_monomial]
    rw [Polynomial.coeff_add, hS, hE, hR]
    have hG : ∀ n ∈ Finset.range (k-j+1),
        (chapter5Entry1PlusCoeff n * h^n * (c * (((k.descFactorial n : ℕ)):ℝ))) *
          (((((k-n).choose j : ℕ)):ℝ) * h^(k-n-j))
        = (c * h^(k-j) * (((k.choose j : ℕ)):ℝ)) *
          (((((k-j).choose n : ℕ)):ℝ) * (((1-(2:ℝ)^n) * (bernoulli n : ℝ)))) := by
      intro n hn
      have hnm : n ≤ k - j := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
      exact shift_term_factor c h k j n hjk hnm
    rw [Finset.sum_congr rfl hG, ← Finset.mul_sum, Finset.sum_range_succ]
    have hTm : ((((k-j).choose (k-j) : ℕ)):ℝ) *
          (((1-(2:ℝ)^(k-j)) * (bernoulli (k-j) : ℝ)))
        = ((1-(2:ℝ)^(k-j)) * (bernoulli (k-j) : ℝ)) := by
      rw [Nat.choose_self, Nat.cast_one, one_mul]
    rw [hTm]
    have hE2 := expansion_monomial_value c h k j hjk
    rw [hE2]
    have hF : (c * h^(k-j) * (((k.choose j : ℕ)):ℝ)) *
          ((∑ n ∈ Finset.range (k-j), (((k-j).choose n : ℕ):ℝ) *
            (((1-(2:ℝ)^n) * (bernoulli n : ℝ)))) +
            ((1-(2:ℝ)^(k-j)) * (bernoulli (k-j) : ℝ))) +
          (c * h^(k-j) * (((k.choose j : ℕ)):ℝ)) *
            ((1-(2:ℝ)^(k-j)) * (bernoulli (k-j) : ℝ))
        = (c * h^(k-j) * (((k.choose j : ℕ)):ℝ)) *
          ((∑ n ∈ Finset.range (k-j), (((k-j).choose n : ℕ):ℝ) *
            (((1-(2:ℝ)^n) * (bernoulli n : ℝ)))) +
            2 * (((1-(2:ℝ)^(k-j)) * (bernoulli (k-j) : ℝ)))) := by
      ring
    rw [hF]
    have hbern := bernoulli_weighted_sum_real (k-j)
    rw [hbern]
    by_cases hm1 : k - j = 1
    · rw [ite_eq_left hm1, mul_one]
      have hkj : k - 1 = j := by omega
      rw [ite_eq_left hkj]
      have hj1 : j + 1 = k := by omega
      rw [hm1, pow_one, choose_succ_self_cast k j hj1 hjk]
      ring
    · rw [ite_eq_right hm1, mul_zero]
      by_cases hkj : k - 1 = j
      · rw [ite_eq_left hkj]
        by_cases hk0 : k = 0
        · subst hk0
          simp
        · exfalso
          apply hm1
          omega
      · rw [ite_eq_right hkj, mul_zero]
  · have hkj : k < j := by omega
    have hE0 : (chapter5DerivativeExpansion chapter5Entry1PlusCoeff h
        (Polynomial.monomial k c)).coeff j = 0 := by
      rw [hEform, coeff_finset_sum]
      apply Finset.sum_eq_zero
      intro n hn
      have hnk : n ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
      rw [Polynomial.coeff_C_mul, iterate_derivative_monomial c k n, ite_eq_left hnk,
        Polynomial.coeff_monomial, ite_eq_right (by omega : ¬ k - n = j), mul_zero]
    have hS0 : (chapter5PolynomialShift h (chapter5DerivativeExpansion
        chapter5Entry1PlusCoeff h (Polynomial.monomial k c))).coeff j = 0 := by
      rw [shift_expansion_form c h k, coeff_finset_sum]
      apply Finset.sum_eq_zero
      intro n hn
      have hnk : n ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
      rw [iterate_derivative_monomial c k n, ite_eq_left hnk, Polynomial.monomial_comp]
      have hC : Polynomial.C (chapter5Entry1PlusCoeff n * h ^ n) *
          (Polynomial.C (c * (((k.descFactorial n : ℕ)):ℝ)) *
            (Polynomial.X + Polynomial.C h)^(k-n))
          = Polynomial.C (chapter5Entry1PlusCoeff n * h^n *
            (c * (((k.descFactorial n : ℕ)):ℝ))) *
            (Polynomial.X + Polynomial.C h)^(k-n) := by
        rw [← mul_assoc, ← Polynomial.C_mul]
      rw [hC, Polynomial.coeff_C_mul, shift_pow_coeff h (k-n) j,
        ite_eq_right (by omega : ¬ j ≤ k - n), mul_zero]
    have hR0 : (Polynomial.C h * (Polynomial.monomial k c).derivative).coeff j = 0 := by
      rw [Polynomial.derivative_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_monomial,
        ite_eq_right (by omega : ¬ k - 1 = j), mul_zero]
    rw [Polynomial.coeff_add, hS0, hE0, hR0, add_zero]

private theorem existence_part :
    ∀ (phi : ℝ[X]) (h : ℝ),
      chapter5PolynomialShift h
          (chapter5DerivativeExpansion chapter5Entry1PlusCoeff h phi) +
        chapter5DerivativeExpansion chapter5Entry1PlusCoeff h phi =
      Polynomial.C h * phi.derivative := by
  intro phi h
  induction phi using Polynomial.induction_on'
  case add p q hp hq =>
    rw [chapter5PolynomialShift_eq_taylor] at hp hq ⊢
    rw [expansion_add _ h p q, map_add, Polynomial.derivative_add, mul_add]
    linear_combination hp + hq
  case monomial n a =>
    exact monomial_case a h n

private theorem eval_finset_sum (s : Finset ℕ) (f : ℕ → ℝ[X]) (x : ℝ) :
    Polynomial.eval x (∑ n ∈ s, f n) = ∑ n ∈ s, Polynomial.eval x (f n) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert n s hn ih =>
    rw [Finset.sum_insert hn, Finset.sum_insert hn, Polynomial.eval_add, ih]

private theorem key_recurrence (a : ℕ → ℝ)
    (hP : ∀ (phi : ℝ[X]) (h : ℝ),
      chapter5PolynomialShift h (chapter5DerivativeExpansion a h phi) +
        chapter5DerivativeExpansion a h phi =
      Polynomial.C h * phi.derivative) (m : ℕ) :
    (∑ n ∈ Finset.range m, a n * (((m.descFactorial n : ℕ)):ℝ)) +
      2 * (a m * (((m.factorial : ℕ)):ℝ))
      = if m = 1 then (1:ℝ) else 0 := by
  have hdeg : (Polynomial.X^m : ℝ[X]).natDegree = m := Polynomial.natDegree_X_pow m
  have hEformX := expansion_eq_sum_range a 1 (Polynomial.X^m : ℝ[X]) (m+1) (by omega)
  have hPm := hP (Polynomial.X^m : ℝ[X]) 1
  have h0 := congrArg (Polynomial.eval 0) hPm
  simp only [Polynomial.eval_add] at h0
  have hshift : Polynomial.eval 0 (chapter5PolynomialShift 1
      (chapter5DerivativeExpansion a 1 (Polynomial.X^m : ℝ[X])))
      = Polynomial.eval 1 (chapter5DerivativeExpansion a 1 (Polynomial.X^m : ℝ[X])) := by
    rw [chapter5PolynomialShift_eq_taylor, Polynomial.taylor_eval, zero_add]
  rw [hshift] at h0
  have hE0 : Polynomial.eval 0 (chapter5DerivativeExpansion a 1 (Polynomial.X^m : ℝ[X]))
      = a m * (((m.factorial:ℕ)):ℝ) := by
    rw [hEformX, eval_finset_sum]
    have hterm : ∀ n ∈ Finset.range (m+1),
        Polynomial.eval 0 (Polynomial.C (a n * 1^n) *
          (Polynomial.derivative^[n]) (Polynomial.X^m : ℝ[X]))
        = (if n = m then a m * (((m.factorial:ℕ)):ℝ) else 0) := by
      intro n hn
      have hnm : n ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.X_pow_eq_monomial,
        iterate_derivative_monomial 1 m n, ite_eq_left hnm, Polynomial.eval_monomial]
      by_cases hn2 : n = m
      · subst hn2
        simp only [Nat.sub_self, pow_zero, mul_one, one_mul, one_pow,
          Nat.descFactorial_self, ite_true]
      · have hpos : m - n ≠ 0 := by omega
        rw [ite_eq_right hn2, zero_pow hpos, mul_zero, mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq',
      ite_eq_left (Finset.mem_range.mpr (Nat.lt_succ_self m))]
  have hE1 : Polynomial.eval 1 (chapter5DerivativeExpansion a 1 (Polynomial.X^m : ℝ[X]))
      = ∑ n ∈ Finset.range (m+1), a n * (((m.descFactorial n : ℕ)):ℝ) := by
    rw [hEformX, eval_finset_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hnm : n ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.X_pow_eq_monomial,
      iterate_derivative_monomial 1 m n, ite_eq_left hnm, Polynomial.eval_monomial]
    simp only [one_pow, one_mul, mul_one]
  have hR : Polynomial.eval 0 (Polynomial.C (1:ℝ) * (Polynomial.X^m : ℝ[X]).derivative)
      = if m = 1 then (1:ℝ) else 0 := by
    rw [Polynomial.derivative_X_pow, Polynomial.eval_mul, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    by_cases hm : m = 1
    · subst hm
      simp
    · by_cases hm0 : m = 0
      · subst hm0
        simp
      · have hpos : m - 1 ≠ 0 := by omega
        rw [ite_eq_right hm, zero_pow hpos, mul_zero, mul_zero]
  rw [hE0, hE1, hR] at h0
  rw [Finset.sum_range_succ, Nat.descFactorial_self] at h0
  linear_combination h0

private theorem uniqueness_part (a : ℕ → ℝ)
    (hP : ∀ (phi : ℝ[X]) (h : ℝ),
      chapter5PolynomialShift h (chapter5DerivativeExpansion a h phi) +
        chapter5DerivativeExpansion a h phi =
      Polynomial.C h * phi.derivative) :
    a = chapter5Entry1PlusCoeff := by
  have hex : ∀ (phi : ℝ[X]) (h : ℝ),
      chapter5PolynomialShift h
        (chapter5DerivativeExpansion chapter5Entry1PlusCoeff h phi) +
        chapter5DerivativeExpansion chapter5Entry1PlusCoeff h phi =
      Polynomial.C h * phi.derivative := existence_part
  have hQ : ∀ m : ℕ, ∀ n : ℕ, n ≤ m → a n = chapter5Entry1PlusCoeff n := by
    intro m
    induction m with
    | zero =>
      intro n hn
      have hn0 : n = 0 := by omega
      subst hn0
      have e_a := key_recurrence a hP 0
      have e_0 := key_recurrence chapter5Entry1PlusCoeff hex 0
      simp at e_a e_0
      linarith
    | succ m ih =>
      intro n hn
      by_cases hnm : n ≤ m
      · exact ih n hnm
      · have hnm' : n = m + 1 := by omega
        subst hnm'
        have e_a := key_recurrence a hP (m+1)
        have e_0 := key_recurrence chapter5Entry1PlusCoeff hex (m+1)
        have hsum : (∑ i ∈ Finset.range (m+1), a i * ((((m+1).descFactorial i : ℕ)):ℝ))
            = ∑ i ∈ Finset.range (m+1), chapter5Entry1PlusCoeff i *
              ((((m+1).descFactorial i : ℕ)):ℝ) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi_le : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
          rw [ih i hi_le]
        rw [hsum] at e_a
        have hne : (2:ℝ) * ((((m+1).factorial:ℕ)):ℝ) ≠ 0 := by
          apply mul_ne_zero
          · norm_num
          · exact_mod_cast Nat.factorial_ne_zero _
        have hsub : (2:ℝ) * ((((m+1).factorial:ℕ)):ℝ) *
            (a (m+1) - chapter5Entry1PlusCoeff (m+1)) = 0 := by
          linear_combination e_a - e_0
        have h2 := (mul_eq_zero.mp hsub).resolve_left hne
        linarith
  funext n
  exact hQ n n le_rfl

/-- Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 5.
Proves `Wanted` entry `ramanujan_part1_ch5_entry1_euleriangf`.
-/
theorem ramanujan_part1_ch5_entry1_euleriangf :
    (∀ (phi : ℝ[X]) (h : ℝ),
      chapter5PolynomialShift h
          (chapter5DerivativeExpansion chapter5Entry1PlusCoeff h phi) +
        chapter5DerivativeExpansion chapter5Entry1PlusCoeff h phi =
      Polynomial.C h * phi.derivative) ∧
    ∀ a : ℕ → ℝ,
      (∀ (phi : ℝ[X]) (h : ℝ),
        chapter5PolynomialShift h (chapter5DerivativeExpansion a h phi) +
            chapter5DerivativeExpansion a h phi =
          Polynomial.C h * phi.derivative) →
      a = chapter5Entry1PlusCoeff := by
  exact ⟨existence_part, uniqueness_part⟩

end

end Entry1Euleriangf

end MathlibExt.Analysis.Ramanujan.Part1Ch5
