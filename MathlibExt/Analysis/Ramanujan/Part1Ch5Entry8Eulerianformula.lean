/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import MathlibExt.Analysis.Ramanujan.Part1Ch5Entry4
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 5, Entry 8

Entry 8 from B. C. Berndt, *Ramanujan's Notebooks, Part I* (Springer, 1985):
evaluations of the Eulerian polynomial `chapter5Psi` at `-1` and `1`, and the
two power series for `1 / (Complex.exp z + 1)` in terms of Bernoulli numbers
and Eulerian polynomials.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch5

namespace Entry8Eulerianformula

open scoped Nat Real BigOperators Polynomial ContDiff
open Filter Finset Complex Topology Entry4
open PowerSeries

noncomputable section

def chapter5Entry8BernoulliTerm (z : ℂ) (j : ℕ) : ℂ :=
  (1 - (2 : ℂ) ^ (j + 1)) * (bernoulli (j + 1) : ℂ) * z ^ j /
    ((j + 1).factorial : ℂ)

def chapter5Entry8PsiTerm (z : ℂ) (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ n * chapter5Psi n (1 : ℂ) * z ^ n /
    ((2 : ℂ) ^ (n + 1) * (n.factorial : ℂ))

private theorem eulerian_zero : ∀ (n : ℕ), eulerianNumber n 0 = 1 := by
  intro n
  induction n with
  | zero => exact eulerianNumber.eq_1
  | succ n ih => rw [eulerianNumber.eq_3 0 n]; simp [ih]

private theorem eulerian_vanish : ∀ (n k : ℕ), n ≤ k → 1 ≤ n → eulerianNumber n k = 0 := by
  intro n
  induction n with
  | zero => intro k _ h1; omega
  | succ n ih =>
    intro k hnk _
    rw [eulerianNumber.eq_3 k n]
    have h2 : n + 1 - k = 0 := by omega
    rw [h2, zero_mul, add_zero]
    cases n with
    | zero =>
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      rw [eulerianNumber.eq_2, mul_zero]
    | succ m =>
      have h3 : eulerianNumber (m + 1) k = 0 := ih k (by omega) (by omega)
      rw [h3, mul_zero]

private theorem shift_sum_gen {R : Type*} [Semiring R] (n : ℕ) (c f : ℕ → R) :
    ∑ k ∈ range (n + 1), c k * (if k = 0 then 0 else f (k - 1)) =
    ∑ j ∈ range n, c (j + 1) * f j := by
  induction n with
  | zero => simp
  | succ n ih =>
    conv_lhs => rw [Finset.sum_range_succ]
    conv_rhs => rw [Finset.sum_range_succ]
    rw [ih, ite_eq_right (by omega : n + 1 ≠ 0), Nat.add_sub_cancel]

private theorem shift_sum (n : ℕ) (c f : ℕ → ℕ) :
    ∑ k ∈ range (n + 1), c k * (if k = 0 then 0 else f (k - 1)) =
    ∑ j ∈ range n, c (j + 1) * f j :=
  shift_sum_gen n c f

private theorem rowsum_nat (n : ℕ) :
    ∑ k ∈ range (n + 1), eulerianNumber (n + 1) k =
    (n + 1) * ∑ k ∈ range (n + 1), eulerianNumber n k := by
  have expand : ∀ k : ℕ, eulerianNumber (n + 1) k =
      (k + 1) * eulerianNumber n k +
      (n + 1 - k) * (if k = 0 then 0 else eulerianNumber n (k - 1)) :=
    fun k => eulerianNumber.eq_3 k n
  simp_rw [expand, Finset.sum_add_distrib]
  have hB : ∑ k ∈ range (n + 1),
        (n + 1 - k) * (if k = 0 then 0 else eulerianNumber n (k - 1)) =
      ∑ j ∈ range n, ((n - j) * eulerianNumber n j) := by
    rw [shift_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hsub : n + 1 - (j + 1) = n - j := by omega
    rw [hsub]
  have hC : ∑ k ∈ range n, ((k + 1) * eulerianNumber n k + (n - k) * eulerianNumber n k) =
      (n + 1) * ∑ k ∈ range n, eulerianNumber n k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
    have hkk : (k + 1) + (n - k) = n + 1 := by omega
    calc (k + 1) * eulerianNumber n k + (n - k) * eulerianNumber n k
        = ((k + 1) + (n - k)) * eulerianNumber n k := by ring
      _ = (n + 1) * eulerianNumber n k := by rw [hkk]
  have hre : (∑ k ∈ range n, (k + 1) * eulerianNumber n k) +
        (∑ j ∈ range n, (n - j) * eulerianNumber n j) =
      ∑ k ∈ range n, ((k + 1) * eulerianNumber n k + (n - k) * eulerianNumber n k) := by
    rw [Finset.sum_add_distrib]
  have hA : ∑ k ∈ range (n + 1), (k + 1) * eulerianNumber n k =
      (∑ k ∈ range n, (k + 1) * eulerianNumber n k) + (n + 1) * eulerianNumber n n := by
    rw [Finset.sum_range_succ]
  rw [hB, hA, add_right_comm, hre, hC, ← mul_add, Finset.sum_range_succ]

private theorem psi_succ_neg_one (n : ℕ) :
    chapter5Psi (n + 1) (-1 : ℂ) =
    ∑ k ∈ range (n + 1), (eulerianNumber (n + 1) k : ℂ) := by
  unfold chapter5Psi
  rw [ite_eq_right (Nat.add_one_ne_zero n)]
  apply Finset.sum_congr rfl
  intro k _
  rw [neg_neg, one_pow, mul_one]

private theorem psi_bridge (n : ℕ) :
    chapter5Psi n (-1 : ℂ) = ∑ k ∈ range (n + 1), (eulerianNumber n k : ℂ) := by
  induction n with
  | zero =>
    have hL : chapter5Psi 0 (-1 : ℂ) = 1 := by unfold chapter5Psi; simp
    rw [hL]
    simp [eulerianNumber.eq_1]
  | succ n ih =>
    rw [psi_succ_neg_one n]
    conv_rhs => rw [Finset.sum_range_succ]
    have hv : (eulerianNumber (n + 1) (n + 1) : ℂ) = 0 := by
      exact_mod_cast eulerian_vanish (n + 1) (n + 1) le_rfl (by omega)
    rw [hv, add_zero]

private theorem psi_neg_one (n : ℕ) : chapter5Psi n (-1 : ℂ) = (n.factorial : ℂ) := by
  induction n with
  | zero =>
    have hL : chapter5Psi 0 (-1 : ℂ) = 1 := by unfold chapter5Psi; simp
    rw [hL]
    simp
  | succ n ih =>
    have hr := rowsum_nat n
    have hrC : ∑ k ∈ range (n + 1), (eulerianNumber (n + 1) k : ℂ) =
        ((n + 1 : ℕ) : ℂ) * ∑ k ∈ range (n + 1), (eulerianNumber n k : ℂ) := by
      exact_mod_cast hr
    rw [psi_succ_neg_one n, hrC, ← psi_bridge n, ih, Nat.factorial_succ]
    push_cast
    ring

private noncomputable def psL : PowerSeries ℂ :=
  PowerSeries.mk fun n => (1 - (2 : ℂ) ^ (n + 1)) * (bernoulli (n + 1) : ℂ) /
      ((n + 1).factorial : ℂ)

private theorem rescale_pres_mul (a : ℂ) (f g : PowerSeries ℂ) :
    rescale a f * rescale a g = rescale a (f * g) := by
  apply PowerSeries.ext
  intro n
  rw [coeff_mul, coeff_rescale, coeff_mul]
  simp_rw [coeff_rescale]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ hij
  have hij' : i + j = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [← hij', pow_add]
  ring

private theorem hBcoeff (n : ℕ) : coeff n (bernoulliPowerSeries ℂ) =
    (bernoulli n : ℂ) / (n.factorial : ℂ) := by
  rw [bernoulliPowerSeries, coeff_mk, map_div₀]
  simp

private theorem hLcoeff (n : ℕ) : coeff n psL =
    (1 - (2 : ℂ) ^ (n + 1)) * (bernoulli (n + 1) : ℂ) / ((n + 1).factorial : ℂ) := by
  rw [psL, coeff_mk]

private theorem hE1m : PowerSeries.exp ℂ - 1 ≠ 0 := by
  intro h
  have h1 := congrArg (coeff 1) h
  simp only [map_sub] at h1
  rw [coeff_exp] at h1
  simp at h1

private theorem hXL : PowerSeries.X * psL =
    bernoulliPowerSeries ℂ - rescale (2 : ℂ) (bernoulliPowerSeries ℂ) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    rw [coeff_zero_X_mul]
    simp only [map_sub, hBcoeff, coeff_rescale, bernoulli_zero]
    simp
  | succ n =>
    rw [coeff_succ_X_mul, hLcoeff]
    simp only [map_sub, hBcoeff, coeff_rescale]
    ring

private theorem e2rescale : (PowerSeries.exp ℂ) ^ 2 =
    PowerSeries.rescale (2 : ℂ) (PowerSeries.exp ℂ) := by
  have h := PowerSeries.exp_pow_eq_rescale_exp (A := ℂ) 2
  simpa using h

private theorem hsubrescale : PowerSeries.rescale (2 : ℂ) (PowerSeries.exp ℂ - 1) =
    (PowerSeries.exp ℂ) ^ 2 - 1 := by
  rw [e2rescale]
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp
  | succ n => simp

private theorem hB2 : PowerSeries.rescale (2 : ℂ) (bernoulliPowerSeries ℂ) *
    ((PowerSeries.exp ℂ) ^ 2 - 1) = 2 * PowerSeries.X := by
  rw [← hsubrescale, rescale_pres_mul, bernoulliPowerSeries_mul_exp_sub_one,
    PowerSeries.rescale_X, map_ofNat]

private theorem hD : (bernoulliPowerSeries ℂ -
    PowerSeries.rescale (2 : ℂ) (bernoulliPowerSeries ℂ)) *
    (PowerSeries.exp ℂ + 1) = PowerSeries.X := by
  refine mul_right_cancel₀ hE1m ?_
  have e1 : ((bernoulliPowerSeries ℂ -
      PowerSeries.rescale (2 : ℂ) (bernoulliPowerSeries ℂ)) *
      (PowerSeries.exp ℂ + 1)) * (PowerSeries.exp ℂ - 1) =
      (bernoulliPowerSeries ℂ -
        PowerSeries.rescale (2 : ℂ) (bernoulliPowerSeries ℂ)) *
      ((PowerSeries.exp ℂ) ^ 2 - 1) := by ring
  have e3 : bernoulliPowerSeries ℂ * ((PowerSeries.exp ℂ) ^ 2 - 1) =
      PowerSeries.X * (PowerSeries.exp ℂ + 1) := by
    have e4 : (PowerSeries.exp ℂ) ^ 2 - 1 =
        (PowerSeries.exp ℂ - 1) * (PowerSeries.exp ℂ + 1) := by ring
    rw [e4, ← mul_assoc, bernoulliPowerSeries_mul_exp_sub_one]
  rw [e1, sub_mul, hB2, e3]
  ring

private theorem hL : psL * (PowerSeries.exp ℂ + 1) = 1 := by
  have h1 : (psL * (PowerSeries.exp ℂ + 1)) * PowerSeries.X =
      1 * PowerSeries.X := by
    have e : (psL * (PowerSeries.exp ℂ + 1)) * PowerSeries.X =
        (PowerSeries.X * psL) * (PowerSeries.exp ℂ + 1) := by ring
    rw [e, hXL, hD, one_mul]
  exact mul_right_cancel₀ PowerSeries.X_ne_zero h1

private noncomputable def auxF : ℂ → ℂ := fun x => 1 / (Complex.exp x + 1)

private noncomputable def auxG : ℂ → ℂ := fun x => Complex.exp x + 1

private theorem hev : ∀ᶠ x : ℂ in nhds 0, Complex.exp x + 1 ≠ 0 := by
  have hcont : ContinuousAt (fun x : ℂ => Complex.exp x + 1) 0 :=
    (Complex.continuous_exp.add continuous_const).continuousAt
  have hne : (fun x : ℂ => Complex.exp x + 1) 0 ≠ 0 := by simp [Complex.exp_zero]
  exact hcont.eventually_ne hne

private theorem heq : (auxF * auxG) =ᶠ[nhds (0:ℂ)] fun _ => 1 := by
  filter_upwards [hev] with x hx
  exact div_mul_cancel₀ 1 hx

private theorem hgCont : ∀ m : ℕ, ContDiffAt ℂ (↑m) auxG 0 := by
  intro m
  have hg : ContDiffAt ℂ (↑m) (fun x : ℂ => Complex.exp x + 1) 0 :=
    ContDiffAt.add Complex.contDiff_exp.contDiffAt contDiff_const.contDiffAt
  exact hg

private theorem hfCont : ∀ m : ℕ, ContDiffAt ℂ (↑m) auxF 0 := by
  intro m
  have h := ContDiffAt.div (f := fun _ : ℂ => (1:ℂ)) (g := fun x : ℂ => Complex.exp x + 1)
    (x := (0:ℂ)) (n := (↑m : WithTop ℕ∞))
    contDiff_const.contDiffAt
    (ContDiffAt.add Complex.contDiff_exp.contDiffAt contDiff_const.contDiffAt)
    (by simp [Complex.exp_zero])
  exact h

private theorem hexpfun : ∀ j : ℕ, iteratedDeriv j Complex.exp = Complex.exp := by
  intro j
  induction j with
  | zero => exact iteratedDeriv_zero
  | succ j ih => rw [iteratedDeriv_succ, ih, Complex.deriv_exp]

private theorem hgval : ∀ j : ℕ, iteratedDeriv j auxG 0 = 1 + (if j = 0 then (1:ℂ) else 0) := by
  intro j
  have h := iteratedDeriv_add (𝕜 := ℂ) (f := Complex.exp) (g := fun _ : ℂ => 1)
    Complex.contDiff_exp.contDiffAt contDiff_const.contDiffAt (n := j) (x := 0)
  have hfun : (Complex.exp + fun _ : ℂ => (1:ℂ)) = auxG := rfl
  rw [hfun, hexpfun j, Complex.exp_zero, iteratedDeriv_const] at h
  exact h

private noncomputable def auxT : PowerSeries ℂ :=
  PowerSeries.mk fun n => iteratedDeriv n auxF 0 / (n.factorial : ℂ)

private theorem hTcoeff (n : ℕ) : coeff n auxT = iteratedDeriv n auxF 0 / (n.factorial : ℂ) := by
  rw [auxT, coeff_mk]

private theorem hEcoeff (j : ℕ) : coeff j (PowerSeries.exp ℂ) = 1 / ((j.factorial : ℕ) : ℂ) := by
  rw [coeff_exp]
  simp

private theorem hScoeff (j : ℕ) : coeff j (PowerSeries.exp ℂ + 1) =
    iteratedDeriv j auxG 0 / ((j.factorial : ℕ) : ℂ) := by
  rw [hgval j]
  simp only [map_add, hEcoeff, coeff_one]
  by_cases hj : j = 0
  · subst hj
    simp
  · rw [ite_eq_right hj]
    simp

private theorem termid (n i : ℕ) (hi : i ≤ n) (d e : ℂ) :
    d / (i.factorial : ℂ) * (e / ((n - i).factorial : ℂ)) =
    ((n.choose i : ℕ) : ℂ) * d * e / (n.factorial : ℂ) := by
  have h1 : ((n.choose i : ℕ) : ℂ) * (i.factorial : ℂ) * ((n - i).factorial : ℂ) =
      (n.factorial : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  have hfi : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hfj : ((n - i).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - i)
  have hfn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero hfi hfj) hfn]
  linear_combination -(d * e) * h1

private theorem hTS : auxT * (PowerSeries.exp ℂ + 1) = 1 := by
  apply PowerSeries.ext
  intro n
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [show n.succ = n + 1 from rfl]
  simp_rw [hTcoeff, hScoeff]
  have hL := iteratedDeriv_mul (𝕜 := ℂ) (n := n) (x := 0) (f := auxF) (g := auxG)
    (hfCont n) (hgCont n)
  have hE := Filter.EventuallyEq.iteratedDeriv_eq n heq (x := (0:ℂ))
  rw [iteratedDeriv_const] at hE
  have hsum : ∑ k ∈ range (n + 1),
        (iteratedDeriv k auxF 0 / (k.factorial : ℂ) *
          (iteratedDeriv (n - k) auxG 0 / (((n - k).factorial : ℕ) : ℂ))) =
      (∑ k ∈ range (n + 1), ((n.choose k : ℕ) : ℂ) * iteratedDeriv k auxF 0 *
        iteratedDeriv (n - k) auxG 0) / (n.factorial : ℂ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    exact termid n k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) _ _
  rw [hsum, ← hL, hE, coeff_one]
  by_cases hn : n = 0
  · subst hn
    simp
  · simp only [hn, ite_false, zero_div]

private theorem hTL : auxT = psL := by
  have e1 : auxT = auxT * (psL * (PowerSeries.exp ℂ + 1)) := by rw [hL, mul_one]
  have e2 : auxT * (psL * (PowerSeries.exp ℂ + 1)) =
      (auxT * (PowerSeries.exp ℂ + 1)) * psL := by ring
  have e3 : (auxT * (PowerSeries.exp ℂ + 1)) * psL = psL := by rw [hTS, one_mul]
  rw [e1, e2, e3]

private theorem dval : ∀ j : ℕ, iteratedDeriv j auxF 0 =
    (1 - (2 : ℂ) ^ (j + 1)) * (bernoulli (j + 1) : ℂ) / ((j : ℂ) + 1) := by
  intro j
  have hcj := congrArg (coeff j) hTL
  rw [hTcoeff, hLcoeff] at hcj
  have hfj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hj1 : ((((j + 1 : ℕ))) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  have ecast : ((((j + 1 : ℕ))) : ℂ) = ((j : ℂ) + 1) := by push_cast; ring
  have hfact : (((j + 1).factorial : ℕ) : ℂ) =
      ((((j + 1 : ℕ))) : ℂ) * (j.factorial : ℂ) := by
    exact_mod_cast Nat.factorial_succ j
  rw [hfact] at hcj
  calc iteratedDeriv j auxF 0
      = (j.factorial : ℂ) * (iteratedDeriv j auxF 0 / (j.factorial : ℂ)) := by
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ hfj]
    _ = (j.factorial : ℂ) * ((1 - (2 : ℂ) ^ (j + 1)) * (bernoulli (j + 1) : ℂ) /
        (((((j + 1 : ℕ))) : ℂ) * (j.factorial : ℂ))) := by rw [hcj]
    _ = (1 - (2 : ℂ) ^ (j + 1)) * (bernoulli (j + 1) : ℂ) / (((j : ℂ)) + 1) := by
        rw [← mul_div_assoc, mul_comm (j.factorial : ℂ) _,
          mul_div_mul_right _ _ hfj, ecast]

private noncomputable def psiPoly (m : ℕ) : Polynomial ℂ :=
  ∑ k ∈ range m, Polynomial.C (eulerianNumber m k : ℂ) * (-Polynomial.X) ^ k

private theorem psiPoly_eval (m : ℕ) (p : ℂ) :
    (psiPoly (m + 1)).eval p = chapter5Psi (m + 1) p := by
  unfold chapter5Psi psiPoly
  rw [ite_eq_right (Nat.add_one_ne_zero m), Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k _
  simp

private theorem psiPoly_deriv_sum (m : ℕ) (p : ℂ) : (psiPoly m).derivative.eval p =
    ∑ k ∈ range m, (eulerianNumber m k : ℂ) * (k : ℂ) * (-1) * (-p) ^ (k - 1) := by
  unfold psiPoly
  rw [Polynomial.derivative_sum, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Polynomial.derivative_C_mul, Polynomial.derivative_pow,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_neg, Polynomial.eval_X, Polynomial.derivative_neg,
    Polynomial.derivative_X, Polynomial.eval_one]
  ring

private theorem psi_rec_sum (m : ℕ) (hm : 1 ≤ m) (p : ℂ) :
    ∑ k ∈ range (m + 1), (eulerianNumber (m + 1) k : ℂ) * (-p) ^ k =
    (1 - (m : ℂ) * p) * ∑ k ∈ range m, (eulerianNumber m k : ℂ) * (-p) ^ k +
    p * (1 + p) * ∑ k ∈ range m, (eulerianNumber m k : ℂ) * (k : ℂ) * (-1) * (-p) ^ (k - 1) := by
  have expand : ∀ k : ℕ, (eulerianNumber (m + 1) k : ℂ) * (-p) ^ k =
      (((((k + 1 : ℕ))) : ℂ) * (eulerianNumber m k : ℂ) +
        ((((m + 1 - k : ℕ))) : ℂ) *
          (if k = 0 then (0:ℂ) else (eulerianNumber m (k - 1) : ℂ))) * (-p) ^ k := by
    intro k
    have hc : (eulerianNumber (m + 1) k : ℂ) =
        ((((k + 1 : ℕ))) : ℂ) * (eulerianNumber m k : ℂ) +
          ((((m + 1 - k : ℕ))) : ℂ) *
            (if k = 0 then (0:ℂ) else (eulerianNumber m (k - 1) : ℂ)) := by
      exact_mod_cast eulerianNumber.eq_3 k m
    rw [hc]
  simp_rw [expand, add_mul]
  rw [Finset.sum_add_distrib]
  have hB : (∑ k ∈ range (m + 1), ((((m + 1 - k : ℕ))) : ℂ) *
        (if k = 0 then (0:ℂ) else (eulerianNumber m (k - 1) : ℂ)) * (-p) ^ k) =
      (∑ j ∈ range m, ((((m - j : ℕ))) : ℂ) * (eulerianNumber m j : ℂ) * (-p) ^ (j + 1)) := by
    have step1 : (∑ k ∈ range (m + 1), ((((m + 1 - k : ℕ))) : ℂ) *
          (if k = 0 then (0:ℂ) else (eulerianNumber m (k - 1) : ℂ)) * (-p) ^ k) =
        (∑ k ∈ range (m + 1), ((((m + 1 - k : ℕ))) : ℂ) * (-p) ^ k *
          (if k = 0 then (0:ℂ) else (eulerianNumber m (k - 1) : ℂ))) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [step1]
    have hshift := shift_sum_gen (R := ℂ) m
      (fun k : ℕ => ((((m + 1 - k : ℕ))) : ℂ) * (-p) ^ k)
      (fun j : ℕ => (eulerianNumber m j : ℂ))
    rw [hshift]
    apply Finset.sum_congr rfl
    intro j _
    have hsub : m + 1 - (j + 1) = m - j := by omega
    rw [hsub]
    ring
  have hA : (∑ k ∈ range (m + 1), ((((k + 1 : ℕ))) : ℂ) * (eulerianNumber m k : ℂ) * (-p) ^ k) =
      (∑ k ∈ range m, ((((k + 1 : ℕ))) : ℂ) * (eulerianNumber m k : ℂ) * (-p) ^ k) := by
    rw [Finset.sum_range_succ]
    have hv : (eulerianNumber m m : ℂ) = 0 := by
      exact_mod_cast eulerian_vanish m m le_rfl hm
    rw [hv, mul_zero, zero_mul, add_zero]
  have key : ∀ k ∈ range m, ((((k + 1 : ℕ))) : ℂ) * (eulerianNumber m k : ℂ) * (-p) ^ k +
      ((((m - k : ℕ))) : ℂ) * (eulerianNumber m k : ℂ) * (-p) ^ (k + 1) =
      (1 - (m : ℂ) * p) * ((eulerianNumber m k : ℂ) * (-p) ^ k) +
      p * (1 + p) * ((eulerianNumber m k : ℂ) * (k : ℂ) * (-1) * (-p) ^ (k - 1)) := by
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      simp only [Nat.cast_one, Nat.cast_zero, Nat.sub_zero, pow_zero, pow_one,
        Nat.zero_sub, mul_zero, mul_one, zero_add, mul_add]
      ring
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk0
      have hjm : j + 1 ≤ m := le_of_lt (Finset.mem_range.mp hk)
      rw [Nat.cast_sub hjm]
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, pow_succ]
      ring
  have eA : (1 - (m : ℂ) * p) * ∑ k ∈ range m, (eulerianNumber m k : ℂ) * (-p) ^ k =
      ∑ k ∈ range m, (1 - (m : ℂ) * p) * ((eulerianNumber m k : ℂ) * (-p) ^ k) := by
    rw [Finset.mul_sum]
  have eD : p * (1 + p) *
      ∑ k ∈ range m, (eulerianNumber m k : ℂ) * (k : ℂ) * (-1) * (-p) ^ (k - 1) =
      ∑ k ∈ range m, p * (1 + p) *
        ((eulerianNumber m k : ℂ) * (k : ℂ) * (-1) * (-p) ^ (k - 1)) := by
    rw [Finset.mul_sum]
  rw [hA, hB, eA, eD, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl key

private theorem psi_one (p : ℂ) : chapter5Psi 1 p = 1 := by
  unfold chapter5Psi
  rw [ite_eq_right (by omega : (1:ℕ) ≠ 0)]
  simp [eulerian_zero]

private theorem psiPoly_eval_gen (n : ℕ) (hn : n ≠ 0) (p : ℂ) :
    (psiPoly n).eval p = chapter5Psi n p := by
  unfold chapter5Psi psiPoly
  rw [ite_eq_right hn, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k _
  simp

private theorem psi_recurrence (m : ℕ) (hm : 1 ≤ m) (p : ℂ) :
    chapter5Psi (m + 1) p = (1 - (m : ℂ) * p) * chapter5Psi m p +
    p * (1 + p) * (psiPoly m).derivative.eval p := by
  have h1 : chapter5Psi (m + 1) p =
      ∑ k ∈ range (m + 1), (eulerianNumber (m + 1) k : ℂ) * (-p) ^ k := by
    unfold chapter5Psi
    rw [ite_eq_right (Nat.add_one_ne_zero m)]
  have h2 : chapter5Psi m p =
      ∑ k ∈ range m, (eulerianNumber m k : ℂ) * (-p) ^ k := by
    unfold chapter5Psi
    rw [ite_eq_right (by omega : m ≠ 0)]
  rw [h1, h2, psiPoly_deriv_sum]
  exact psi_rec_sum m hm p

private theorem hEplus1 (x : ℂ) :
    HasDerivAt (fun y : ℂ => Complex.exp y + 1) (Complex.exp x) x := by
  have h := (Complex.hasDerivAt_exp x).add_const (1:ℂ)
  simpa using h

private theorem div_cleanup (u V w q w2 : ℂ) (n : ℕ) (hV : V ≠ 0) (hVeq : V = u + 1)
    (hrec : w2 = (1 - (n : ℂ) * u) * w + u * (1 + u) * q) :
    (((-u)*w + (-u)*(q*u)) * V^(n+1) - (-u*w) * ((((n+1 : ℕ)):ℂ)*V^n*u)) / (V^(n+1))^2
    = -u*w2 / V^(n+2) := by
  have hD2 : (V^(n+1))^2 ≠ 0 := pow_ne_zero 2 (pow_ne_zero _ hV)
  have hV2 : V^(n+2) ≠ 0 := pow_ne_zero _ hV
  rw [div_eq_div_iff hD2 hV2, hrec, hVeq]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

private theorem psiDeriv : ∀ n : ℕ, ∀ _hn : 1 ≤ n, ∀ x : ℂ, Complex.exp x + 1 ≠ 0 →
    iteratedDeriv n auxF x =
    -Complex.exp x * chapter5Psi n (Complex.exp x) / (Complex.exp x + 1)^(n+1) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro x hx
    have h1 : HasDerivAt auxF (-Complex.exp x / (Complex.exp x + 1)^2) x := by
      have hdiv := HasDerivAt.div (hasDerivAt_const x (1:ℂ)) (hEplus1 x) hx
      have e : (0:ℂ) * (Complex.exp x + 1) - 1 * Complex.exp x = -Complex.exp x := by ring
      rw [e] at hdiv
      exact hdiv
    have h2 : iteratedDeriv 1 auxF x = -Complex.exp x / (Complex.exp x + 1)^2 := by
      rw [iteratedDeriv_one]
      exact h1.deriv
    rw [h2, psi_one]
    ring
  | succ n hmn ih =>
    intro x hx
    have hcont : ContinuousAt (fun y : ℂ => Complex.exp y + 1) x :=
      (Complex.continuous_exp.add continuous_const).continuousAt
    have hev : ∀ᶠ y in nhds x, Complex.exp y + 1 ≠ 0 := hcont.eventually_ne hx
    have hQeval : ∀ y : ℂ, (psiPoly n).eval (Complex.exp y) = chapter5Psi n (Complex.exp y) := by
      intro y
      exact psiPoly_eval_gen n (by omega) (Complex.exp y)
    have hB : HasDerivAt (fun y : ℂ => (psiPoly n).eval (Complex.exp y))
        ((psiPoly n).derivative.eval (Complex.exp x) * Complex.exp x) x :=
      (Polynomial.hasDerivAt (psiPoly n) (Complex.exp x)).comp x (Complex.hasDerivAt_exp x)
    have hA : HasDerivAt (fun y : ℂ => -Complex.exp y) (-Complex.exp x) x :=
      (Complex.hasDerivAt_exp x).neg
    have hAB : HasDerivAt
        ((fun y : ℂ => -Complex.exp y) * (fun y : ℂ => (psiPoly n).eval (Complex.exp y)))
        ((-Complex.exp x) * (psiPoly n).eval (Complex.exp x) +
          (-Complex.exp x) * ((psiPoly n).derivative.eval (Complex.exp x) * Complex.exp x)) x :=
      hA.mul hB
    have hD : HasDerivAt (fun y : ℂ => (Complex.exp y + 1)^(n+1))
        ((((n+1 : ℕ)):ℂ) * (Complex.exp x + 1)^n * Complex.exp x) x := by
      have hpow := (hEplus1 x).fun_pow (n+1)
      rw [Nat.add_sub_cancel] at hpow
      exact hpow
    have hDne : (Complex.exp x + 1)^(n+1) ≠ 0 := pow_ne_zero _ hx
    have hF := hAB.div hD hDne
    have heq : iteratedDeriv n auxF =ᶠ[nhds x]
        (((fun y : ℂ => -Complex.exp y) * (fun y : ℂ => (psiPoly n).eval (Complex.exp y))) /
          (fun y : ℂ => (Complex.exp y + 1)^(n+1))) :=
      Filter.eventuallyEq_of_mem hev (fun y hy => by
        change iteratedDeriv n auxF y =
          -Complex.exp y * (psiPoly n).eval (Complex.exp y) / (Complex.exp y + 1)^(n+1)
        rw [hQeval y]
        exact ih y hy)
    have hderiv : deriv (iteratedDeriv n auxF) x =
        deriv (((fun y : ℂ => -Complex.exp y) * (fun y : ℂ => (psiPoly n).eval (Complex.exp y))) /
          (fun y : ℂ => (Complex.exp y + 1)^(n+1))) x :=
      Filter.EventuallyEq.deriv_eq heq
    have hstep : iteratedDeriv (n+1) auxF x =
        deriv (((fun y : ℂ => -Complex.exp y) * (fun y : ℂ => (psiPoly n).eval (Complex.exp y))) /
          (fun y : ℂ => (Complex.exp y + 1)^(n+1))) x := by
      rw [iteratedDeriv_succ]
      exact hderiv
    have hrec : chapter5Psi (n+1) (Complex.exp x) =
        (1 - (n:ℂ)*Complex.exp x) * (psiPoly n).eval (Complex.exp x) +
        Complex.exp x * (1 + Complex.exp x) * (psiPoly n).derivative.eval (Complex.exp x) := by
      have h := psi_recurrence n hmn (Complex.exp x)
      rw [← hQeval x] at h
      exact h
    have hconv : deriv (((fun y : ℂ => -Complex.exp y) *
          (fun y : ℂ => (psiPoly n).eval (Complex.exp y))) /
          (fun y : ℂ => (Complex.exp y + 1)^(n+1))) x =
        -Complex.exp x * chapter5Psi (n+1) (Complex.exp x) / (Complex.exp x + 1)^(n+1+1) := by
      have hform : deriv (((fun y : ℂ => -Complex.exp y) *
            (fun y : ℂ => (psiPoly n).eval (Complex.exp y))) /
            (fun y : ℂ => (Complex.exp y + 1)^(n+1))) x =
          (((-Complex.exp x) * (psiPoly n).eval (Complex.exp x) +
            (-Complex.exp x) * ((psiPoly n).derivative.eval (Complex.exp x) * Complex.exp x)) *
            (Complex.exp x + 1)^(n+1) -
            (-Complex.exp x) * (psiPoly n).eval (Complex.exp x) *
              ((((n+1 : ℕ)):ℂ) * (Complex.exp x + 1)^n * Complex.exp x)) /
            ((Complex.exp x + 1)^(n+1))^2 := hF.deriv
      rw [hform]
      exact div_cleanup (Complex.exp x) (Complex.exp x + 1)
        ((psiPoly n).eval (Complex.exp x)) ((psiPoly n).derivative.eval (Complex.exp x))
        (chapter5Psi (n+1) (Complex.exp x)) n hx rfl hrec
    rw [hstep, hconv]

private theorem psivalue (n : ℕ) (hn : 1 ≤ n) : chapter5Psi n (1:ℂ) =
    (2:ℂ)^(n+1) * ((2:ℂ)^(n+1) - 1) * (bernoulli (n+1):ℂ) / ((n:ℂ) + 1) := by
  have hx0 : Complex.exp (0:ℂ) + 1 ≠ 0 := by simp [Complex.exp_zero]
  have hder := psiDeriv n hn 0 hx0
  have e11 : ((1:ℂ) + 1) = 2 := by norm_num
  rw [Complex.exp_zero, e11] at hder
  have hder2 : iteratedDeriv n auxF 0 =
      -(chapter5Psi n (1:ℂ)) / (2:ℂ)^(n+1) := by
    rw [hder]; ring
  have hdv := dval n
  have hE2 : ((2:ℂ)^(n+1)) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hm : ((n:ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hP : -(chapter5Psi n (1:ℂ)) / (2:ℂ)^(n+1) =
      (1 - (2:ℂ)^(n+1)) * (bernoulli (n+1):ℂ) / ((n:ℂ) + 1) := by
    rw [← hder2, ← hdv]
  have hP' : chapter5Psi n (1:ℂ) * (((n:ℂ) + 1)) =
      -((2:ℂ)^(n+1)) * ((1 - (2:ℂ)^(n+1)) * (bernoulli (n+1):ℂ)) := by
    rw [div_eq_div_iff hE2 hm] at hP
    linear_combination -hP
  rw [eq_div_iff hm]
  linear_combination hP'

private theorem aux_exp_add_one_ne (z : ℂ) (hz : ‖z‖ < Real.pi) :
    Complex.exp z + 1 ≠ 0 := by
  intro h
  have he : Complex.exp z = -1 := by linear_combination h
  have h2 : Complex.exp (2 * z) = 1 := by
    rw [two_mul, Complex.exp_add, he]
    ring
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h2
  have hz_eq : z = (k : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    linear_combination hk / 2
  have hk0 : k ≠ 0 := by
    intro hk0
    rw [hk0] at hz_eq
    simp only [Int.cast_zero, zero_mul]at hz_eq
    rw [hz_eq, Complex.exp_zero] at he
    norm_num at he
  have h1 : (1 : ℝ) ≤ (|k| : ℝ) := by exact_mod_cast Int.one_le_abs hk0
  have hnorm : ‖z‖ = (|k| : ℝ) * Real.pi := by
    rw [hz_eq, norm_mul, Complex.norm_intCast, norm_mul, Complex.norm_real,
      Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hnorm] at hz
  have hle : (1 : ℝ) * Real.pi ≤ (|k| : ℝ) * Real.pi :=
    mul_le_mul_of_nonneg_right h1 (le_of_lt Real.pi_pos)
  rw [one_mul] at hle
  linarith

private theorem fDiffBall : DifferentiableOn ℂ auxF (Metric.ball (0:ℂ) Real.pi) := by
  have h1 : DifferentiableOn ℂ (fun _ : ℂ => (1:ℂ)) (Metric.ball (0:ℂ) Real.pi) :=
    differentiableOn_const 1
  have h2 : DifferentiableOn ℂ (fun x : ℂ => Complex.exp x + 1) (Metric.ball (0:ℂ) Real.pi) :=
    (Complex.differentiable_exp.add_const 1).differentiableOn
  have h3 : ∀ x ∈ Metric.ball (0:ℂ) Real.pi,
      (fun x : ℂ => Complex.exp x + 1) x ≠ 0 := by
    intro x hx
    have hzx : ‖x‖ < Real.pi := by
      have hmem := Metric.mem_ball.mp hx
      simpa using hmem
    exact aux_exp_add_one_ne x hzx
  have h := DifferentiableOn.div h1 h2 h3
  exact h

private theorem hasSumBernoulli (z : ℂ) (hz : ‖z‖ < Real.pi) :
    HasSum (chapter5Entry8BernoulliTerm z) (1 / (Complex.exp z + 1)) := by
  have hzmem : z ∈ Metric.ball (0:ℂ) Real.pi := Metric.mem_ball.mpr (by simpa using hz)
  have hT := Complex.hasSum_taylorSeries_on_ball fDiffBall hzmem
  have heq : (chapter5Entry8BernoulliTerm z) =
      (fun n => ((n.factorial : ℂ))⁻¹ • (z - 0)^n • iteratedDeriv n auxF 0) := by
    funext j
    have hd := dval j
    have hfj : (j.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    have hj1 : (((j:ℂ)) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    have hfact : (((j+1).factorial:ℕ):ℂ) = ((((j+1:ℕ))):ℂ)*(j.factorial:ℂ) := by
      exact_mod_cast Nat.factorial_succ j
    have ecast : ((((j+1:ℕ))):ℂ) = (((j:ℂ)) + 1) := by push_cast; ring
    unfold chapter5Entry8BernoulliTerm
    rw [hd, hfact, ecast]
    simp only [sub_zero, smul_eq_mul]
    field_simp
  rw [heq]
  exact hT

private theorem hasSumPsi (z : ℂ) (hz : ‖z‖ < Real.pi) :
    HasSum (chapter5Entry8PsiTerm z) (1 / (Complex.exp z + 1)) := by
  have hzmem : z ∈ Metric.ball (0:ℂ) Real.pi := Metric.mem_ball.mpr (by simpa using hz)
  have hT := Complex.hasSum_taylorSeries_on_ball fDiffBall hzmem
  have heq : (chapter5Entry8PsiTerm z) =
      (fun n => ((n.factorial : ℂ))⁻¹ • (z - 0)^n • iteratedDeriv n auxF 0) := by
    funext j
    by_cases hj0 : j = 0
    · subst hj0
      have hPsi0 : chapter5Psi 0 (1:ℂ) = 1 := by unfold chapter5Psi; simp
      have hd0 : iteratedDeriv 0 auxF 0 = 1/2 := by
        rw [iteratedDeriv_zero]
        change 1 / (Complex.exp 0 + 1) = 1 / 2
        rw [Complex.exp_zero]
        norm_num
      unfold chapter5Entry8PsiTerm
      rw [hPsi0, hd0]
      simp
    · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
      have hneg : (-1:ℂ)^j * chapter5Psi j (1:ℂ) = -chapter5Psi j (1:ℂ) := by
        by_cases hodd : Odd j
        · rw [hodd.neg_one_pow]
          ring
        · obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.mp hodd
          have hodd1 : Odd (j+1) := ⟨k, by omega⟩
          have hB0 : bernoulli (j+1) = 0 :=
            bernoulli_eq_zero_of_odd hodd1 (by omega)
          have hPsi0 : chapter5Psi j (1:ℂ) = 0 := by
            rw [psivalue j hj1, hB0]
            simp
          rw [hPsi0, mul_zero, neg_zero]
      have hPsi := psivalue j hj1
      have hd := dval j
      have hE2 : ((2:ℂ)^(j+1)) ≠ 0 := pow_ne_zero _ two_ne_zero
      have hfj : (j.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
      have hm : (((j:ℂ)) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
      unfold chapter5Entry8PsiTerm
      rw [hneg, hPsi, hd]
      simp only [sub_zero, smul_eq_mul]
      field_simp
      ring
  rw [heq]
  exact hT

/-- **No zeros of e^z + 1 in the disc of radius pi.** For every complex number $z$ with
$|z| < \pi$, we have $e^z + 1 \ne 0$. -/
theorem chapter5Entry8_exp_add_one_ne (z : ℂ) (hz : ‖z‖ < Real.pi) :
    Complex.exp z + 1 ≠ 0 :=
  aux_exp_add_one_ne z hz

/-- **Eulerian polynomials at p = -1.** Let $A(n,k)$ be the Eulerian numbers, given by
$A(0,0) = 1$, $A(0,k) = 0$ for $k \ge 1$ and
$A(n+1,k) = (k+1)A(n,k) + (n+1-k)A(n,k-1)$, where the last term is $0$ when $k = 0$, and let
$\Psi_0(p) = 1$ and $\Psi_n(p) = \sum_{k=0}^{n-1} A(n,k)(-p)^k$ for $n \ge 1$. For every natural
number $n$, $\Psi_n(-1) = n!$. -/
theorem chapter5Entry8_psi_neg_one (n : ℕ) :
    chapter5Psi n (-1 : ℂ) = (n.factorial : ℂ) :=
  psi_neg_one n

/-- **Eulerian polynomials at p = 1 in terms of Bernoulli numbers.** Let $A(n,k)$ be the Eulerian
numbers, given by $A(0,0) = 1$, $A(0,k) = 0$ for $k \ge 1$ and
$A(n+1,k) = (k+1)A(n,k) + (n+1-k)A(n,k-1)$, where the last term is $0$ when $k = 0$; let
$\Psi_0(p) = 1$ and $\Psi_n(p) = \sum_{k=0}^{n-1} A(n,k)(-p)^k$ for $n \ge 1$, and let $B_m$ be
the Bernoulli numbers. For every integer $n \ge 1$,
$\Psi_n(1) = 2^{n+1}(2^{n+1} - 1)B_{n+1}/(n+1)$. -/
theorem chapter5Entry8_psi_one (n : ℕ) (hn : 1 ≤ n) :
    chapter5Psi n (1 : ℂ) =
      (2 : ℂ) ^ (n + 1) * ((2 : ℂ) ^ (n + 1) - 1) *
        (bernoulli (n + 1) : ℂ) / (n + 1 : ℂ) :=
  psivalue n hn

/-- **Bernoulli-number expansion of 1/(e^z + 1) in the disc of radius pi.** Let $B_m$ be the
Bernoulli numbers, with $B_1 = -\tfrac{1}{2}$. For every complex number $z$ with $|z| < \pi$, the
series $\sum_{j \ge 0} (1 - 2^{j+1}) B_{j+1} z^j/(j+1)!$ is summable with sum $1/(e^z + 1)$. -/
theorem chapter5Entry8_hasSum_bernoulli (z : ℂ) (hz : ‖z‖ < Real.pi) :
    HasSum (chapter5Entry8BernoulliTerm z)
      (1 / (Complex.exp z + 1)) :=
  hasSumBernoulli z hz

/-- **Eulerian-polynomial expansion of 1/(e^z + 1) in the disc of radius pi.** Let $A(n,k)$ be the
Eulerian numbers, given by $A(0,0) = 1$, $A(0,k) = 0$ for $k \ge 1$ and
$A(n+1,k) = (k+1)A(n,k) + (n+1-k)A(n,k-1)$, where the last term is $0$ when $k = 0$, and let
$\Psi_0(p) = 1$ and $\Psi_n(p) = \sum_{k=0}^{n-1} A(n,k)(-p)^k$ for $n \ge 1$. For every complex
number $z$ with $|z| < \pi$, the series $\sum_{m \ge 0} (-1)^m \Psi_m(1) z^m/(2^{m+1} m!)$ is
summable with sum $1/(e^z + 1)$. -/
theorem chapter5Entry8_hasSum_psi (z : ℂ) (hz : ‖z‖ < Real.pi) :
    HasSum (chapter5Entry8PsiTerm z)
      (1 / (Complex.exp z + 1)) :=
  hasSumPsi z hz

/-- **Eulerian polynomials at 1 and -1 and two series for 1/(e^z + 1).** Let $A(n,k)$ be the
Eulerian numbers, given by $A(0,0) = 1$, $A(0,k) = 0$ for $k \ge 1$ and
$A(n+1,k) = (k+1)A(n,k) + (n+1-k)A(n,k-1)$, where the last term is $0$ when $k = 0$; let
$\Psi_0(p) = 1$ and $\Psi_n(p) = \sum_{k=0}^{n-1} A(n,k)(-p)^k$ for $n \ge 1$, and let $B_m$ be
the Bernoulli numbers, with $B_1 = -\tfrac{1}{2}$. For every integer $n \ge 1$ and every complex
number $z$ with $|z| < \pi$, we have $e^z + 1 \ne 0$, $\Psi_n(-1) = n!$,
$\Psi_n(1) = 2^{n+1}(2^{n+1} - 1)B_{n+1}/(n+1)$, the series
$\sum_{j \ge 0} (1 - 2^{j+1}) B_{j+1} z^j/(j+1)!$ is summable with sum $1/(e^z + 1)$, and the
series $\sum_{m \ge 0} (-1)^m \Psi_m(1) z^m/(2^{m+1} m!)$ is summable with sum $1/(e^z + 1)$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 5, Entry 8.
-/
theorem ramanujan_part1_ch5_entry8_eulerianformula (n : ℕ) (z : ℂ)
    (hn : 1 ≤ n) (hz : ‖z‖ < Real.pi) :
    Complex.exp z + 1 ≠ 0 ∧
      chapter5Psi n (-1 : ℂ) = (n.factorial : ℂ) ∧
      chapter5Psi n (1 : ℂ) =
        (2 : ℂ) ^ (n + 1) * ((2 : ℂ) ^ (n + 1) - 1) *
          (bernoulli (n + 1) : ℂ) / (n + 1 : ℂ) ∧
      HasSum (chapter5Entry8BernoulliTerm z)
        (1 / (Complex.exp z + 1)) ∧
      HasSum (chapter5Entry8PsiTerm z)
        (1 / (Complex.exp z + 1)) := by
  exact ⟨chapter5Entry8_exp_add_one_ne z hz, chapter5Entry8_psi_neg_one n,
    chapter5Entry8_psi_one n hn, chapter5Entry8_hasSum_bernoulli z hz,
    chapter5Entry8_hasSum_psi z hz⟩

end
end Entry8Eulerianformula
end MathlibExt.Analysis.Ramanujan.Part1Ch5
end
