/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Squarefree
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 5

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch5

namespace Entry2iEuleriangf

open scoped Nat Real BigOperators Interval Polynomial
open Finset

noncomputable section

def chapter5PolynomialShift {R : Type*} [Semiring R]
    (h : R) (p : R[X]) : R[X] :=
  p.comp (Polynomial.X + Polynomial.C h)

/-- **The polynomial shift is the Taylor shift.** For a semiring $R$, an element $h \in R$ and a
polynomial $p \in R[x]$, the shift $p(x + h)$ (the composition of $p$ with $x + h$) equals the
Taylor expansion of $p$ at $h$, the polynomial whose coefficient of $x^k$ is the $k$-th Hasse
derivative of $p$ evaluated at $h$. -/
theorem chapter5PolynomialShift_eq_taylor {R : Type*} [Semiring R] (h : R) (p : R[X]) :
    chapter5PolynomialShift h p = Polynomial.taylor h p :=
  (Polynomial.taylor_apply h p).symm

def chapter5Entry2F (phi : ℝ[X]) (n : ℕ) : ℝ[X] :=
  phi +
    ∑ k ∈ Icc 1 n,
      Polynomial.C
          ((-1 : ℝ) ^ k * ((n.factorial : ℝ) ^ 2) /
            (((n + k).factorial : ℝ) * ((n - k).factorial : ℝ))) *
        (chapter5PolynomialShift (k : ℝ) phi +
          chapter5PolynomialShift (-(k : ℝ)) phi)

def chapter5Entry2MinusSolution (phi : ℝ[X]) : ℝ[X] :=
  ∑ n ∈ range (phi.natDegree / 2 + 1),
    Polynomial.C (1 / ((2 * n + 1 : ℕ) : ℝ)) * chapter5Entry2F phi n

def chapter5Entry2PlusSolution (phi : ℝ[X]) : ℝ[X] :=
  ∑ n ∈ range (phi.natDegree / 2 + 1),
    Polynomial.C ((Nat.choose (2 * n) n : ℝ) / (2 : ℝ) ^ n) *
      chapter5Entry2F phi n

private abbrev psE : PowerSeries ℝ := PowerSeries.exp ℝ
private abbrev psEb : PowerSeries ℝ := PowerSeries.rescale (-1) (PowerSeries.exp ℝ)

private theorem neg_one_sq_pow (m : ℕ) : ((-1 : ℝ) ^ m) ^ 2 = 1 := by
  rw [sq, ← pow_add, ← two_mul]
  exact Even.neg_one_pow ⟨m, two_mul m⟩

private theorem neg_one_pow_mul_self (m : ℕ) : (-1 : ℝ) ^ m * (-1) ^ m = 1 := by
  rw [← pow_add, show m + m = 2 * m from by ring]
  exact Even.neg_one_pow ⟨m, two_mul m⟩

private theorem neg_one_sub_pow (i j : ℕ) (h : j ≤ i) :
    (-1 : ℝ) ^ (i - j) = (-1) ^ i * (-1) ^ j := by
  have h2 : (-1 : ℝ) ^ (i - j) * (-1) ^ j = (-1) ^ i := by
    rw [← pow_add, Nat.sub_add_cancel h]
  calc (-1 : ℝ) ^ (i - j) = (-1 : ℝ) ^ (i - j) * (((-1) ^ j) ^ 2) := by
        rw [neg_one_sq_pow, mul_one]
    _ = ((-1 : ℝ) ^ (i - j) * (-1) ^ j) * (-1) ^ j := by ring
    _ = (-1) ^ i * (-1) ^ j := by rw [h2]

private theorem scalar_match_upper (n k : ℕ) (hk : k ≤ n) :
    ((-1 : ℝ) ^ n * ((n.factorial : ℝ) ^ 2) / ((2 * n).factorial : ℝ)) *
      ((2 * n).choose (n + k) : ℝ) * (-1 : ℝ) ^ (2 * n - (n + k)) =
      (-1 : ℝ) ^ k * ((n.factorial : ℝ) ^ 2) /
        (((n + k).factorial : ℝ) * ((n - k).factorial : ℝ)) := by
  have hle : n + k ≤ 2 * n := by omega
  have hsub : 2 * n - (n + k) = n - k := by omega
  have key : ((2 * n).choose (n + k) : ℝ) * ((n + k).factorial : ℝ) *
      ((n - k).factorial : ℝ) = ((2 * n).factorial : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial hle
    have h2 : 2 * n - (n + k) = n - k := by omega
    rw [h2] at h
    exact_mod_cast h
  have hF1 : ((n + k).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hF2 : ((n - k).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hF3 : ((2 * n).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [hsub, neg_one_sub_pow n k hk,
    show (-1 : ℝ) ^ n * (n.factorial : ℝ) ^ 2 / ((2 * n).factorial : ℝ) *
      ((2 * n).choose (n + k) : ℝ) * ((-1 : ℝ) ^ n * (-1) ^ k)
      = ((n.factorial : ℝ) ^ 2 * ((2 * n).choose (n + k) : ℝ) * (-1 : ℝ) ^ k /
        ((2 * n).factorial : ℝ)) * ((-1 : ℝ) ^ n * (-1) ^ n) from by ring,
    neg_one_pow_mul_self n, mul_one]
  field_simp
  linear_combination key

private theorem scalar_match_lower (n k : ℕ) (hk : k ≤ n) :
    ((-1 : ℝ) ^ n * ((n.factorial : ℝ) ^ 2) / ((2 * n).factorial : ℝ)) *
      ((2 * n).choose (n - k) : ℝ) * (-1 : ℝ) ^ (2 * n - (n - k)) =
      (-1 : ℝ) ^ k * ((n.factorial : ℝ) ^ 2) /
        (((n + k).factorial : ℝ) * ((n - k).factorial : ℝ)) := by
  have hle : n - k ≤ 2 * n := by omega
  have hsub : 2 * n - (n - k) = n + k := by omega
  have key : ((2 * n).choose (n - k) : ℝ) * ((n - k).factorial : ℝ) *
      ((n + k).factorial : ℝ) = ((2 * n).factorial : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial hle
    have h2 : 2 * n - (n - k) = n + k := by omega
    rw [h2] at h
    exact_mod_cast h
  have hF1 : ((n + k).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hF2 : ((n - k).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hF3 : ((2 * n).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [hsub, pow_add,
    show (-1 : ℝ) ^ n * (n.factorial : ℝ) ^ 2 / ((2 * n).factorial : ℝ) *
      ((2 * n).choose (n - k) : ℝ) * ((-1 : ℝ) ^ n * (-1) ^ k)
      = ((n.factorial : ℝ) ^ 2 * ((2 * n).choose (n - k) : ℝ) * (-1 : ℝ) ^ k /
        ((2 * n).factorial : ℝ)) * ((-1 : ℝ) ^ n * (-1) ^ n) from by ring,
    neg_one_pow_mul_self n, mul_one]
  field_simp
  linear_combination key

private theorem scalar_match_center (n : ℕ) :
    ((-1 : ℝ) ^ n * ((n.factorial : ℝ) ^ 2) / ((2 * n).factorial : ℝ)) *
      ((2 * n).choose n : ℝ) * (-1 : ℝ) ^ (2 * n - n) = 1 := by
  have hsub : 2 * n - n = n := by omega
  have key : ((2 * n).choose n : ℝ) * ((n.factorial : ℝ)) *
      ((n.factorial : ℝ)) = ((2 * n).factorial : ℝ) := by
    have h := Nat.add_choose_mul_factorial_mul_factorial n n
    have h2 : n + n = 2 * n := by ring
    rw [h2] at h
    exact_mod_cast h
  have hF1 : ((n.factorial : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hF3 : ((2 * n).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [hsub,
    show (-1 : ℝ) ^ n * (n.factorial : ℝ) ^ 2 / ((2 * n).factorial : ℝ) *
      ((2 * n).choose n : ℝ) * (-1 : ℝ) ^ n
      = ((n.factorial : ℝ) ^ 2 * ((2 * n).choose n : ℝ) /
        ((2 * n).factorial : ℝ)) * ((-1 : ℝ) ^ n * (-1) ^ n) from by ring,
    neg_one_pow_mul_self n, mul_one]
  field_simp
  linear_combination key

private theorem sum_range_two_mul_add_one_eq {A : Type*} [AddCommMonoid A] (G : ℕ → A) (n : ℕ) :
    ∑ j ∈ Finset.range (2 * n + 1), G j =
      G n + ∑ k ∈ Finset.Icc 1 n, (G (n + k) + G (n - k)) := by
  have h1 : 2 * n + 1 = n + (n + 1) := by omega
  rw [h1, Finset.sum_range_add, Finset.sum_range_succ']
  simp only [Nat.add_zero]
  have hrefl : ∑ k ∈ Finset.range n, G k = ∑ k ∈ Finset.range n, G (n - (k + 1)) := by
    have h := Finset.sum_range_reflect (fun k => G (n - (k + 1))) n
    rw [← h]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    congr 1
    omega
  rw [hrefl]
  have hIcc : (∑ k ∈ Finset.Icc 1 n, (G (n + k) + G (n - k))) =
      ∑ k ∈ Finset.range n, (G (n + (k + 1)) + G (n - (k + 1))) := by
    have : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := rfl
    rw [this, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro k hk
    rw [add_comm 1 k]
  rw [hIcc, Finset.sum_add_distrib]
  ac_rfl

private theorem sym_shift_identity {A : Type*} [CommRing A] {a b : A} (hab : a * b = 1) :
    a + b - 2 = b * (a - 1) ^ 2 := by
  linear_combination (2 - a) * hab

private theorem n7_expand {A : Type*} [CommRing A] [Algebra ℝ A] (a b : A) (hab : a * b = 1)
    (n : ℕ) :
    (((-1 : ℝ) ^ n * ((n.factorial : ℝ) ^ 2) / ((2 * n).factorial : ℝ)) • (a + b - 2) ^ n) =
      ∑ j ∈ Finset.range (2 * n + 1),
        ((((-1 : ℝ) ^ n * ((n.factorial : ℝ) ^ 2) / ((2 * n).factorial : ℝ)) *
          (((2 * n).choose j : ℝ)) * (-1 : ℝ) ^ (2 * n - j)) • (a ^ j * b ^ n)) := by
  have hexp : (a - 1) ^ (2 * n) =
      ∑ j ∈ Finset.range (2 * n + 1),
          (a ^ j * (-1 : A) ^ (2 * n - j) * (((2 * n).choose j : A))) := by
    rw [sub_eq_add_neg]
    exact add_pow a (-1) (2 * n)
  rw [sym_shift_identity hab, mul_pow, ← pow_mul, hexp, Finset.mul_sum, smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have e1 : (-1 : A) ^ (2 * n - j) = algebraMap ℝ A ((-1 : ℝ) ^ (2 * n - j)) := by
    simp [map_pow]
  have e2 : (((2 * n).choose j : A)) = algebraMap ℝ A ((((2 * n).choose j : ℝ))) :=
    (map_natCast (algebraMap ℝ A) ((2 * n).choose j)).symm
  rw [e1, e2, mul_assoc (a ^ j) _ _, (map_mul (algebraMap ℝ A) _ _).symm]
  have hcomm : b ^ n * (a ^ j * algebraMap ℝ A ((-1 : ℝ) ^ (2 * n - j) * (((2 * n).choose j : ℝ))))
      = algebraMap ℝ A ((-1 : ℝ) ^ (2 * n - j) * (((2 * n).choose j : ℝ))) * (a ^ j * b ^ n) := by
    ring
  rw [hcomm, Algebra.smul_def, Algebra.smul_def, ← mul_assoc, (map_mul (algebraMap ℝ A) _ _).symm]
  congr 1
  ring

private theorem aeval_derivative_apply_eq_zero {p phi : ℝ[X]} {m : ℕ}
    (hdvd : Polynomial.X ^ m ∣ p) (hlt : phi.natDegree < m) :
    (Polynomial.aeval Polynomial.derivative) p phi = 0 := by
  obtain ⟨q, rfl⟩ := hdvd
  have h0 : (⇑Polynomial.derivative)^[m] phi = 0 := Polynomial.iterate_derivative_eq_zero hlt
  rw [mul_comm, map_mul, Polynomial.aeval_X_pow, Module.End.mul_apply, Module.End.pow_apply,
    h0, map_zero]

private theorem aeval_derivative_apply_eq_of_sub {p q phi : ℝ[X]} {m : ℕ}
    (hdvd : Polynomial.X ^ m ∣ p - q) (hlt : phi.natDegree < m) :
    (Polynomial.aeval Polynomial.derivative) p phi = (Polynomial.aeval Polynomial.derivative) q
        phi := by
  have h : (Polynomial.aeval Polynomial.derivative) (p - q) phi = 0 :=
    aeval_derivative_apply_eq_zero hdvd hlt
  rw [map_sub, LinearMap.sub_apply] at h
  exact sub_eq_zero.mp h

private theorem natDegree_aeval_derivative_apply_le (p phi : ℝ[X]) :
    ((Polynomial.aeval Polynomial.derivative) p phi).natDegree ≤ phi.natDegree := by
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  rw [LinearMap.smul_apply, Module.End.pow_apply]
  exact le_trans (Polynomial.natDegree_smul_le _ _)
    (le_trans (Polynomial.natDegree_iterate_derivative phi i) (Nat.sub_le _ _))

private theorem x_pow_succ_dvd_of_derivative {g : PowerSeries ℝ} {m : ℕ}
    (h0 : PowerSeries.constantCoeff g = 0)
    (hdvd : PowerSeries.X ^ m ∣ PowerSeries.derivative g) :
    PowerSeries.X ^ (m + 1) ∣ g := by
  rw [PowerSeries.X_pow_dvd_iff] at hdvd ⊢
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · rw [PowerSeries.coeff_zero_eq_constantCoeff]
    exact h0
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : k < m := by omega
    have h1 := hdvd k hk
    rw [PowerSeries.coeff_derivative] at h1
    have h2 : ((k : ℝ) + 1) ≠ 0 := by positivity
    exact (mul_eq_zero.mp h1).resolve_right h2

private noncomputable def psAct (M : ℕ) (f : PowerSeries ℝ) : Module.End ℝ ℝ[X] :=
  (Polynomial.aeval Polynomial.derivative) ((PowerSeries.trunc M) f)

private theorem psAct_trunc_aeval (M : ℕ) (p : ℝ[X]) (phi : ℝ[X]) (hM : phi.natDegree < M) :
    (Polynomial.aeval Polynomial.derivative) ((PowerSeries.trunc M) (p : PowerSeries ℝ)) phi =
      (Polynomial.aeval Polynomial.derivative) p phi := by
  apply aeval_derivative_apply_eq_of_sub _ hM
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  have h1 : ((PowerSeries.trunc M) (p : PowerSeries ℝ)).coeff d = p.coeff d := by
    simp [PowerSeries.coeff_trunc, Polynomial.coeff_coe, hd]
  have h2 : ((PowerSeries.trunc M) (p : PowerSeries ℝ) - p).coeff d =
      ((PowerSeries.trunc M) (p : PowerSeries ℝ)).coeff d - p.coeff d := by simp
  rw [h2, h1, sub_self]

private theorem psAct_add (M : ℕ) (f g : PowerSeries ℝ) :
    psAct M (f + g) = psAct M f + psAct M g := by
  unfold psAct
  rw [map_add, map_add]

private theorem psAct_smul (M : ℕ) (c : ℝ) (f : PowerSeries ℝ) :
    psAct M (c • f) = c • psAct M f := by
  unfold psAct
  rw [map_smul, map_smul]

private theorem psAct_sum (M : ℕ) {ι : Type*} (s : Finset ι) (F : ι → PowerSeries ℝ) :
    psAct M (∑ i ∈ s, F i) = ∑ i ∈ s, psAct M (F i) := by
  unfold psAct
  rw [map_sum, map_sum]

private theorem psAct_one (M : ℕ) (phi : ℝ[X]) (hM : phi.natDegree < M) :
    psAct M 1 phi = phi := by
  unfold psAct
  rw [← Polynomial.coe_one, psAct_trunc_aeval M 1 phi hM, map_one, Module.End.one_apply]

private theorem psAct_X_pow (M : ℕ) (phi : ℝ[X]) (hM : phi.natDegree < M) :
    psAct M PowerSeries.X phi = Polynomial.derivative phi := by
  unfold psAct
  rw [← Polynomial.coe_X, psAct_trunc_aeval M Polynomial.X phi hM, Polynomial.aeval_X]

private theorem psAct_C (M : ℕ) (c : ℝ) (phi : ℝ[X]) (hM : phi.natDegree < M) :
    psAct M (PowerSeries.C c) phi = c • phi := by
  unfold psAct
  rw [← Polynomial.coe_C, psAct_trunc_aeval M (Polynomial.C c) phi hM, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]

private theorem psAct_natDegree_le (M : ℕ) (f : PowerSeries ℝ) (phi : ℝ[X]) :
    (psAct M f phi).natDegree ≤ phi.natDegree := by
  unfold psAct
  exact natDegree_aeval_derivative_apply_le _ _

private theorem psAct_mul (M : ℕ) (f g : PowerSeries ℝ) (phi : ℝ[X]) (hM : phi.natDegree < M) :
    psAct M (f * g) phi = psAct M f (psAct M g phi) := by
  have htr : (PowerSeries.trunc M) (f * g) =
      (PowerSeries.trunc M) (((PowerSeries.trunc M f * PowerSeries.trunc M g : ℝ[X]) :
        PowerSeries ℝ)) := by
    rw [Polynomial.coe_mul, PowerSeries.trunc_trunc_mul_trunc]
  unfold psAct
  rw [htr, psAct_trunc_aeval M _ phi hM, map_mul, Module.End.mul_apply]

private theorem psAct_eq_zero_of_X_pow_dvd (M : ℕ) (f : PowerSeries ℝ) (phi : ℝ[X]) {m : ℕ}
    (hdvd : PowerSeries.X ^ m ∣ f) (hlt : phi.natDegree < m) :
    psAct M f phi = 0 := by
  apply aeval_derivative_apply_eq_zero _ hlt
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  have h1 : PowerSeries.coeff d f = 0 := (PowerSeries.X_pow_dvd_iff.mp hdvd) d hd
  rw [PowerSeries.coeff_trunc]
  split_ifs with hM'
  · exact h1
  · rfl

private theorem coeff_exp_real (n : ℕ) :
    PowerSeries.coeff n (psE) = 1 / (n.factorial : ℝ) := by
  rw [PowerSeries.coeff_exp]
  simp

private theorem exp_mul_rescale_neg_eq_one :
    psE * psEb = 1 :=
  PowerSeries.exp_mul_exp_neg_eq_one

private theorem exp_pow_eq_rescale (k : ℕ) :
    psE ^ k = PowerSeries.rescale (k : ℝ) (psE) :=
  PowerSeries.exp_pow_eq_rescale_exp k

private theorem rescale_neg_pow (k : ℕ) :
    psEb ^ k =
      PowerSeries.rescale (-(k : ℝ)) (psE) := by
  rw [← map_pow, exp_pow_eq_rescale, PowerSeries.rescale_rescale]
  congr 1
  ring

private theorem rescale_one_exp :
    PowerSeries.rescale (1 : ℝ) (psE) = psE := by
  rw [PowerSeries.rescale_one]
  rfl

private theorem derivative_rescale_neg_exp :
    PowerSeries.derivative (psEb) =
      -(psEb) := by
  apply PowerSeries.ext_iff.mpr
  intro n
  rw [map_neg]
  have h1 : PowerSeries.coeff n (PowerSeries.derivative (psEb))
      = (-1 : ℝ) ^ (n + 1) * (1 / (((n + 1).factorial : ℝ))) * ((n : ℝ) + 1) := by
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_rescale, coeff_exp_real]
  have h2 : PowerSeries.coeff n (psEb)
      = (-1 : ℝ) ^ n * (1 / ((n.factorial : ℝ))) := by
    rw [PowerSeries.coeff_rescale, coeff_exp_real]
  rw [h1, h2]
  have hF : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
    push_cast [Nat.factorial_succ]
    ring
  have hFne : ((n.factorial : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hneg : (-1 : ℝ) ^ (n + 1) = -(-1 : ℝ) ^ n := by
    rw [pow_succ, mul_neg, mul_one]
  rw [hneg, hF]
  field_simp

private theorem coeff0_exp : PowerSeries.coeff 0 (psE) = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_exp]

private theorem coeff1_exp : PowerSeries.coeff 1 (psE) = 1 := by
  rw [coeff_exp_real]
  norm_num

private theorem coeff0_rescale_neg_exp :
    PowerSeries.coeff 0 (psEb) = 1 := by
  rw [PowerSeries.coeff_rescale, coeff0_exp]
  norm_num

private theorem coeff1_rescale_neg_exp :
    PowerSeries.coeff 1 (psEb) = -1 := by
  rw [PowerSeries.coeff_rescale, coeff1_exp]
  norm_num

private theorem coeff0_two : PowerSeries.coeff 0 (2 : PowerSeries ℝ) = 2 := by
  rw [show (2 : PowerSeries ℝ) = PowerSeries.C 2 from rfl, PowerSeries.coeff_C]
  norm_num

private theorem coeff1_two : PowerSeries.coeff 1 (2 : PowerSeries ℝ) = 0 := by
  rw [show (2 : PowerSeries ℝ) = PowerSeries.C 2 from rfl, PowerSeries.coeff_C]
  norm_num

private theorem exp_add_rescale_sub_two :
    PowerSeries.X ^ 2 ∣ (psE + psEb - 2) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  interval_cases m
  · rw [map_sub, map_add, coeff0_exp, coeff0_rescale_neg_exp, coeff0_two]
    norm_num
  · rw [map_sub, map_add, coeff1_exp, coeff1_rescale_neg_exp, coeff1_two]
    norm_num

private noncomputable def psC (n : ℕ) : ℝ := 2 ^ n * ((n.factorial : ℝ) ^ 2) /
    ((2 * n + 1).factorial : ℝ)

private theorem psC_recurrence (N : ℕ) : (2 * N + 3 : ℝ) * psC (N + 1) = ((N + 1 : ℕ) : ℝ) * psC
    N := by
  unfold psC
  have e1 : 2 * (N + 1) + 1 = (2 * N + 2) + 1 := by ring
  have e2 : 2 * N + 2 = (2 * N + 1) + 1 := by ring
  rw [e1, Nat.factorial_succ (2 * N + 2), e2, Nat.factorial_succ (2 * N + 1),
    Nat.factorial_succ N, pow_succ (2 : ℝ) N]
  have hF1 : ((2 * N + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hF2 : ((N.factorial : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  push_cast
  field_simp
  ring

private theorem ode_step (a : ℝ) (m : ℕ) :
    (1 - Polynomial.X) * (Polynomial.C a * Polynomial.X ^ (m + 1)) +
      (2 * Polynomial.X - Polynomial.X ^ 2) *
        Polynomial.derivative (Polynomial.C a * Polynomial.X ^ (m + 1)) =
      Polynomial.C ((2 * m + 3) * a) * Polynomial.X ^ (m + 1) -
        Polynomial.C ((m + 2) * a) * Polynomial.X ^ (m + 2) := by
  have c1 : Polynomial.C a + 2 * Polynomial.C (a * ((m + 1 : ℕ) : ℝ)) =
      Polynomial.C ((2 * m + 3) * a) := by
    rw [two_mul, ← Polynomial.C_add, ← Polynomial.C_add]
    congr 1
    push_cast
    ring
  have c2 : Polynomial.C a + Polynomial.C (a * ((m + 1 : ℕ) : ℝ)) =
      Polynomial.C ((m + 2) * a) := by
    rw [← Polynomial.C_add]
    congr 1
    push_cast
    ring
  rw [Polynomial.derivative_C_mul, Polynomial.derivative_X_pow, Nat.add_sub_cancel,
    ← mul_assoc (Polynomial.C a) _ _, ← Polynomial.C_mul]
  linear_combination (Polynomial.X ^ (m + 1)) * c1 - (Polynomial.X ^ (m + 2)) * c2

private noncomputable def psYpoly (N : ℕ) : ℝ[X] :=
  ∑ n ∈ Finset.range (N + 1), Polynomial.C (psC n) * Polynomial.X ^ n

private theorem arcsin_poly_ode (N : ℕ) :
    (1 - Polynomial.X) * psYpoly N +
      (2 * Polynomial.X - Polynomial.X ^ 2) * Polynomial.derivative (psYpoly N) =
      1 - Polynomial.C (((N + 1 : ℕ) : ℝ) * psC N) * Polynomial.X ^ (N + 1) := by
  induction N with
  | zero =>
    have hc0 : psC 0 = 1 := by unfold psC; norm_num
    simp [psYpoly, hc0]
  | succ N IH =>
    have hys : psYpoly (N + 1) = psYpoly N + Polynomial.C (psC (N + 1)) * Polynomial.X ^
        (N + 1) := by
      simp [psYpoly, Finset.sum_range_succ]
    have hstep := ode_step (psC (N + 1)) N
    have hrec := psC_recurrence N
    have hrecC : Polynomial.C ((2 * N + 3) * psC (N + 1)) =
        Polynomial.C (((N + 1 : ℕ) : ℝ) * psC N) := by rw [hrec]
    have htop : Polynomial.C ((((N + 2 : ℕ)) : ℝ) * psC (N + 1)) =
        Polynomial.C (((N : ℝ) + 2) * psC (N + 1)) := by
      rw [Nat.cast_add, Nat.cast_ofNat]
    have eNN : N + 1 + 1 = N + 2 := rfl
    rw [hys, Polynomial.derivative_add]
    rw [eNN]
    linear_combination IH + hstep + (Polynomial.X ^ (N + 1)) * hrecC +
      (Polynomial.X ^ (N + 2)) * htop

private theorem taylor_eq_psAct_rescale_exp_aux (m : ℕ) (h : ℝ) (phi : ℝ[X])
    (hM : phi.natDegree < m + 1) :
    Polynomial.taylor h phi =
      (Polynomial.aeval Polynomial.derivative)
        ((PowerSeries.trunc (m + 1)) (PowerSeries.rescale h (psE))) phi := by
  have stepA : (Polynomial.aeval Polynomial.derivative)
        ((PowerSeries.trunc (m + 1)) (PowerSeries.rescale h (psE))) phi =
      ∑ k ∈ Finset.range (m + 1), h ^ k • Polynomial.hasseDeriv k phi := by
    rw [Polynomial.aeval_eq_sum_range' (PowerSeries.natDegree_trunc_lt _ _),
      LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro k hk
    have hkm : k < m + 1 := Finset.mem_range.mp hk
    have hck : ((PowerSeries.trunc (m + 1)) (PowerSeries.rescale h (psE))).coeff k =
        h ^ k * (1 / (k.factorial : ℝ)) := by
      rw [PowerSeries.coeff_trunc]
      simp only [hkm, ite_true]
      rw [PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
      simp
    have hfact := Polynomial.factorial_smul_hasseDeriv (R := ℝ) k
    have h2 := congrArg (fun F => F phi) hfact
    rw [LinearMap.smul_apply] at h2
    have hF : ((k.factorial : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have e2 : h ^ k * (1 / (k.factorial : ℝ)) * (k.factorial : ℝ) = h ^ k := by
      field_simp
    rw [LinearMap.smul_apply, Module.End.pow_apply, hck, ← h2, nsmul_eq_mul,
      Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul, ← mul_assoc,
      (map_natCast Polynomial.C (k.factorial)).symm, ← map_mul, e2]
  have stepB : Polynomial.taylor h phi =
      ∑ k ∈ Finset.range (m + 1), h ^ k • Polynomial.hasseDeriv k phi := by
    apply Polynomial.ext
    intro n
    have hdeg : (Polynomial.hasseDeriv n phi).natDegree < m + 1 :=
      lt_of_le_of_lt (le_trans (Polynomial.natDegree_hasseDeriv_le phi n) (Nat.sub_le _ _))
        hM
    rw [Polynomial.taylor_coeff, Polynomial.eval_eq_sum_range' hdeg,
      Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Polynomial.coeff_smul, Polynomial.hasseDeriv_coeff, Polynomial.hasseDeriv_coeff,
      smul_eq_mul]
    have echi : (i + n).choose n = (n + i).choose i := by
      rw [add_comm i n]
      exact Nat.choose_symm_add
    rw [echi]
    ring
  rw [stepB, stepA]

private theorem n7_full {A : Type*} [CommRing A] [Algebra ℝ A] (a b : A) (hab : a * b = 1) (n : ℕ) :
    1 + ∑ k ∈ Finset.Icc 1 n,
        (((-1 : ℝ) ^ k * ((n.factorial : ℝ) ^ 2) /
          (((n + k).factorial : ℝ) * ((n - k).factorial : ℝ))) • (a ^ k + b ^ k))
      = (((-1 : ℝ) ^ n * ((n.factorial : ℝ) ^ 2) / ((2 * n).factorial : ℝ)) • (a + b - 2) ^ n) := by
  have e2 : a ^ n * b ^ n = 1 := by rw [← mul_pow, hab, one_pow]
  have hexp := n7_expand a b hab n
  have hsplit := sum_range_two_mul_add_one_eq
    (fun j => ((((-1 : ℝ) ^ n * ((n.factorial : ℝ) ^ 2) / ((2 * n).factorial : ℝ)) *
      (((2 * n).choose j : ℝ)) * (-1 : ℝ) ^ (2 * n - j)) • (a ^ j * b ^ n))) n
  have gup : ∀ k ∈ Finset.Icc 1 n,
      ((((-1 : ℝ) ^ n * ((n.factorial : ℝ) ^ 2) / ((2 * n).factorial : ℝ)) *
        (((2 * n).choose (n + k) : ℝ)) * (-1 : ℝ) ^ (2 * n - (n + k))) • (a ^ (n + k) * b ^ n))
      = (((-1 : ℝ) ^ k * ((n.factorial : ℝ) ^ 2) /
          (((n + k).factorial : ℝ) * ((n - k).factorial : ℝ))) • a ^ k) := by
    intro k hk
    have hkle : k ≤ n := (Finset.mem_Icc.mp hk).2
    have e : a ^ (n + k) * b ^ n = a ^ k := by
      have e3 : a ^ (n + k) = a ^ n * a ^ k := pow_add a n k
      rw [e3, show (a ^ n * a ^ k) * b ^ n = (a ^ n * b ^ n) * a ^ k from by ring, e2,
        one_mul]
    rw [e, scalar_match_upper n k hkle]
  have glo : ∀ k ∈ Finset.Icc 1 n,
      ((((-1 : ℝ) ^ n * ((n.factorial : ℝ) ^ 2) / ((2 * n).factorial : ℝ)) *
        (((2 * n).choose (n - k) : ℝ)) * (-1 : ℝ) ^ (2 * n - (n - k))) • (a ^ (n - k) * b ^ n))
      = (((-1 : ℝ) ^ k * ((n.factorial : ℝ) ^ 2) /
          (((n + k).factorial : ℝ) * ((n - k).factorial : ℝ))) • b ^ k) := by
    intro k hk
    have hkle : k ≤ n := (Finset.mem_Icc.mp hk).2
    have e3 : b ^ n = b ^ (n - k) * b ^ k := by rw [← pow_add, Nat.sub_add_cancel hkle]
    have e4 : a ^ (n - k) * b ^ (n - k) = 1 := by rw [← mul_pow, hab, one_pow]
    have e : a ^ (n - k) * b ^ n = b ^ k := by
      rw [e3, show a ^ (n - k) * (b ^ (n - k) * b ^ k) =
        (a ^ (n - k) * b ^ (n - k)) * b ^ k from by ring, e4, one_mul]
    rw [e, scalar_match_lower n k hkle]
  have gmid : ((((-1 : ℝ) ^ n * ((n.factorial : ℝ) ^ 2) / ((2 * n).factorial : ℝ)) *
        (((2 * n).choose n : ℝ)) * (-1 : ℝ) ^ (2 * n - n)) • (a ^ n * b ^ n)) = 1 := by
    rw [e2, scalar_match_center n, one_smul]
  rw [hexp, hsplit, gmid]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [gup k hk, glo k hk, smul_add]

private theorem taylor_eq_psAct (M : ℕ) (h : ℝ) (phi : ℝ[X]) (hM : phi.natDegree < M) :
    Polynomial.taylor h phi = psAct M (PowerSeries.rescale h (psE)) phi := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : M ≠ 0)
  exact taylor_eq_psAct_rescale_exp_aux m h phi hM

private theorem psAct_exp_pow_shift (M : ℕ) (k : ℕ) (phi : ℝ[X]) (hM : phi.natDegree < M) :
    psAct M (psE ^ k) phi = chapter5PolynomialShift (k : ℝ) phi := by
  rw [exp_pow_eq_rescale, ← taylor_eq_psAct M _ phi hM]
  exact (Polynomial.taylor_apply _ _).trans rfl

private theorem psAct_ebar_pow_shift (M : ℕ) (k : ℕ) (phi : ℝ[X]) (hM : phi.natDegree < M) :
    psAct M (psEb ^ k) phi =
      chapter5PolynomialShift (-(k : ℝ)) phi := by
  rw [rescale_neg_pow, ← taylor_eq_psAct M _ phi hM]
  exact (Polynomial.taylor_apply _ _).trans rfl

private noncomputable def psBeta (n : ℕ) : ℝ :=
  2 ^ n * ((n.factorial : ℝ) ^ 2) / ((2 * n).factorial : ℝ)

private noncomputable def psW : PowerSeries ℝ :=
  1 - PowerSeries.C (1 / 2 : ℝ) *
    (psE + psEb)

private theorem hwe : psE + psEb - 2 =
    (-2 : ℝ) • psW := by
  have hCCmul : (-2 : ℝ) * (1 / 2) = -1 := by norm_num
  have hCC : (PowerSeries.C (-2 : ℝ)) * (PowerSeries.C (1 / 2 : ℝ)) = -1 := by
    rw [← map_mul, hCCmul]
    simp
  have hC2 : (PowerSeries.C (2 : ℝ)) = 2 := rfl
  have hCm2 : (PowerSeries.C (-2 : ℝ)) = -2 := by
    rw [show (-2 : ℝ) = -(2 : ℝ) from rfl, map_neg, hC2]
  have hneg1 : (-1 : PowerSeries ℝ) *
        (psE + psEb) =
      -(psE + psEb) := by
    rw [neg_mul, one_mul]
  rw [Algebra.smul_def, PowerSeries.algebraMap_eq]
  unfold psW
  rw [mul_sub, mul_one, ← mul_assoc, hCC, hCm2, hneg1, sub_neg_eq_add]
  abel

private theorem hbeta (n : ℕ) :
    (((-1 : ℝ) ^ n * ((n.factorial : ℝ) ^ 2) / ((2 * n).factorial : ℝ)) * (-2 : ℝ) ^ n) =
      psBeta n := by
  have h2n : (-1 : ℝ) ^ n * (-2 : ℝ) ^ n = 2 ^ n := by
    rw [← mul_pow]
    norm_num
  have hF : ((2 * n).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  unfold psBeta
  rw [show (-1 : ℝ) ^ n * (n.factorial : ℝ) ^ 2 / ((2 * n).factorial : ℝ) * (-2 : ℝ) ^ n =
    ((-1 : ℝ) ^ n * (-2 : ℝ) ^ n) * ((n.factorial : ℝ) ^ 2 / ((2 * n).factorial : ℝ)) from by ring,
    h2n]
  ring

private theorem entry2F_eq_smul_psAct (phi : ℝ[X]) (n M : ℕ) (hM : phi.natDegree < M) :
    chapter5Entry2F phi n = psBeta n • psAct M (psW ^ n) phi := by
  have hN7 := n7_full (psE) (psEb)
    exp_mul_rescale_neg_eq_one n
  have hbridge : (psE + psEb - 2) ^ n =
      ((-2 : ℝ) ^ n) • psW ^ n := by
    rw [hwe, smul_pow]
  have hbeta' : (((-1 : ℝ) ^ n * ((n.factorial : ℝ) ^ 2) / ((2 * n).factorial : ℝ)) *
      (-2 : ℝ) ^ n) • psAct M (psW ^ n) phi = psBeta n • psAct M (psW ^ n) phi := by
    rw [hbeta n]
  have key : psAct M (1 + ∑ k ∈ Finset.Icc 1 n,
      (((-1 : ℝ) ^ k * ((n.factorial : ℝ) ^ 2) /
        (((n + k).factorial : ℝ) * ((n - k).factorial : ℝ))) •
        (psE ^ k + psEb ^ k))) phi =
      chapter5Entry2F phi n := by
    rw [psAct_add, LinearMap.add_apply, psAct_sum, LinearMap.sum_apply, psAct_one M phi hM]
    unfold chapter5Entry2F
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [psAct_smul, LinearMap.smul_apply, psAct_add, LinearMap.add_apply,
      psAct_exp_pow_shift M k phi hM, psAct_ebar_pow_shift M k phi hM,
      smul_add, Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul, ← mul_add]
  rw [← key, hN7, hbridge, psAct_smul, LinearMap.smul_apply, psAct_smul,
    LinearMap.smul_apply, ← mul_smul]
  exact hbeta'

private theorem psW_pow_dvd (n : ℕ) : PowerSeries.X ^ (2 * n) ∣ psW ^ n := by
  have hC2 : (2 : PowerSeries ℝ) = PowerSeries.C 2 := rfl
  have hC12 : PowerSeries.C (1 / 2 : ℝ) * 2 = 1 := by
    rw [hC2, ← map_mul]
    norm_num
  have h2 : PowerSeries.X ^ 2 ∣ psW := by
    have hneg : PowerSeries.C (-1 / 2 : ℝ) = -PowerSeries.C (1 / 2 : ℝ) := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2) from by ring, map_neg]
    have hsub : psW = PowerSeries.C (-1 / 2 : ℝ) *
        (psE + psEb - 2) := by
      unfold psW
      rw [hneg, neg_mul, mul_sub, neg_sub, hC12]
    rw [hsub]
    exact Dvd.dvd.mul_left exp_add_rescale_sub_two _
  have h3 : (PowerSeries.X ^ 2) ^ n ∣ psW ^ n := pow_dvd_pow_of_dvd h2 n
  rwa [pow_mul]

private theorem entry2F_eq_zero_of_natDegree_lt (phi : ℝ[X]) (n : ℕ)
    (hlt : phi.natDegree < 2 * n) : chapter5Entry2F phi n = 0 := by
  have hM : phi.natDegree < phi.natDegree + 1 := Nat.lt_succ_self _
  rw [entry2F_eq_smul_psAct phi n (phi.natDegree + 1) hM]
  have hkill : psAct (phi.natDegree + 1) (psW ^ n) phi = 0 := by
    apply psAct_eq_zero_of_X_pow_dvd _ _ _ (psW_pow_dvd n) hlt
  rw [hkill, _root_.smul_zero]

private noncomputable def psY (N : ℕ) : PowerSeries ℝ := Polynomial.aeval psW (psYpoly N)

private noncomputable def psG (N : ℕ) : PowerSeries ℝ :=
  (psE - psEb) * psY N -
    PowerSeries.C (2 : ℝ) * PowerSeries.X

private theorem psC2 : (2 : PowerSeries ℝ) = PowerSeries.C 2 := rfl

private theorem psC4 : (4 : PowerSeries ℝ) = PowerSeries.C 4 := rfl

private theorem h2C12 : (2 : PowerSeries ℝ) * PowerSeries.C (1 / 2 : ℝ) = 1 := by
  rw [psC2, ← map_mul]
  norm_num [map_one]

private theorem hC14 : PowerSeries.C (1 / 2 : ℝ) * 4 = PowerSeries.C (2 : ℝ) := by
  rw [psC4, ← map_mul]
  norm_num

private theorem h2cC : PowerSeries.C (1 / 2 : ℝ) * PowerSeries.C (2 : ℝ) = 1 := by
  rw [← map_mul]
  norm_num [map_one]

private theorem psB2 : psE + psEb =
    2 * (1 - psW) := by
  have e1 : 1 - psW = PowerSeries.C (1 / 2 : ℝ) *
      (psE + psEb) := by
    unfold psW
    ring
  rw [e1, ← mul_assoc, h2C12, one_mul]

private theorem psB2C : psE + psEb =
    PowerSeries.C (2 : ℝ) * (1 - psW) := by
  have h := psB2
  rwa [psC2] at h

private theorem pssq : (psE - psEb) *
    (psE - psEb) =
    (psE + psEb) *
      (psE + psEb) - 4 :=
  by linear_combination (-4) * exp_mul_rescale_neg_eq_one

private theorem psDs : PowerSeries.derivative
    (psE - psEb) =
    psE + psEb := by
  rw [map_sub, PowerSeries.derivative_exp, derivative_rescale_neg_exp, sub_neg_eq_add]

private theorem psDw : PowerSeries.derivative psW =
    -(PowerSeries.C (1 / 2 : ℝ) *
      (psE - psEb)) := by
  have e1 : PowerSeries.derivative
      (PowerSeries.C (1 / 2 : ℝ) *
        (psE + psEb)) =
      PowerSeries.C (1 / 2 : ℝ) *
        (psE + -psEb) := by
    rw [Derivation.leibniz, PowerSeries.derivative_C, map_add, PowerSeries.derivative_exp,
      derivative_rescale_neg_exp, smul_eq_mul, smul_eq_mul, mul_zero, add_zero]
  have e0 : (1 : PowerSeries ℝ) = PowerSeries.C (1 : ℝ) := (map_one PowerSeries.C).symm
  unfold psW
  rw [map_sub, e0, PowerSeries.derivative_C, e1, zero_sub, sub_eq_add_neg]

private theorem psD2X : PowerSeries.derivative (PowerSeries.C (2 : ℝ) * PowerSeries.X) =
    PowerSeries.C (2 : ℝ) := by
  rw [Derivation.leibniz, PowerSeries.derivative_X, PowerSeries.derivative_C, smul_eq_mul,
    smul_eq_mul, mul_one, mul_zero, add_zero]

private theorem psMapped (N : ℕ) : (1 - psW) * psY N +
    (PowerSeries.C (2 : ℝ) * psW - psW * psW) *
      Polynomial.aeval psW (Polynomial.derivative (psYpoly N)) =
    1 - PowerSeries.C (((N + 1 : ℕ) : ℝ) * psC N) * psW ^ (N + 1) := by
  have hN10 := arcsin_poly_ode N
  have hmap := congrArg (Polynomial.aeval psW) hN10
  simp only [map_add, map_sub, map_mul, map_one, Polynomial.aeval_X, map_pow,
    Polynomial.aeval_C, PowerSeries.algebraMap_eq] at hmap
  rw [map_ofNat, pow_two, ← map_mul, psC2] at hmap
  unfold psY
  linear_combination hmap

private theorem cC2bridge : PowerSeries.C (1 / 2 : ℝ) *
    (PowerSeries.C (2 : ℝ) * PowerSeries.C (2 : ℝ)) = PowerSeries.C (2 : ℝ) := by
  rw [← mul_assoc, h2cC, one_mul]

private theorem psBCOMB : PowerSeries.C (1 / 2 : ℝ) *
    ((psE + psEb) *
      (psE + psEb)) =
    PowerSeries.C (2 : ℝ) * ((1 - psW) * (1 - psW)) := by
  rw [psB2C, show PowerSeries.C (1 / 2 : ℝ) *
      ((PowerSeries.C (2 : ℝ) * (1 - psW)) * (PowerSeries.C (2 : ℝ) * (1 - psW))) =
      (PowerSeries.C (1 / 2 : ℝ) * (PowerSeries.C (2 : ℝ) * PowerSeries.C (2 : ℝ))) *
        ((1 - psW) * (1 - psW)) from by ring, cC2bridge]

private theorem psDeriv (N : ℕ) : PowerSeries.derivative (psG N) =
    -(PowerSeries.C (2 : ℝ) * PowerSeries.C (((N + 1 : ℕ) : ℝ) * psC N)) * psW ^ (N + 1) := by
  have E1 : PowerSeries.derivative (psG N) =
      PowerSeries.derivative ((psE -
        psEb) * psY N) -
        PowerSeries.derivative (PowerSeries.C (2 : ℝ) * PowerSeries.X) := by
    unfold psG
    rw [map_sub]
  have E2 : PowerSeries.derivative
      ((psE - psEb) * psY N) =
      (psE - psEb) *
        PowerSeries.derivative (psY N) +
        psY N * PowerSeries.derivative
          (psE - psEb) := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have E4 : PowerSeries.derivative (psY N) =
      Polynomial.aeval psW (Polynomial.derivative (psYpoly N)) *
        PowerSeries.derivative psW := by
    unfold psY
    rw [Derivation.map_aeval, smul_eq_mul]
  linear_combination E1 + E2 +
    (psE - psEb) * E4 +
    psY N * psDs +
    ((psE - psEb) *
      Polynomial.aeval psW (Polynomial.derivative (psYpoly N))) * psDw -
    psD2X +
    (-(PowerSeries.C (1 / 2 : ℝ)) *
      Polynomial.aeval psW (Polynomial.derivative (psYpoly N))) * pssq +
    (-Polynomial.aeval psW (Polynomial.derivative (psYpoly N))) * psBCOMB +
    (Polynomial.aeval psW (Polynomial.derivative (psYpoly N))) * hC14 +
    (PowerSeries.C (2 : ℝ)) * psMapped N +
    (psY N) * psB2C +
    ((Polynomial.aeval psW (Polynomial.derivative (psYpoly N))) *
      PowerSeries.C (2 : ℝ) * psW) * psC2

private theorem psConstCoeff (N : ℕ) : PowerSeries.constantCoeff (psG N) = 0 := by
  have hs : PowerSeries.constantCoeff
      (psE - psEb) = 0 := by
    rw [map_sub, PowerSeries.constantCoeff_exp]
    have h1 : PowerSeries.constantCoeff (psEb) = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff]
      exact coeff0_rescale_neg_exp
    rw [h1, sub_self]
  have h2 : PowerSeries.constantCoeff (PowerSeries.C (2 : ℝ) * PowerSeries.X) = 0 := by
    rw [map_mul, PowerSeries.constantCoeff_X, mul_zero]
  unfold psG
  rw [map_sub, map_mul, hs, zero_mul, h2, sub_self]

private theorem psDvd (N : ℕ) : PowerSeries.X ^ (2 * N + 3) ∣ psG N := by
  have hD : PowerSeries.X ^ (2 * N + 2) ∣ PowerSeries.derivative (psG N) := by
    rw [psDeriv N]
    have hw : PowerSeries.X ^ (2 * N + 2) ∣ psW ^ (N + 1) := by
      have h := psW_pow_dvd (N + 1)
      have e2 : 2 * (N + 1) = 2 * N + 2 := by ring
      rwa [e2] at h
    exact Dvd.dvd.mul_left hw _
  have h0 := psConstCoeff N
  have h := x_pow_succ_dvd_of_derivative h0 hD
  have e : 2 * N + 2 + 1 = 2 * N + 3 := by omega
  rwa [e] at h

private theorem hcb (n : ℕ) : (1 / (((2 * n + 1 : ℕ)) : ℝ)) * psBeta n = psC n := by
  have hF1 : ((((2 * n + 1 : ℕ))) : ℝ) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    omega
  have hF2 : ((2 * n).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  unfold psBeta psC
  rw [Nat.factorial_succ]
  push_cast
  field_simp

private theorem hYbridge (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), (psC n) • psW ^ n) = psY N := by
  unfold psY psYpoly
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_mul, Polynomial.aeval_C, PowerSeries.algebraMap_eq, Polynomial.aeval_X_pow,
    Algebra.smul_def, PowerSeries.algebraMap_eq]

private theorem psAct_sub (M : ℕ) (f g : PowerSeries ℝ) (phi : ℝ[X]) :
    psAct M (f - g) phi = psAct M f phi - psAct M g phi := by
  unfold psAct
  rw [map_sub, map_sub, LinearMap.sub_apply]

private theorem minus_identity (phi : ℝ[X]) :
    chapter5PolynomialShift 1 (chapter5Entry2MinusSolution phi) -
      chapter5PolynomialShift (-1) (chapter5Entry2MinusSolution phi) =
      Polynomial.C 2 * phi.derivative := by
  have hM : phi.natDegree < phi.natDegree + 1 := Nat.lt_succ_self _
  have hN2 : phi.natDegree < 2 * (phi.natDegree / 2) + 3 := by omega
  have hMinus : chapter5Entry2MinusSolution phi =
      psAct (phi.natDegree + 1)
        (∑ n ∈ Finset.range (phi.natDegree / 2 + 1), (psC n) • psW ^ n) phi := by
    unfold chapter5Entry2MinusSolution
    rw [psAct_sum, LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← Polynomial.smul_eq_C_mul, entry2F_eq_smul_psAct phi n _ hM, ← mul_smul,
      hcb n, ← LinearMap.smul_apply, ← psAct_smul]
  have hMd : (chapter5Entry2MinusSolution phi).natDegree < phi.natDegree + 1 := by
    rw [hMinus]
    exact lt_of_le_of_lt (psAct_natDegree_le _ _ _) hM
  have sh1 : chapter5PolynomialShift (1 : ℝ) (chapter5Entry2MinusSolution phi) =
      psAct (phi.natDegree + 1) (psE *
        (∑ n ∈ Finset.range (phi.natDegree / 2 + 1), (psC n) • psW ^ n)) phi := by
    have t1 : chapter5PolynomialShift (1 : ℝ) (chapter5Entry2MinusSolution phi) =
        psAct (phi.natDegree + 1) (PowerSeries.rescale 1 (psE))
          (chapter5Entry2MinusSolution phi) :=
      ((Polynomial.taylor_apply _ _).trans rfl).symm.trans (taylor_eq_psAct _ 1 _ hMd)
    rw [t1, hMinus, ← psAct_mul _ _ _ phi hM, rescale_one_exp]
  have sh2 : chapter5PolynomialShift (-1 : ℝ) (chapter5Entry2MinusSolution phi) =
      psAct (phi.natDegree + 1) (psEb *
        (∑ n ∈ Finset.range (phi.natDegree / 2 + 1), (psC n) • psW ^ n)) phi := by
    have t2 : chapter5PolynomialShift (-1 : ℝ) (chapter5Entry2MinusSolution phi) =
        psAct (phi.natDegree + 1) (psEb)
          (chapter5Entry2MinusSolution phi) :=
      ((Polynomial.taylor_apply _ _).trans rfl).symm.trans (taylor_eq_psAct _ (-1) _ hMd)
    rw [t2, hMinus, ← psAct_mul _ _ _ phi hM]
  have hkill : psAct (phi.natDegree + 1) (psG (phi.natDegree / 2)) phi = 0 :=
    psAct_eq_zero_of_X_pow_dvd _ _ _ (psDvd _) hN2
  have hC2X : psAct (phi.natDegree + 1)
      (PowerSeries.C (2 : ℝ) * PowerSeries.X) phi = Polynomial.C 2 * phi.derivative := by
    have e1 : psAct (phi.natDegree + 1)
        (PowerSeries.C (2 : ℝ) * PowerSeries.X) phi =
        psAct (phi.natDegree + 1) (PowerSeries.C (2 : ℝ))
          (psAct (phi.natDegree + 1) PowerSeries.X phi) :=
      psAct_mul _ _ _ phi hM
    have hDd : (phi.derivative).natDegree < phi.natDegree + 1 :=
      lt_of_le_of_lt (Polynomial.natDegree_derivative_le _) (by omega)
    rw [e1, psAct_X_pow _ _ hM, psAct_C _ _ _ hDd, Polynomial.smul_eq_C_mul]
  have hSY : (psE - psEb) *
      (∑ n ∈ Finset.range (phi.natDegree / 2 + 1), (psC n) • psW ^ n) =
      psG (phi.natDegree / 2) + PowerSeries.C (2 : ℝ) * PowerSeries.X := by
    rw [hYbridge]
    unfold psG
    rw [sub_add_cancel]
  rw [sh1, sh2, ← psAct_sub, ← sub_mul, hSY, psAct_add, LinearMap.add_apply, hkill, hC2X,
    zero_add]

private theorem hpb (n : ℕ) : ((Nat.choose (2 * n) n : ℝ) / (2 : ℝ) ^ n) * psBeta n = 1 := by
  have key : ((Nat.choose (2 * n) n : ℝ)) * ((n.factorial : ℝ) ^ 2) =
      ((2 * n).factorial : ℝ) := by
    have h := Nat.add_choose_mul_factorial_mul_factorial n n
    have h2 : n + n = 2 * n := by ring
    rw [h2] at h
    rw [sq, ← mul_assoc]
    exact_mod_cast h
  have h2n : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hF : ((2 * n).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  unfold psBeta
  field_simp
  linear_combination key

private theorem plus_identity (phi : ℝ[X]) :
    chapter5PolynomialShift 1 (chapter5Entry2PlusSolution phi) +
      chapter5PolynomialShift (-1) (chapter5Entry2PlusSolution phi) =
      Polynomial.C 2 * phi := by
  have hM : phi.natDegree < phi.natDegree + 1 := Nat.lt_succ_self _
  have hN2 : phi.natDegree < 2 * (phi.natDegree / 2) + 2 := by omega
  have hPlus : chapter5Entry2PlusSolution phi =
      psAct (phi.natDegree + 1)
        (∑ n ∈ Finset.range (phi.natDegree / 2 + 1), psW ^ n) phi := by
    unfold chapter5Entry2PlusSolution
    rw [psAct_sum, LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← Polynomial.smul_eq_C_mul, entry2F_eq_smul_psAct phi n _ hM, ← mul_smul,
      hpb n, one_smul]
  have hMd : (chapter5Entry2PlusSolution phi).natDegree < phi.natDegree + 1 := by
    rw [hPlus]
    exact lt_of_le_of_lt (psAct_natDegree_le _ _ _) hM
  have sh1 : chapter5PolynomialShift (1 : ℝ) (chapter5Entry2PlusSolution phi) =
      psAct (phi.natDegree + 1) (psE *
        (∑ n ∈ Finset.range (phi.natDegree / 2 + 1), psW ^ n)) phi := by
    have t1 : chapter5PolynomialShift (1 : ℝ) (chapter5Entry2PlusSolution phi) =
        psAct (phi.natDegree + 1) (PowerSeries.rescale 1 (psE))
          (chapter5Entry2PlusSolution phi) :=
      ((Polynomial.taylor_apply _ _).trans rfl).symm.trans (taylor_eq_psAct _ 1 _ hMd)
    rw [t1, hPlus, ← psAct_mul _ _ _ phi hM, rescale_one_exp]
  have sh2 : chapter5PolynomialShift (-1 : ℝ) (chapter5Entry2PlusSolution phi) =
      psAct (phi.natDegree + 1) (psEb *
        (∑ n ∈ Finset.range (phi.natDegree / 2 + 1), psW ^ n)) phi := by
    have t2 : chapter5PolynomialShift (-1 : ℝ) (chapter5Entry2PlusSolution phi) =
        psAct (phi.natDegree + 1) (psEb)
          (chapter5Entry2PlusSolution phi) :=
      ((Polynomial.taylor_apply _ _).trans rfl).symm.trans (taylor_eq_psAct _ (-1) _ hMd)
    rw [t2, hPlus, ← psAct_mul _ _ _ phi hM]
  have geom : (1 - psW) * (∑ n ∈ Finset.range (phi.natDegree / 2 + 1), psW ^ n) =
      1 - psW ^ (phi.natDegree / 2 + 1) := by
    have h := mul_geom_sum psW (phi.natDegree / 2 + 1)
    linear_combination -h
  have hEE : (psE + psEb) *
      (∑ n ∈ Finset.range (phi.natDegree / 2 + 1), psW ^ n) =
      2 - 2 * psW ^ (phi.natDegree / 2 + 1) := by
    rw [psB2, mul_assoc, geom, mul_sub, mul_one]
  have hkill2 : psAct (phi.natDegree + 1) (psW ^ (phi.natDegree / 2 + 1)) phi = 0 :=
    psAct_eq_zero_of_X_pow_dvd _ _ _ (psW_pow_dvd _) hN2
  have h2phi : psAct (phi.natDegree + 1) (2 : PowerSeries ℝ) phi = (2 : ℝ) • phi := by
    rw [psC2]
    exact psAct_C _ 2 _ hM
  have h2w : psAct (phi.natDegree + 1)
      ((2 : PowerSeries ℝ) * psW ^ (phi.natDegree / 2 + 1)) phi = 0 := by
    have e : (2 : PowerSeries ℝ) * psW ^ (phi.natDegree / 2 + 1) =
        (2 : ℝ) • psW ^ (phi.natDegree / 2 + 1) := by
      rw [Algebra.smul_def, PowerSeries.algebraMap_eq, psC2]
    rw [e, psAct_smul, LinearMap.smul_apply, hkill2, smul_zero]
  rw [sh1, sh2, ← LinearMap.add_apply, ← psAct_add, ← add_mul, hEE, psAct_sub, h2phi,
    h2w, sub_zero, Polynomial.smul_eq_C_mul]

/-- **Ramanujan's solutions of two central difference equations.** Let $\varphi$ be a real
polynomial of degree $d$ (with $d = 0$ for $\varphi = 0$). For $n \ge 0$ let
$F_n(x) = \varphi(x) + \sum_{k=1}^{n} \frac{(-1)^k (n!)^2}{(n+k)!\,(n-k)!}
\bigl(\varphi(x+k) + \varphi(x-k)\bigr)$, and let
$M = \sum_{n=0}^{\lfloor d/2 \rfloor} \frac{1}{2n+1} F_n$ and
$P = \sum_{n=0}^{\lfloor d/2 \rfloor} \binom{2n}{n} 2^{-n} F_n$. Then $F_n = 0$ for every $n$
with $d < 2n$, $M(x+1) - M(x-1) = 2 \varphi'(x)$ and $P(x+1) + P(x-1) = 2 \varphi(x)$, as
polynomials in $x$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 5,
Entry 2(i), pp. 111–112.
-/
theorem ramanujan_part1_ch5_entry2i_euleriangf (phi : ℝ[X]) :
    (∀ n : ℕ, phi.natDegree < 2 * n → chapter5Entry2F phi n = 0) ∧
      chapter5PolynomialShift 1 (chapter5Entry2MinusSolution phi) -
          chapter5PolynomialShift (-1) (chapter5Entry2MinusSolution phi) =
        Polynomial.C 2 * phi.derivative ∧
      chapter5PolynomialShift 1 (chapter5Entry2PlusSolution phi) +
          chapter5PolynomialShift (-1) (chapter5Entry2PlusSolution phi) =
        Polynomial.C 2 * phi := by
  exact ⟨entry2F_eq_zero_of_natDegree_lt phi, minus_identity phi, plus_identity phi⟩

end
end Entry2iEuleriangf
end MathlibExt.Analysis.Ramanujan.Part1Ch5
end
