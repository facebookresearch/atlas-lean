/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Basic
public import MathlibExt.Analysis.Ramanujan.Part1Ch8Entry12Qgammaintegers
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Data.Set.Countable
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import MathlibExt.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 8

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8

namespace Entry11Qgammafunctional

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter8Digamma (z : ℂ) : ℂ :=
  deriv Complex.Gamma z / Complex.Gamma z

def chapter8PhiTerm (x : ℂ) (j : ℕ) : ℂ :=
  let k := j + 1
  2 / ((((k : ℂ) * x) ^ 3) - (k : ℂ) * x)

def chapter8Phi (x : ℂ) : ℂ :=
  1 + ∑' j : ℕ, chapter8PhiTerm x j

/-- **Digamma as the logarithmic derivative of Gamma (used for Chapter 8, Entry 11).** For every
complex number $z$, $\Gamma'(z)/\Gamma(z) = \psi(z)$, where $\psi$ is the digamma function.

At the poles $z = 0, -1, -2, \dots$ the conventions $\Gamma(z) = 0$ and division by zero giving
$0$ make both sides $0$, so the identity holds for every $z$. -/
theorem chapter8Digamma_eq_digamma (z : ℂ) :
    chapter8Digamma z = Complex.digamma z := by
  unfold chapter8Digamma
  rw [Complex.digamma_def, logDeriv_apply]

/-- Entry 11's `chapter8PhiTerm` agrees with Entry 12's version. -/
theorem chapter8PhiTerm_eq_entry12Qgammaintegers (x : ℂ) (j : ℕ) :
    chapter8PhiTerm x j =
      MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry12Qgammaintegers.chapter8PhiTerm x j := by
  unfold chapter8PhiTerm
    MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry12Qgammaintegers.chapter8PhiTerm
  rfl

/-- **The Entry 11 and Entry 12 definitions of $\varphi$ agree.** For every complex number $x$,
the function $\varphi(x) = 1 + \sum_{k \ge 1} \frac{2}{(kx)^3 - kx}$ as defined for Entry 11
equals the function given by the same formula for Entry 12.

In both definitions the sum is the unconditional sum, taken to be $0$ when it does not converge,
and a term with zero denominator is $0$. -/
theorem chapter8Phi_eq_entry12Qgammaintegers (x : ℂ) :
    chapter8Phi x =
      MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry12Qgammaintegers.chapter8Phi x := by
  simp only [chapter8Phi,
    MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry12Qgammaintegers.chapter8Phi,
    chapter8PhiTerm_eq_entry12Qgammaintegers]

private lemma chapter8PhiTermNormBound (x : ℂ) (hx0 : x ≠ 0)
    (hpoles : ∀ k : ℕ,
      x ≠ 1 / ((k + 1 : ℕ) : ℂ) ∧
        x ≠ -(1 / ((k + 1 : ℕ) : ℂ)))
    (j : ℕ)
    (hbig : (2 : ℝ) ≤ ((((j + 1 : ℕ)) : ℝ) * ‖x‖) ^ 2) :
    ‖chapter8PhiTerm x j‖ ≤ (4 / ‖x‖ ^ 3) * (1 / ((((j + 1 : ℕ)) : ℝ) ^ 2)) := by
  have hr : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx0
  have hkC : ((j + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  have hkR : (1 : ℝ) ≤ ((((j + 1 : ℕ)) : ℝ)) := by
    have : 1 ≤ j + 1 := Nat.le_add_left 1 j
    exact_mod_cast this
  have hterm : chapter8PhiTerm x j =
      2 / (((((j + 1 : ℕ) : ℂ) * x) ^ 3 - ((j + 1 : ℕ) : ℂ) * x)) := by
    simp only [chapter8PhiTerm]
  rw [hterm]
  set kC : ℂ := ((j + 1 : ℕ) : ℂ) with hkdef
  set kR : ℝ := (((j + 1 : ℕ)) : ℝ) with hkRdef
  set c : ℂ := kC * x with hcdef
  have hcnorm : ‖c‖ = kR * ‖x‖ := by
    rw [hcdef, norm_mul, Complex.norm_natCast]
  have hkRpos : (0 : ℝ) < kR := by linarith
  have hcpos : (0 : ℝ) < ‖c‖ := by rw [hcnorm]; positivity
  have hDne : (c ^ 3 - c) ≠ 0 := by
    have hk : ((j + 1 : ℕ) : ℂ) ≠ 0 := hkC
    have h1 := (hpoles j).1
    have h2 := (hpoles j).2
    have hc0 : c ≠ 0 := mul_ne_zero hk hx0
    have hc1 : c ≠ 1 := by
      intro h
      apply h1
      have : x = 1 / kC := by
        rw [hcdef] at h
        field_simp at h ⊢
        linear_combination h
      rwa [hkdef] at this
    have hcm1 : c ≠ -1 := by
      intro h
      apply h2
      have : x = -(1 / kC) := by
        rw [hcdef] at h
        field_simp at h ⊢
        linear_combination h
      rwa [hkdef] at this
    have hfac : c ^ 3 - c = c * (c - 1) * (c + 1) := by ring
    have hsub : c - 1 ≠ 0 := by intro h; apply hc1; linear_combination h
    have hadd : c + 1 ≠ 0 := by intro h; apply hcm1; linear_combination h
    rw [hfac]
    exact mul_ne_zero (mul_ne_zero hc0 hsub) hadd
  have hDpos : (0 : ℝ) < ‖c ^ 3 - c‖ := norm_pos_iff.mpr hDne
  have hnorm2 : ‖(2 : ℂ) / (c ^ 3 - c)‖ = 2 / ‖c ^ 3 - c‖ := by
    rw [norm_div]
    norm_num
  rw [hnorm2]
  have hfac : c ^ 3 - c = c * (c ^ 2 - 1) := by ring
  have hDnorm : ‖c ^ 3 - c‖ = ‖c‖ * ‖c ^ 2 - 1‖ := by
    rw [hfac, norm_mul]
  have hcsq : ‖c ^ 2 - 1‖ ≥ ‖c‖ ^ 2 - 1 := by
    have h := norm_sub_norm_le (c ^ 2) (1 : ℂ)
    rwa [norm_pow, norm_one] at h
  have hbigc : (2 : ℝ) ≤ ‖c‖ ^ 2 := by
    rw [hcnorm]
    simpa [hkRdef] using hbig
  have hlow : ‖c‖ ^ 2 / 2 ≤ ‖c ^ 2 - 1‖ := by linarith
  have hDlow : ‖c‖ ^ 3 / 2 ≤ ‖c ^ 3 - c‖ := by
    rw [hDnorm]
    have hmul : ‖c‖ * (‖c‖ ^ 2 / 2) = ‖c‖ ^ 3 / 2 := by ring
    calc ‖c‖ ^ 3 / 2 = ‖c‖ * (‖c‖ ^ 2 / 2) := by rw [hmul]
      _ ≤ ‖c‖ * ‖c ^ 2 - 1‖ := by
        apply mul_le_mul_of_nonneg_left hlow (le_of_lt hcpos)
  have hstep : 2 / ‖c ^ 3 - c‖ ≤ 4 / ‖c‖ ^ 3 := by
    have heq : (4 : ℝ) / ‖c‖ ^ 3 = 2 / (‖c‖ ^ 3 / 2) := by ring
    rw [heq]
    gcongr
  calc 2 / ‖c ^ 3 - c‖ ≤ 4 / ‖c‖ ^ 3 := hstep
    _ = (4 / ‖x‖ ^ 3) * (1 / kR ^ 3) := by
        rw [hcnorm]
        field_simp
    _ ≤ (4 / ‖x‖ ^ 3) * (1 / kR ^ 2) := by
        have hCnn : (0 : ℝ) ≤ 4 / ‖x‖ ^ 3 := by positivity
        apply mul_le_mul_of_nonneg_left _ hCnn
        apply one_div_le_one_div_of_le _ _
        · positivity
        · have : kR ^ 2 ≤ kR ^ 3 := by
            calc kR ^ 2 = kR ^ 2 * 1 := by ring
              _ ≤ kR ^ 2 * kR := by
                apply mul_le_mul_of_nonneg_left hkR (by positivity)
              _ = kR ^ 3 := by ring
          exact this

private lemma chapter8PhiSummable (x : ℂ) (hx0 : x ≠ 0)
    (hpoles : ∀ k : ℕ,
      x ≠ 1 / ((k + 1 : ℕ) : ℂ) ∧
        x ≠ -(1 / ((k + 1 : ℕ) : ℂ))) :
    Summable (chapter8PhiTerm x) := by
  have hr : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx0
  set C : ℝ := 4 / ‖x‖ ^ 3 with hCdef
  have hsum_base : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  have hsum_scaled : Summable (fun n : ℕ => C * ((1 : ℝ) / ((n : ℝ) ^ 2))) :=
    hsum_base.mul_left C
  have hsum_shift :
      Summable (fun j : ℕ => C * ((1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2))) := by
    have h := (summable_nat_add_iff (k := 1)).mpr hsum_scaled
    simpa using h
  apply Summable.of_norm_bounded_eventually
    (g := fun j : ℕ => C * ((1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2))) hsum_shift
  rw [Nat.cofinite_eq_atTop]
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, (2 : ℝ) ≤ ((N0 : ℝ) * ‖x‖) ^ 2 := by
    obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, (Real.sqrt 2 / ‖x‖) ≤ N0 :=
      ⟨⌈Real.sqrt 2 / ‖x‖⌉₊, Nat.le_ceil _⟩
    refine ⟨N0, ?_⟩
    have h1 : Real.sqrt 2 ≤ (N0 : ℝ) * ‖x‖ := by
      rw [div_le_iff₀ hr] at hN0
      linarith [hN0]
    calc (2 : ℝ) = (Real.sqrt 2) ^ 2 := by rw [Real.sq_sqrt (by norm_num)]
      _ ≤ ((N0 : ℝ) * ‖x‖) ^ 2 := by
        apply pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  filter_upwards [eventually_ge_atTop N0] with j hj
  have hmono : ((N0 : ℝ) * ‖x‖) ^ 2 ≤ ((((j + 1 : ℕ)) : ℝ) * ‖x‖) ^ 2 := by
    have hle : (N0 : ℝ) ≤ ((((j + 1 : ℕ)) : ℝ)) := by
      have : N0 ≤ j + 1 := by
        calc N0 ≤ j := hj
          _ ≤ j + 1 := Nat.le_add_right j 1
      exact_mod_cast this
    have hle2 : (N0 : ℝ) * ‖x‖ ≤ ((((j + 1 : ℕ)) : ℝ)) * ‖x‖ := by
      apply mul_le_mul_of_nonneg_right hle (le_of_lt hr)
    apply pow_le_pow_left₀ (by positivity) hle2 2
  have hbig : (2 : ℝ) ≤ ((((j + 1 : ℕ)) : ℝ) * ‖x‖) ^ 2 := le_trans hN0 hmono
  simpa [hCdef] using chapter8PhiTermNormBound x hx0 hpoles j hbig

private lemma chapter8GammaOneDivAvoid (x : ℂ) (hx0 : x ≠ 0)
    (hpoles : ∀ k : ℕ,
      x ≠ 1 / ((k + 1 : ℕ) : ℂ) ∧
        x ≠ -(1 / ((k + 1 : ℕ) : ℂ)))
    (m : ℕ) : (1 / x : ℂ) ≠ -(m : ℂ) := by
  intro hm
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simp only [Nat.cast_zero, neg_zero] at hm
    exact (div_ne_zero one_ne_zero hx0) hm
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, (Nat.sub_add_cancel hpos).symm⟩
    have h2 := (hpoles k).2
    apply h2
    have hxinv : x⁻¹ = -((k + 1 : ℕ) : ℂ) := by simpa [one_div] using hm
    have hinv : x⁻¹⁻¹ = (-((k + 1 : ℕ) : ℂ))⁻¹ := by rw [hxinv]
    rw [inv_inv] at hinv
    rw [hinv, inv_neg, ← one_div]

private lemma chapter8GammaOneSubAvoid (x : ℂ)
    (hpoles : ∀ k : ℕ,
      x ≠ 1 / ((k + 1 : ℕ) : ℂ) ∧
        x ≠ -(1 / ((k + 1 : ℕ) : ℂ)))
    (m : ℕ) : (1 - 1 / x : ℂ) ≠ -(m : ℂ) := by
  intro hm
  have h1 := (hpoles m).1
  apply h1
  have h12 : (1 : ℂ) / x = 1 + (m : ℂ) := by linear_combination -hm
  have hcast : ((m + 1 : ℕ) : ℂ) = 1 + (m : ℂ) := by push_cast; ring
  have hxinv : x⁻¹ = ((m + 1 : ℕ) : ℂ) := by
    rw [hcast]
    simpa [one_div] using h12
  have hinv : x⁻¹⁻¹ = (((m + 1 : ℕ) : ℂ))⁻¹ := by rw [hxinv]
  rw [inv_inv] at hinv
  rw [hinv, ← one_div]

private def U : Set ℂ := (Set.range ((↑) : ℤ → ℂ))ᶜ

private def digTerm (j : ℕ) (w : ℂ) : ℂ :=
  1 / ((j + 1 : ℕ) : ℂ) - 1 / (w + ((j + 1 : ℕ) : ℂ))

private def digF (w : ℂ) : ℂ :=
  Complex.digamma (w + 1) + (Real.eulerMascheroniConstant : ℂ)

private def digG (w : ℂ) : ℂ :=
  ∑' j : ℕ, digTerm j w

private lemma U_isOpen : IsOpen U :=
  Complex.isOpen_compl_range_intCast

private lemma U_preconnected : IsPreconnected U :=
  (Set.Countable.isConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num)
    (Set.countable_range _)).2

private lemma U_mem_iff (w : ℂ) :
    w ∈ U ↔ ∀ n : ℤ, w ≠ ((n : ℤ) : ℂ) := by
  simp only [U, Set.mem_compl_iff, Set.mem_range, not_exists, ne_comm]

private lemma K_ne (j : ℕ) : ((j + 1 : ℕ) : ℂ) ≠ 0 := by
  exact_mod_cast Nat.succ_ne_zero j

private lemma add_K_ne_of_mem_U (w : ℂ) (hw : w ∈ U) (j : ℕ) :
    w + ((j + 1 : ℕ) : ℂ) ≠ 0 := by
  intro hcon
  have hw' := (U_mem_iff w).mp hw
  set n : ℤ := -((j + 1 : ℕ) : ℤ) with hn
  have hcast : (n : ℂ) = -((j + 1 : ℕ) : ℂ) := by
    simp only [hn, Int.cast_neg, Int.cast_natCast]
  have hw_eq : w = (n : ℂ) := by
    rw [hcast]
    linear_combination hcon
  exact hw' n hw_eq

private lemma digTerm_eq (j : ℕ) (w : ℂ)
    (hK : ((j + 1 : ℕ) : ℂ) ≠ 0)
    (hWK : w + ((j + 1 : ℕ) : ℂ) ≠ 0) :
    digTerm j w = w / (((j + 1 : ℕ) : ℂ) * (w + ((j + 1 : ℕ) : ℂ))) := by
  simp only [digTerm]
  field_simp
  ring

private lemma analyticAt_digTerm_of_ne (w0 : ℂ) (j : ℕ)
    (h : w0 + ((j + 1 : ℕ) : ℂ) ≠ 0) :
    AnalyticAt ℂ (fun w => digTerm j w) w0 := by
  simp only [digTerm]
  fun_prop

private lemma add_K_ne_of_mem_ball (R : ℝ) (J : ℕ) (hJ : 2 * R ≤ (J : ℝ))
    (w : ℂ) (hw : w ∈ Metric.ball (0 : ℂ) R) (i : ℕ) :
    w + ((i + J + 1 : ℕ) : ℂ) ≠ 0 := by
  intro hcon
  have h1 : (J : ℝ) ≤ ((i + J + 1 : ℕ) : ℝ) := by
    apply Nat.cast_le.mpr
    omega
  have hK : 2 * R ≤ ((i + J + 1 : ℕ) : ℝ) := by linarith
  have hnormK : ‖(((i + J + 1 : ℕ)) : ℂ)‖ = ((i + J + 1 : ℕ) : ℝ) :=
    Complex.norm_natCast _
  have hw_norm : ‖w‖ < R := by
    simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hw
  have heq : (((i + J + 1 : ℕ)) : ℂ) = -w := by linear_combination hcon
  have hKeq : ((i + J + 1 : ℕ) : ℝ) = ‖w‖ := by
    rw [← hnormK, heq, norm_neg]
  have hnn : 0 ≤ ‖w‖ := norm_nonneg _
  linarith

private lemma norm_digTerm_tail_le (R : ℝ) (hR : 0 < R) (J : ℕ)
    (hJ : 2 * R ≤ (J : ℝ)) (w : ℂ) (hw : w ∈ Metric.ball (0 : ℂ) R)
    (i : ℕ) :
    ‖digTerm (i + J) w‖ ≤ 2 * R / ((((i + J + 1 : ℕ)) : ℝ)) ^ 2 := by
  set Kℕ : ℕ := i + J + 1 with hKℕ
  set Kℂ : ℂ := ((Kℕ : ℕ) : ℂ) with hKℂ
  set Kℝ : ℝ := ((Kℕ : ℕ) : ℝ) with hKℝ
  have hK_eq : ((i + J + 1 : ℕ) : ℂ) = Kℂ := rfl
  have hJ_eq : i + J + 1 = Kℕ := rfl
  have hK_ne : Kℂ ≠ 0 := by
    rw [hKℂ]
    exact_mod_cast Nat.succ_ne_zero (i + J)
  have hWK_ne : w + Kℂ ≠ 0 := by
    have h := add_K_ne_of_mem_ball R J hJ w hw i
    simpa [hKℂ, hKℕ] using h
  have heq : digTerm (i + J) w = w / (Kℂ * (w + Kℂ)) := by
    have h0 := digTerm_eq (i + J) w hK_ne hWK_ne
    simpa [Kℂ, Kℕ] using h0
  have hw_norm : ‖w‖ < R := by
    simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hw
  have h1 : (J : ℝ) ≤ Kℝ := by
    simp only [hKℝ, hKℕ]
    apply Nat.cast_le.mpr
    omega
  have hK_ge : 2 * R ≤ Kℝ := by linarith
  have hK_pos : 0 < Kℝ := by linarith
  have hnormK : ‖Kℂ‖ = Kℝ := by
    simp only [hKℂ, hKℝ, Complex.norm_natCast]
  have htri0 := norm_add_le (w + Kℂ) (-w)
  have heqK : (w + Kℂ) + -w = Kℂ := by abel
  rw [heqK, hnormK, norm_neg] at htri0
  have hlow : Kℝ / 2 ≤ ‖w + Kℂ‖ := by linarith
  have hpos2 : 0 < ‖w + Kℂ‖ := by linarith
  have hden_le : Kℝ * (Kℝ / 2) ≤ Kℝ * ‖w + Kℂ‖ := by
    apply mul_le_mul_of_nonneg_left hlow (le_of_lt hK_pos)
  have hnum_le : ‖w‖ ≤ R := le_of_lt hw_norm
  have heq2 : (2 * R / Kℝ ^ 2 : ℝ) = R / (Kℝ * (Kℝ / 2)) := by
    field_simp
  rw [heq, norm_div, norm_mul, hnormK]
  rw [heq2]
  gcongr

private lemma summable_tail_majorant (R : ℝ) (J : ℕ) :
    Summable (fun i : ℕ => 2 * R / ((((i + J + 1 : ℕ)) : ℝ)) ^ 2) := by
  have hbase : Summable (fun n : ℕ => 2 * R / ((n : ℝ)) ^ 2) := by
    have h0 : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ)) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
    have h1 := h0.mul_left (2 * R)
    simpa only [div_eq_mul_inv, one_mul] using h1
  have hshift := (summable_nat_add_iff (J + 1)).mpr hbase
  have hnat : ∀ i : ℕ, i + (J + 1) = i + J + 1 := fun i => by omega
  simpa [hnat] using hshift

private lemma summable_digTerm (w : ℂ) :
    Summable (fun j : ℕ => digTerm j w) := by
  set R : ℝ := ‖w‖ + 1 with hR
  have hR_pos : 0 < R := by
    have hnn : 0 ≤ ‖w‖ := norm_nonneg _
    linarith
  have hw_ball : w ∈ Metric.ball (0 : ℂ) R := by
    simp only [Metric.mem_ball, dist_eq_norm, sub_zero, hR]
    linarith [norm_nonneg (a := w)]
  obtain ⟨J, hJ⟩ := exists_nat_ge (2 * R)
  have hbound : ∀ i : ℕ,
      ‖digTerm (i + J) w‖ ≤ 2 * R / ((((i + J + 1 : ℕ)) : ℝ)) ^ 2 :=
    fun i => norm_digTerm_tail_le R hR_pos J hJ w hw_ball i
  have hmaj := summable_tail_majorant R J
  have htail : Summable (fun i : ℕ => digTerm (i + J) w) :=
    Summable.of_norm_bounded hmaj hbound
  exact (summable_nat_add_iff J).mp htail

private lemma analyticAt_head (w0 : ℂ) (hw0 : w0 ∈ U) (J : ℕ) :
    AnalyticAt ℂ (fun w => ∑ j ∈ Finset.range J, digTerm j w) w0 := by
  induction J with
  | zero =>
    simp only [Finset.sum_range_zero]
    exact analyticAt_const
  | succ J ih =>
    have h_single : AnalyticAt ℂ (fun w => digTerm J w) w0 :=
      analyticAt_digTerm_of_ne w0 J (add_K_ne_of_mem_U w0 hw0 J)
    have h_sum := ih.add h_single
    have heq : (fun w => ∑ j ∈ Finset.range (J + 1), digTerm j w)
        = (fun w => (∑ j ∈ Finset.range J, digTerm j w) + digTerm J w) := by
      funext w
      rw [Finset.sum_range_succ]
    rw [heq]
    exact h_sum

private lemma tail_differentiableOn (R : ℝ) (hR : 0 < R) (J : ℕ)
    (hJ : 2 * R ≤ (J : ℝ)) :
    DifferentiableOn ℂ (fun w => ∑' i : ℕ, digTerm (i + J) w)
      (Metric.ball (0 : ℂ) R) := by
  apply Complex.differentiableOn_tsum_of_summable_norm
    (u := fun i : ℕ => 2 * R / ((((i + J + 1 : ℕ)) : ℝ)) ^ 2)
    (summable_tail_majorant R J) _ Metric.isOpen_ball _
  · intro i w hw
    have hne : w + ((i + J + 1 : ℕ) : ℂ) ≠ 0 :=
      add_K_ne_of_mem_ball R J hJ w hw i
    have hA : AnalyticAt ℂ (fun w => digTerm (i + J) w) w :=
      analyticAt_digTerm_of_ne w (i + J) hne
    exact hA.differentiableAt.differentiableWithinAt
  · intro i w hw
    exact norm_digTerm_tail_le R hR J hJ w hw i

private lemma digF_analytic : AnalyticOnNhd ℂ digF U := by
  intro w hw
  have hw1 : ∀ m : ℕ, w + 1 ≠ -((m : ℕ) : ℂ) := by
    intro m hcon
    have hw' := (U_mem_iff w).mp hw
    set n : ℤ := -1 - ((m : ℕ) : ℤ) with hn
    have hcast : (n : ℂ) = -1 - ((m : ℕ) : ℂ) := by
      simp only [hn, Int.cast_sub, Int.cast_neg, Int.cast_one,
        Int.cast_natCast]
    have hw_eq : w = (n : ℂ) := by
      rw [hcast]
      linear_combination hcon
    exact hw' n hw_eq
  have hG : AnalyticAt ℂ Complex.digamma (w + 1) :=
    Complex.analyticAt_digamma _ hw1
  have hshift : AnalyticAt ℂ (fun w : ℂ => w + 1) w := by
    fun_prop
  have hcomp : AnalyticAt ℂ (Complex.digamma ∘ (fun w : ℂ => w + 1)) w :=
    AnalyticAt.comp (f := (fun w : ℂ => w + 1)) (x := w) hG hshift
  have hadd : AnalyticAt ℂ ((Complex.digamma ∘ (fun w : ℂ => w + 1))
      + fun _ : ℂ => (Real.eulerMascheroniConstant : ℂ)) w :=
    hcomp.add analyticAt_const
  apply hadd.congr
  apply Filter.Eventually.of_forall
  intro v
  simp only [digF, Function.comp_apply, Pi.add_apply]

private lemma digG_analytic : AnalyticOnNhd ℂ digG U := by
  intro w0 hw0
  set R : ℝ := ‖w0‖ + 1 with hR
  have hR_pos : 0 < R := by
    have hnn : 0 ≤ ‖w0‖ := norm_nonneg _
    linarith
  have hw0_ball : w0 ∈ Metric.ball (0 : ℂ) R := by
    simp only [Metric.mem_ball, dist_eq_norm, sub_zero, hR]
    linarith [norm_nonneg (a := w0)]
  obtain ⟨J, hJ⟩ := exists_nat_ge (2 * R)
  have hHead : AnalyticAt ℂ
      (fun w => ∑ j ∈ Finset.range J, digTerm j w) w0 :=
    analyticAt_head w0 hw0 J
  have hTailDiff : DifferentiableOn ℂ
      (fun w => ∑' i : ℕ, digTerm (i + J) w) (Metric.ball (0 : ℂ) R) :=
    tail_differentiableOn R hR_pos J hJ
  have hTail : AnalyticAt ℂ (fun w => ∑' i : ℕ, digTerm (i + J) w) w0 :=
    hTailDiff.analyticAt (Metric.isOpen_ball.mem_nhds hw0_ball)
  have hSum : AnalyticAt ℂ (fun w => (∑ j ∈ Finset.range J, digTerm j w)
      + (∑' i : ℕ, digTerm (i + J) w)) w0 :=
    hHead.add hTail
  apply hSum.congr
  have h1 := Metric.isOpen_ball.mem_nhds hw0_ball
  have h2 := U_isOpen.mem_nhds hw0
  have hmem : Metric.ball (0 : ℂ) R ∩ U ∈ 𝓝 w0 :=
    Filter.inter_mem h1 h2
  apply Filter.eventuallyEq_of_mem hmem
  intro w hw
  have hwU : w ∈ U := hw.2
  have hsum := summable_digTerm w
  have hsplit := Summable.sum_add_tsum_nat_add J hsum
  simp only [digG]
  exact hsplit

private lemma cast_digTerm (t : ℝ) (j : ℕ) :
    (((1 / ((j : ℝ) + 1) - 1 / (t + (j : ℝ) + 1) : ℝ)) : ℂ)
      = digTerm j (t : ℂ) := by
  have h1 : ((((j : ℝ) + 1 : ℝ)) : ℂ) = ((j + 1 : ℕ) : ℂ) := by
    push_cast
    ring
  have h2 : ((((t + (j : ℝ) + 1 : ℝ))) : ℂ)
      = (t : ℂ) + ((j + 1 : ℕ) : ℂ) := by
    push_cast
    ring
  simp only [digTerm, Complex.ofReal_sub, Complex.ofReal_div,
    Complex.ofReal_one, h1, h2]

private lemma agree_ofReal (t : ℝ) (ht : 0 < t) :
    digF (t : ℂ) = digG (t : ℂ) := by
  have hReal := Real.hasSum_digamma_series t ht
  have hComplex : HasSum
      (fun j : ℕ => (((1 / ((j : ℝ) + 1)
        - 1 / (t + (j : ℝ) + 1) : ℝ)) : ℂ))
      ((((deriv (fun s => Real.log (Real.Gamma s)) (t + 1)
        + Real.eulerMascheroniConstant : ℝ)) : ℂ)) :=
    (Complex.hasSum_ofReal).mpr hReal
  have hTerms : ∀ j : ℕ,
      ((((1 / ((j : ℝ) + 1) - 1 / (t + (j : ℝ) + 1) : ℝ)) : ℂ))
        = digTerm j (t : ℂ) :=
    fun j => cast_digTerm t j
  have hLim : ((((deriv (fun s => Real.log (Real.Gamma s)) (t + 1)
      + Real.eulerMascheroniConstant : ℝ)) : ℂ)) = digF (t : ℂ) := by
    have hlog := Real.deriv_log_Gamma (t + 1) (by linarith)
    have hdig := Complex.deriv_Gamma_ofReal (t + 1) (by linarith)
    have e1 : (t : ℂ) + 1 = ((t + 1 : ℝ) : ℂ) := by push_cast; ring
    simp only [digF, Complex.digamma_def, logDeriv_apply,
      Complex.ofReal_add, Complex.ofReal_div, e1, ← hdig,
      ← Complex.Gamma_ofReal, hlog]
  have hfun_eq : (fun j : ℕ => (((1 / ((j : ℝ) + 1)
      - 1 / (t + (j : ℝ) + 1) : ℝ)) : ℂ))
      = (fun j : ℕ => digTerm j (t : ℂ)) :=
    funext hTerms
  rw [hfun_eq, hLim] at hComplex
  have htsum := hComplex.tsum_eq
  simp only [digG]
  exact htsum.symm

private lemma half_mem_U : ((1 / 2 : ℝ) : ℂ) ∈ U := by
  rw [U_mem_iff]
  intro n hcon
  have h := congrArg Complex.re hcon
  simp only [Complex.ofReal_re, Complex.intCast_re] at h
  have h2 : 2 * n = 1 := by
    have h3 : ((2 * n : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h3
  omega

private lemma digFreq :
    ∃ᶠ z in 𝓝[≠] ((1 / 2 : ℝ) : ℂ), digF z = digG z := by
  set t : ℕ → ℝ := fun m => 1 / 2 + 1 / ((m : ℝ) + 3) with ht
  set f : ℕ → ℂ := fun m => ((t m : ℝ) : ℂ) with hf
  have hpos : ∀ m : ℕ, 0 < t m := by
    intro m
    have h1 : (0 : ℝ) < 1 / ((m : ℝ) + 3) := by
      apply one_div_pos.mpr
      have hnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
      linarith
    simp only [ht]
    linarith
  have hag : ∀ m : ℕ, digF (f m) = digG (f m) := fun m =>
    agree_ofReal (t m) (hpos m)
  have hfreq_top : ∃ᶠ m in Filter.atTop, digF (f m) = digG (f m) :=
    (Filter.Eventually.of_forall hag).frequently
  have h0 : Filter.Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ))
      Filter.atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 : Filter.Tendsto (fun m : ℕ => (1 / ((m : ℝ) + 3) : ℝ))
      Filter.atTop (𝓝 (0 : ℝ)) := by
    have hshift := (tendsto_add_atTop_iff_nat 2).mpr h0
    have hcongr : (fun m : ℕ => 1 / ((((m + 2 : ℕ)) : ℝ) + 1))
        = (fun m : ℕ => 1 / ((m : ℝ) + 3)) := by
      funext m
      congr 1
      push_cast
      ring
    rwa [hcongr] at hshift
  have h2 : Filter.Tendsto t Filter.atTop (𝓝 (1 / 2 : ℝ)) := by
    have h := tendsto_const_nhds (x := (1 / 2 : ℝ)) |>.add h1
    simpa [ht, add_zero] using h
  have h3 : Filter.Tendsto f Filter.atTop
      (𝓝 (((1 / 2 : ℝ)) : ℂ)) := by
    have hc := Complex.continuous_ofReal.tendsto (1 / 2 : ℝ)
    have hcomp := hc.comp h2
    simpa [hf, ht, Function.comp_def] using hcomp
  have hne : ∀ m : ℕ, f m ≠ ((1 / 2 : ℝ) : ℂ) := by
    intro m hm
    have ht_ne : t m ≠ 1 / 2 := by
      have h1pos : (0 : ℝ) < 1 / ((m : ℝ) + 3) := by
        apply one_div_pos.mpr
        have hnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
        linarith
      simp only [ht]
      linarith
    have hinj := Complex.ofReal_injective.ne ht_ne
    exact hinj (by simpa [hf] using hm)
  have h3' : Filter.Tendsto f Filter.atTop
      (𝓝[≠] (((1 / 2 : ℝ)) : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨h3, Filter.Eventually.of_forall hne⟩
  exact h3'.frequently hfreq_top

private lemma digEqOn : Set.EqOn digF digG U :=
  AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
    digF_analytic digG_analytic U_preconnected half_mem_U digFreq

private lemma digHasSum (w : ℂ) (hw : w ∈ U) :
    HasSum (fun j : ℕ => digTerm j w) (digF w) := by
  have heq : digF w = digG w := digEqOn hw
  have hG : digG w = ∑' j : ℕ, digTerm j w := rfl
  have htsum : (∑' j : ℕ, digTerm j w) = digF w := by
    rw [← hG, ← heq]
  have hHas := (summable_digTerm w).hasSum
  rwa [htsum] at hHas

private lemma neg_mem_U (w : ℂ) (hw : w ∈ U) : -w ∈ U := by
  rw [U_mem_iff] at hw ⊢
  intro n hcon
  have hw' := hw (-n)
  have hcast : (((-n : ℤ)) : ℂ) = -((n : ℤ) : ℂ) :=
    Int.cast_neg n
  have hw_eq : w = (((-n : ℤ)) : ℂ) := by
    rw [hcast]
    linear_combination -hcon
  exact hw' hw_eq

private lemma U_avoids_neg_nat (w : ℂ) (hw : w ∈ U) (m : ℕ) :
    w ≠ -((m : ℕ) : ℂ) := by
  intro hcon
  have hw' := (U_mem_iff w).mp hw
  set n : ℤ := -((m : ℕ) : ℤ) with hn
  have hcast : (n : ℂ) = -((m : ℕ) : ℂ) := by
    simp only [hn, Int.cast_neg, Int.cast_natCast]
  have hw_eq : w = (n : ℂ) := by
    rw [hcast]
    exact hcon
  exact hw' n hw_eq

private lemma z_mem_U (x : ℂ) (hx0 : x ≠ 0)
    (hpoles : ∀ k : ℕ,
      x ≠ 1 / ((k + 1 : ℕ) : ℂ) ∧
        x ≠ -(1 / ((k + 1 : ℕ) : ℂ))) :
    (1 / x : ℂ) ∈ U := by
  rw [U_mem_iff]
  intro n hcon
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · have hcast : ((((m : ℕ) : ℤ)) : ℂ) = ((m : ℕ) : ℂ) := by
      simp only [Int.cast_natCast]
    rw [hcast] at hcon
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simp only [Nat.cast_zero] at hcon
      exact (div_ne_zero one_ne_zero hx0) hcon
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 :=
        ⟨m - 1, (Nat.sub_add_cancel hpos).symm⟩
      have h1 := (hpoles k).1
      apply h1
      have hxinv : x⁻¹ = ((k + 1 : ℕ) : ℂ) := by
        simpa [one_div] using hcon
      have hinv : x⁻¹⁻¹ = (((k + 1 : ℕ) : ℂ))⁻¹ := by rw [hxinv]
      rw [inv_inv] at hinv
      rw [hinv, ← one_div]
  · have hcast : (((-(m : ℤ) : ℤ)) : ℂ) = -((m : ℕ) : ℂ) := by
      simp only [Int.cast_neg, Int.cast_natCast]
    rw [hcast] at hcon
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simp only [Nat.cast_zero, neg_zero] at hcon
      exact (div_ne_zero one_ne_zero hx0) hcon
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 :=
        ⟨m - 1, (Nat.sub_add_cancel hpos).symm⟩
      have h2 := (hpoles k).2
      apply h2
      have hxinv : x⁻¹ = -((k + 1 : ℕ) : ℂ) := by
        simpa [one_div] using hcon
      have hinv : x⁻¹⁻¹ = (-((k + 1 : ℕ) : ℂ))⁻¹ := by rw [hxinv]
      rw [inv_inv] at hinv
      rw [hinv, inv_neg, ← one_div]

private lemma phi_identity (K x : ℂ) (hx0 : x ≠ 0) (hK : K ≠ 0)
    (h_add1 : 1 + K * x ≠ 0) (h_sub1 : -1 + K * x ≠ 0)
    (hK2 : K ^ 2 * x ^ 2 - 1 ≠ 0) :
    (1 / K - 1 / (1 / x + K) + (1 / K - 1 / (-(1 / x) + K)))
      = -x * (2 / ((K * x) ^ 3 - K * x)) := by
  field_simp
  ring

private lemma digTerm_add_eq_phi (x : ℂ) (hx0 : x ≠ 0)
    (hpoles : ∀ k : ℕ,
      x ≠ 1 / ((k + 1 : ℕ) : ℂ) ∧
        x ≠ -(1 / ((k + 1 : ℕ) : ℂ))) (j : ℕ) :
    digTerm j (1 / x) + digTerm j (-(1 / x))
      = -x * chapter8PhiTerm x j := by
  have hK : ((j + 1 : ℕ) : ℂ) ≠ 0 := K_ne j
  have hKx1 : ((j + 1 : ℕ) : ℂ) * x ≠ 1 := by
    intro h
    apply (hpoles j).1
    field_simp at h ⊢
    linear_combination h
  have hKxm1 : ((j + 1 : ℕ) : ℂ) * x ≠ -1 := by
    intro h
    apply (hpoles j).2
    field_simp at h ⊢
    linear_combination h
  have hsub : ((((j + 1 : ℕ) : ℂ) * x) - 1) ≠ 0 := by
    intro h
    apply hKx1
    linear_combination h
  have hadd : ((((j + 1 : ℕ) : ℂ) * x) + 1) ≠ 0 := by
    intro h
    apply hKxm1
    linear_combination h
  have h_add1 : (1 + ((j + 1 : ℕ) : ℂ) * x) ≠ 0 := by
    have h := hadd
    rwa [add_comm] at h
  have h_sub1 : (-1 + ((j + 1 : ℕ) : ℂ) * x) ≠ 0 := by
    have heq : (-1 + ((j + 1 : ℕ) : ℂ) * x)
        = ((((j + 1 : ℕ) : ℂ) * x) - 1) := by ring
    rwa [heq]
  have hK2 : (((j + 1 : ℕ) : ℂ) ^ 2 * x ^ 2 - 1) ≠ 0 := by
    have hfac : (((j + 1 : ℕ) : ℂ) ^ 2 * x ^ 2 - 1)
        = ((((j + 1 : ℕ) : ℂ) * x) - 1)
          * ((((j + 1 : ℕ) : ℂ) * x) + 1) := by ring
    rw [hfac]
    exact mul_ne_zero hsub hadd
  have hgen := phi_identity ((j + 1 : ℕ) : ℂ) x hx0 hK
    h_add1 h_sub1 hK2
  simp only [digTerm, chapter8PhiTerm]
  exact hgen

/-- Canonical `Complex.digamma` form of Entry 11's functional equation. -/
theorem ramanujan_part1_ch8_entry11_qgammafunctional_digamma
    (x : ℂ) (hx0 : x ≠ 0)
    (hpoles : ∀ k : ℕ,
      x ≠ 1 / ((k + 1 : ℕ) : ℂ) ∧
        x ≠ -(1 / ((k + 1 : ℕ) : ℂ))) :
    Summable (chapter8PhiTerm x) ∧
      Complex.Gamma (1 / x) ≠ 0 ∧
      Complex.Gamma (1 - 1 / x) ≠ 0 ∧
      Complex.digamma (1 / x) + Complex.digamma (1 - 1 / x) =
        -2 * (Real.eulerMascheroniConstant : ℂ) - x * chapter8Phi x := by
  refine ⟨chapter8PhiSummable x hx0 hpoles, ?_, ?_, ?_⟩
  · exact Complex.Gamma_ne_zero (fun m => chapter8GammaOneDivAvoid x hx0 hpoles m)
  · exact Complex.Gamma_ne_zero (fun m => chapter8GammaOneSubAvoid x hpoles m)
  · have hzU : (1 / x : ℂ) ∈ U := z_mem_U x hx0 hpoles
    have hnzU : (-(1 / x) : ℂ) ∈ U := neg_mem_U _ hzU
    have h1 := digHasSum (1 / x) hzU
    have h2 := digHasSum (-(1 / x)) hnzU
    have hcomb := h1.add h2
    have hterm_eq : ∀ j : ℕ, digTerm j (1 / x) + digTerm j (-(1 / x))
        = -x * chapter8PhiTerm x j :=
      fun j => digTerm_add_eq_phi x hx0 hpoles j
    have hfun_eq : (fun j : ℕ => digTerm j (1 / x) + digTerm j (-(1 / x)))
        = (fun j : ℕ => -x * chapter8PhiTerm x j) :=
      funext hterm_eq
    rw [hfun_eq] at hcomb
    have hPhiSum := chapter8PhiSummable x hx0 hpoles
    have hPhiHas := hPhiSum.hasSum
    have hMul := hPhiHas.mul_left (-x)
    have hEq : digF (1 / x) + digF (-(1 / x))
        = -x * ∑' j : ℕ, chapter8PhiTerm x j :=
      hcomb.unique hMul
    have hz_avoid : ∀ m : ℕ, (1 / x : ℂ) ≠ -((m : ℕ) : ℂ) :=
      fun m => U_avoids_neg_nat _ hzU m
    have hRec := Complex.digamma_apply_add_one (1 / x) hz_avoid
    have hz_inv : ((1 / x : ℂ))⁻¹ = x := by
      simp only [one_div, inv_inv]
    have hneg_eq : ((-(1 / x) : ℂ) + 1) = (1 - 1 / x : ℂ) := by ring
    have hPhi_def : chapter8Phi x
        = 1 + ∑' j : ℕ, chapter8PhiTerm x j := rfl
    rw [hPhi_def]
    have hEq2 : Complex.digamma ((1 / x : ℂ) + 1)
        + Complex.digamma ((-(1 / x) : ℂ) + 1)
        + 2 * (Real.eulerMascheroniConstant : ℂ)
        = -x * ∑' j : ℕ, chapter8PhiTerm x j := by
      simp only [digF] at hEq
      linear_combination hEq
    rw [hRec, hneg_eq, hz_inv] at hEq2
    linear_combination hEq2

/-- Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 8.

Proves `Wanted` entry `ramanujan_part1_ch8_entry11_qgammafunctional`.
-/
theorem ramanujan_part1_ch8_entry11_qgammafunctional
    (x : ℂ) (hx0 : x ≠ 0)
    (hpoles : ∀ k : ℕ,
      x ≠ 1 / ((k + 1 : ℕ) : ℂ) ∧
        x ≠ -(1 / ((k + 1 : ℕ) : ℂ))) :
    Summable (chapter8PhiTerm x) ∧
      Complex.Gamma (1 / x) ≠ 0 ∧
      Complex.Gamma (1 - 1 / x) ≠ 0 ∧
      chapter8Digamma (1 / x) + chapter8Digamma (1 - 1 / x) =
        -2 * (Real.eulerMascheroniConstant : ℂ) - x * chapter8Phi x := by
  obtain ⟨hsum, hG1, hG2, heq⟩ :=
    ramanujan_part1_ch8_entry11_qgammafunctional_digamma x hx0 hpoles
  refine ⟨hsum, hG1, hG2, ?_⟩
  rw [chapter8Digamma_eq_digamma, chapter8Digamma_eq_digamma]
  exact heq

end
end Entry11Qgammafunctional
end MathlibExt.Analysis.Ramanujan.Part1Ch8
end
