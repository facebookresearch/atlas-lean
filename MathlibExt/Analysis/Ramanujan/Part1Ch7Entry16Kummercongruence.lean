/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Mathlib.NumberTheory.LSeries.ZMod
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
public import MathlibExt.Analysis.Ramanujan.Part1Ch7Phi
public import MathlibExt.Analysis.Ramanujan.Part1Ch7DirichletBeta
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.LSeries.AbelContinuation

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 7

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry16Kummercongruence

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter7Entry16Left (r : ℂ) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) : ℂ :=
  (chapter7Phi r ⟨x - 1, by constructor <;> linarith⟩ +
      chapter7Phi r ⟨-x, by constructor <;> linarith⟩ - 2 * riemannZeta (-r)) /
    (4 * Complex.Gamma (r + 1))

def chapter7Entry16Term (r : ℂ) (x : ℝ) (k : ℕ) : ℂ :=
  (Real.cos (2 * Real.pi * k * x) : ℂ) /
    Complex.cpow (((2 * Real.pi * k : ℝ) : ℂ)) (r + 1)

def chapter7Entry16PartialSum (r : ℂ) (x : ℝ) (N : ℕ) : ℂ :=
  ∑ k ∈ Icc 1 N, chapter7Entry16Term r x k

/-- Cosine-series coefficients with vanishing zeroth term, for Abel summation. -/
private noncomputable def entry16Coeff (x : ℝ) (k : ℕ) : ℂ :=
  if k = 0 then 0 else ((Real.cos (2 * Real.pi * (k : ℝ) * x) : ℝ) : ℂ)

private theorem entry16Coeff_zero (x : ℝ) : entry16Coeff x 0 = 0 := by
  simp [entry16Coeff]

private theorem entry16Coeff_of_ne {x : ℝ} {k : ℕ} (hk : k ≠ 0) :
    entry16Coeff x k = ((Real.cos (2 * Real.pi * (k : ℝ) * x) : ℝ) : ℂ) := by
  simp [entry16Coeff, hk]

/-- The class of `x ∈ (0, 1)` is nonzero in `UnitAddCircle`. -/
private theorem entry16CircleNe {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ((x : ℝ) : UnitAddCircle) ≠ 0 := by
  intro h
  have h2 := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h
  obtain ⟨n, hn⟩ := h2
  have hnx : (n : ℝ) = x := by simpa using hn
  have hn0 : n = 0 ∨ 1 ≤ n ∨ n ≤ -1 := by omega
  rcases hn0 with rfl | h | h
  · simp at hnx
    linarith
  · have hle : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    linarith
  · have hle : (n : ℝ) ≤ -1 := by exact_mod_cast h
    linarith

/-- Product-to-sum identity driving the telescoping bound. -/
private theorem entry16Trig (x : ℝ) (k : ℕ) :
    2 * Real.sin (Real.pi * x) * Real.cos (2 * Real.pi * (k : ℝ) * x)
      = Real.sin ((2 * (k : ℝ) + 1) * Real.pi * x) -
        Real.sin ((2 * (k : ℝ) - 1) * Real.pi * x) := by
  have h := Real.two_mul_sin_mul_cos (Real.pi * x) (2 * Real.pi * (k : ℝ) * x)
  rw [h]
  have e1 : Real.pi * x - 2 * Real.pi * (k : ℝ) * x
      = -((2 * (k : ℝ) - 1) * Real.pi * x) := by ring
  have e2 : Real.pi * x + 2 * Real.pi * (k : ℝ) * x
      = (2 * (k : ℝ) + 1) * Real.pi * x := by ring
  rw [e1, e2, Real.sin_neg]
  ring

/-- The cosine partial sums telescope. -/
private theorem entry16Tele (x : ℝ) (N : ℕ) :
    2 * Real.sin (Real.pi * x) *
        (∑ k ∈ Finset.Icc 1 N, Real.cos (2 * Real.pi * (k : ℝ) * x))
      = Real.sin ((2 * (N : ℝ) + 1) * Real.pi * x) - Real.sin (Real.pi * x) := by
  induction N with
  | zero =>
    rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) from by decide]
    simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    rw [mul_add, ih, entry16Trig x (n + 1)]
    push_cast
    have e3 : (2 * ((n : ℝ) + 1) - 1) * Real.pi * x
        = (2 * (n : ℝ) + 1) * Real.pi * x := by ring
    rw [e3]
    ring

/-- Uniform bound on the coefficient partial sums. -/
private theorem entry16SumBound {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (N : ℕ) :
    ‖∑ k ∈ Finset.Icc 0 N, entry16Coeff x k‖ ≤ 1 / Real.sin (Real.pi * x) := by
  have hsin : 0 < Real.sin (Real.pi * x) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hx0) (by
      have h := mul_lt_mul_of_pos_left hx1 Real.pi_pos
      rwa [mul_one] at h)
  have hA : ∑ k ∈ Finset.Icc 0 N, entry16Coeff x k
      = ((∑ k ∈ Finset.Icc 1 N, Real.cos (2 * Real.pi * (k : ℝ) * x) : ℝ) : ℂ) := by
    by_cases hN : N = 0
    · subst hN
      rw [show Finset.Icc 0 0 = ({0} : Finset ℕ) from by decide]
      rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) from by decide]
      simp [entry16Coeff_zero]
    · have hsplit : Finset.Icc 0 N = insert 0 (Finset.Icc 1 N) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hsplit, Finset.sum_insert (by simp), entry16Coeff_zero, zero_add,
        Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hk0 : k ≠ 0 := by
        have := Finset.mem_Icc.mp hk
        omega
      exact entry16Coeff_of_ne (x := x) hk0
  have hT := entry16Tele x N
  have hDlo : -2 ≤ Real.sin ((2 * (N : ℝ) + 1) * Real.pi * x) - Real.sin (Real.pi * x) := by
    have h1 := Real.neg_one_le_sin ((2 * (N : ℝ) + 1) * Real.pi * x)
    have h2 := Real.sin_le_one (Real.pi * x)
    linarith
  have hDhi : Real.sin ((2 * (N : ℝ) + 1) * Real.pi * x) - Real.sin (Real.pi * x) ≤ 2 := by
    have h1 := Real.sin_le_one ((2 * (N : ℝ) + 1) * Real.pi * x)
    have h2 := Real.neg_one_le_sin (Real.pi * x)
    linarith
  set S := ∑ k ∈ Finset.Icc 1 N, Real.cos (2 * Real.pi * (k : ℝ) * x) with hS
  have hSeq : S = (Real.sin ((2 * (N : ℝ) + 1) * Real.pi * x) - Real.sin (Real.pi * x)) /
      (2 * Real.sin (Real.pi * x)) := by
    rw [eq_div_iff (by positivity : (2 : ℝ) * Real.sin (Real.pi * x) ≠ 0)]
    linarith [hT]
  have hAbs2 : |S| * (2 * Real.sin (Real.pi * x)) ≤ 2 := by
    have hmem : |S * (2 * Real.sin (Real.pi * x))| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hT]
    rwa [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.sin (Real.pi * x))] at hmem
  have hS1 : |S| * Real.sin (Real.pi * x) ≤ 1 := by
    have e : |S| * (2 * Real.sin (Real.pi * x)) = 2 * (|S| * Real.sin (Real.pi * x)) := by
      ring
    linarith [hAbs2]
  have hfin : |S| ≤ 1 / Real.sin (Real.pi * x) := by
    rw [le_div_iff₀ hsin]
    exact hS1
  rw [hA]
  rwa [Complex.norm_real, Real.norm_eq_abs]

/-- The one-based partial sums are `O(n^0)` via the uniform cosine bound. -/
private theorem entry16IsBigO {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (fun n => abelPartialSum (entry16Coeff x) n) =O[Filter.atTop]
      fun n => (((n : ℝ) ^ (0 : ℝ) : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound (1 / Real.sin (Real.pi * x))
  filter_upwards with n
  have hEq : abelPartialSum (entry16Coeff x) n
      = ∑ k ∈ Finset.Icc 0 n, entry16Coeff x k := by
    unfold abelPartialSum
    by_cases hN : n = 0
    · subst hN
      rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) from by decide,
        show Finset.Icc 0 0 = ({0} : Finset ℕ) from by decide]
      simp [entry16Coeff_zero]
    · have hsplit : Finset.Icc 0 n = insert 0 (Finset.Icc 1 n) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hsplit, Finset.sum_insert (by simp), entry16Coeff_zero, zero_add]
  rw [hEq]
  have hB := entry16SumBound hx0 hx1 n
  have hrw : (((n : ℝ) ^ (0 : ℝ) : ℝ)) = 1 := Real.rpow_zero _
  rw [hrw, norm_one, mul_one]
  exact hB

/-- The Abel continuation is analytic where `Re s > 0`. -/
private theorem entry16AnalyticNhd {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    AnalyticOnNhd ℂ (abelContinuation (entry16Coeff x)) {s : ℂ | 0 < s.re} := by
  have hO := entry16IsBigO hx0 hx1
  have hAn := analyticOn_abelContinuation (entry16Coeff x) hO
  intro s hs
  exact AnalyticOn.analyticAt ((Complex.isOpen_re_gt 0).mem_nhds hs) hAn

/-- The Abel continuation agrees with `cosZeta` where `Re s > 1`. -/
private theorem entry16Agree {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) {s : ℂ} (hs : 1 < s.re) :
    abelContinuation (entry16Coeff x) s
      = HurwitzZeta.cosZeta ((x : ℝ) : UnitAddCircle) s := by
  have hs0 : (0 : ℝ) < s.re := by linarith
  have hsne : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hO := entry16IsBigO hx0 hx1
  have hBdd : ∀ n ≠ 0, ‖entry16Coeff x n‖ ≤ (1 : ℝ) := by
    intro n hn
    rw [entry16Coeff_of_ne hn, Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  have hSumm : LSeriesSummable (entry16Coeff x) s :=
    LSeriesSummable_of_bounded_of_one_lt_re hBdd hs
  have hAbelL : abelContinuation (entry16Coeff x) s
      = LSeries (entry16Coeff x) s :=
    abelContinuation_eq_LSeries (entry16Coeff x) le_rfl hs0 hSumm hO
  have hHasCos := HurwitzZeta.hasSum_nat_cosZeta x hs
  have hHasTerm : HasSum (LSeries.term (entry16Coeff x) s)
      (HurwitzZeta.cosZeta ((x : ℝ) : UnitAddCircle) s) := by
    apply HasSum.congr_fun hHasCos
    intro n
    by_cases hn : n = 0
    · subst hn
      simp only [LSeries.term_zero]
      have hpow : (((0 : ℕ) : ℂ)) ^ s = 0 := by simp [Complex.zero_cpow hsne]
      rw [hpow, div_zero]
    · rw [LSeries.term_of_ne_zero hn (entry16Coeff x) s,
        entry16Coeff_of_ne hn]
      have e : (2 * Real.pi * (n : ℝ) * x) = 2 * Real.pi * x * (n : ℝ) := by
        ring
      rw [e]
  have hEq : LSeries (entry16Coeff x) s
      = HurwitzZeta.cosZeta ((x : ℝ) : UnitAddCircle) s :=
    HasSum.unique hSumm.LSeriesHasSum hHasTerm
  exact hAbelL.trans hEq

/-- Key lemma: the cosine series converges to `cosZeta` for `Re s > 0`. -/
private theorem entry16KeyTendsto {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
        ((Real.cos (2 * Real.pi * (k : ℝ) * x) : ℝ) : ℂ) / (k : ℂ) ^ s)
      Filter.atTop (nhds (HurwitzZeta.cosZeta ((x : ℝ) : UnitAddCircle) s)) := by
  have hO := entry16IsBigO hx0 hx1
  have hTend := tendsto_abelContinuation_Icc (entry16Coeff x) hs hO
  have hEq : abelContinuation (entry16Coeff x) s
      = HurwitzZeta.cosZeta ((x : ℝ) : UnitAddCircle) s := by
    have hAF := entry16AnalyticNhd hx0 hx1
    have hAG : AnalyticOnNhd ℂ (HurwitzZeta.cosZeta ((x : ℝ) : UnitAddCircle))
        {s : ℂ | 0 < s.re} := by
      apply AnalyticOnNhd.mono _ (Set.subset_univ _)
      apply DifferentiableOn.analyticOnNhd _ isOpen_univ
      exact (HurwitzZeta.differentiable_cosZeta_of_ne_zero
        (entry16CircleNe hx0 hx1)).differentiableOn
    have hPre : IsPreconnected {s : ℂ | 0 < s.re} :=
      (convex_halfSpace_re_gt 0).isPreconnected
    have hz0 : (2 : ℂ) ∈ {s : ℂ | 0 < s.re} := by
      change (0 : ℝ) < ((2 : ℂ)).re
      rw [show ((2 : ℂ)).re = (2 : ℝ) from rfl]
      norm_num
    have hEqOn : Set.EqOn (abelContinuation (entry16Coeff x))
        (HurwitzZeta.cosZeta ((x : ℝ) : UnitAddCircle)) {s : ℂ | 1 < s.re} := by
      intro t ht
      have ht1 : (1 : ℝ) < t.re := ht
      exact entry16Agree hx0 hx1 ht1
    have hev := Set.EqOn.eventuallyEq_of_mem hEqOn (show {s : ℂ | 1 < s.re} ∈ nhds (2 : ℂ) by
      apply (Complex.isOpen_re_gt 1).mem_nhds
      change (1 : ℝ) < ((2 : ℂ)).re
      rw [show ((2 : ℂ)).re = (2 : ℝ) from rfl]
      norm_num)
    have hEq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hAF hAG hPre hz0 hev
    exact hEq hs
  rw [hEq] at hTend
  have hSumEq : ∀ N : ℕ,
      (∑ n ∈ Finset.Icc 1 N, LSeries.term (entry16Coeff x) s n)
        = ∑ k ∈ Finset.Icc 1 N,
          ((Real.cos (2 * Real.pi * (k : ℝ) * x) : ℝ) : ℂ) / (k : ℂ) ^ s := by
    intro N
    apply Finset.sum_congr rfl
    intro k hk
    have hk0 : k ≠ 0 := by
      have := Finset.mem_Icc.mp hk
      omega
    rw [LSeries.term_of_ne_zero hk0 (entry16Coeff x) s, entry16Coeff_of_ne hk0]
  exact Filter.Tendsto.congr (fun N => hSumEq N) hTend
private theorem entry16LeftEq (r : ℂ) (x : ℝ) (hr : -1 < r.re) (hx0 : 0 < x) (hx1 : x < 1) :
    chapter7Entry16Left r x hx0 hx1 =
      Complex.sin ((Real.pi : ℂ) * r / 2) *
        (HurwitzZeta.cosZeta ((x : ℝ) : UnitAddCircle) (r + 1) /
          (2 * (Real.pi : ℂ)) ^ (r + 1)) := by
  have hsRe : (0 : ℝ) < (r + 1).re := by
    have e : ((r + 1 : ℂ)).re = r.re + 1 := by simp
    linarith
  have hGamma : Complex.Gamma (r + 1) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hsRe
  have hNe : ((x : ℝ) : UnitAddCircle) ≠ 0 := entry16CircleNe hx0 hx1
  have c1 : ((((x - 1 : ℝ) + 1 : ℝ)) : UnitAddCircle) = ((x : ℝ) : UnitAddCircle) := by
    congr 1
    ring
  have c2 : ((((-x : ℝ) + 1 : ℝ)) : UnitAddCircle) = -((x : ℝ) : UnitAddCircle) := by
    have e : ((-x : ℝ) + 1 : ℝ) = 1 - x := by ring
    rw [e, AddCircle.coe_sub, AddCircle.coe_period, zero_sub]
  have hL : chapter7Entry16Left r x hx0 hx1 =
      ((riemannZeta (-r) - HurwitzZeta.hurwitzZeta ((x : ℝ) : UnitAddCircle) (-r)) +
        (riemannZeta (-r) - HurwitzZeta.hurwitzZeta (-((x : ℝ) : UnitAddCircle)) (-r)) -
        2 * riemannZeta (-r)) / (4 * Complex.Gamma (r + 1)) := by
    change ((riemannZeta (-r) -
        HurwitzZeta.hurwitzZeta ((((x - 1 : ℝ) + 1 : ℝ)) : UnitAddCircle) (-r)) +
      (riemannZeta (-r) -
        HurwitzZeta.hurwitzZeta ((((-x : ℝ) + 1 : ℝ)) : UnitAddCircle) (-r)) -
      2 * riemannZeta (-r)) / (4 * Complex.Gamma (r + 1)) = _
    rw [c1, c2]
  have hSide1 : ∀ n : ℕ, r + 1 ≠ -↑n := by
    intro n hn
    have hre := congrArg Complex.re hn
    have e1 : ((r + 1 : ℂ)).re = r.re + 1 := by simp
    have e2 : ((-↑n : ℂ)).re = -((n : ℝ)) := by simp
    rw [e1, e2] at hre
    have hnn : (0 : ℝ) ≤ ((n : ℝ)) := Nat.cast_nonneg n
    linarith
  have hOneSub := HurwitzZeta.hurwitzZetaEven_one_sub (a := ((x : ℝ) : UnitAddCircle))
    (s := r + 1) hSide1 (Or.inl hNe)
  have h1r : (1 : ℂ) - (r + 1) = -r := by ring
  rw [h1r] at hOneSub
  have hEven := HurwitzZeta.hurwitzZetaEven_eq ((x : ℝ) : UnitAddCircle) (-r)
  have harg : (Real.pi : ℂ) * (r + 1) / 2
      = (Real.pi : ℂ) * r / 2 + (Real.pi : ℂ) / 2 := by ring
  have h2pi : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  have hcp : ((2 : ℂ) * (Real.pi : ℂ)) ^ (r + 1) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero h2pi]
    exact Complex.exp_ne_zero _
  have hSum : HurwitzZeta.hurwitzZeta ((x : ℝ) : UnitAddCircle) (-r) +
      HurwitzZeta.hurwitzZeta (-((x : ℝ) : UnitAddCircle)) (-r)
      = 2 * HurwitzZeta.hurwitzZetaEven ((x : ℝ) : UnitAddCircle) (-r) := by
    rw [hEven]
    ring
  have hNum : (riemannZeta (-r) - HurwitzZeta.hurwitzZeta ((x : ℝ) : UnitAddCircle) (-r)) +
      (riemannZeta (-r) - HurwitzZeta.hurwitzZeta (-((x : ℝ) : UnitAddCircle)) (-r)) -
      2 * riemannZeta (-r)
      = -(HurwitzZeta.hurwitzZeta ((x : ℝ) : UnitAddCircle) (-r) +
        HurwitzZeta.hurwitzZeta (-((x : ℝ) : UnitAddCircle)) (-r)) := by
    ring
  rw [hL, hNum, hSum, hOneSub, harg, Complex.cos_add_pi_div_two, Complex.cpow_neg]
  field_simp
  ring

/-- **A cosine series for $\varphi_r(x-1) + \varphi_r(-x)$.** For complex $r$ and real $-1 < y < 0$
let $\varphi_r(y) = \zeta(-r) - \zeta(-r, y + 1)$, where $\zeta$ is the Riemann zeta function and
$\zeta(s, a)$ is the Hurwitz zeta function. Let $r$ be a complex number with
$\operatorname{Re} r > -1$ and let $0 < x < 1$. Then the partial sums of
$\sum_{k \ge 1} \cos(2\pi k x) / (2\pi k)^{r+1}$ converge to a limit $L$, and
$$\frac{\varphi_r(x-1) + \varphi_r(-x) - 2\zeta(-r)}{4\,\Gamma(r+1)}
  = \sin\left(\frac{\pi r}{2}\right) L.$$

Proves `Wanted` entry `ramanujan_part1_ch7_entry16_kummercongruence`.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 7, Entry 16.
-/
theorem ramanujan_part1_ch7_entry16_kummercongruence
    (r : ℂ) (x : ℝ) (hr : -1 < r.re) (hx0 : 0 < x) (hx1 : x < 1) :
    ∃! L : ℂ,
      Tendsto (chapter7Entry16PartialSum r x) atTop (𝓝 L) ∧
        chapter7Entry16Left r x hx0 hx1 =
          Complex.sin ((Real.pi : ℂ) * r / 2) * L := by
  have hsRe : (0 : ℝ) < (r + 1).re := by
    have e : ((r + 1 : ℂ)).re = r.re + 1 := by simp
    linarith
  have hKey := entry16KeyTendsto hx0 hx1 (s := r + 1) hsRe
  have hId := entry16LeftEq r x hr hx0 hx1
  have hC : ∀ N : ℕ, chapter7Entry16PartialSum r x N
      = (((2 * (Real.pi : ℂ)) ^ (r + 1)))⁻¹ *
        (∑ k ∈ Finset.Icc 1 N,
          ((Real.cos (2 * Real.pi * (k : ℝ) * x) : ℝ) : ℂ) / ((k : ℂ)) ^ (r + 1)) := by
    intro N
    change ∑ k ∈ Finset.Icc 1 N, chapter7Entry16Term r x k = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    show chapter7Entry16Term r x k = _
    unfold chapter7Entry16Term
    change ((Real.cos (2 * Real.pi * (k : ℝ) * x) : ℝ) : ℂ) /
      ((((2 * Real.pi * (k : ℝ) : ℝ)) : ℂ)) ^ (r + 1) = _
    have h2p : ((2 * (Real.pi : ℂ))) = ((((2 * Real.pi : ℝ)) : ℂ)) := by simp
    have hsplit : ((((2 * Real.pi * (k : ℝ) : ℝ)) : ℂ)) ^ (r + 1)
        = ((((2 * Real.pi : ℝ)) : ℂ)) ^ (r + 1) * ((((k : ℝ)) : ℂ)) ^ (r + 1) := by
      rw [Complex.ofReal_mul]
      exact Complex.mul_cpow_ofReal_nonneg (by positivity) (Nat.cast_nonneg k) (r + 1)
    have hkcast : ((((k : ℝ)) : ℂ)) = ((k : ℂ)) := by norm_cast
    rw [hsplit, hkcast, ← h2p, div_eq_mul_inv, mul_inv, div_eq_mul_inv]
    ring
  have hConv : Filter.Tendsto (chapter7Entry16PartialSum r x) Filter.atTop
      (nhds (HurwitzZeta.cosZeta ((x : ℝ) : UnitAddCircle) (r + 1) /
        (2 * (Real.pi : ℂ)) ^ (r + 1))) := by
    have hmul : Filter.Tendsto
        (fun N : ℕ => (((2 * (Real.pi : ℂ)) ^ (r + 1)))⁻¹ *
          (∑ k ∈ Finset.Icc 1 N,
            ((Real.cos (2 * Real.pi * (k : ℝ) * x) : ℝ) : ℂ) / ((k : ℂ)) ^ (r + 1)))
        Filter.atTop
        (nhds (HurwitzZeta.cosZeta ((x : ℝ) : UnitAddCircle) (r + 1) /
          (2 * (Real.pi : ℂ)) ^ (r + 1))) := by
      have h0 := Filter.Tendsto.mul
        (tendsto_const_nhds (x := (((2 * (Real.pi : ℂ)) ^ (r + 1)))⁻¹)) hKey
      have heq : ((((2 * (Real.pi : ℂ)) ^ (r + 1)))⁻¹ *
            HurwitzZeta.cosZeta ((x : ℝ) : UnitAddCircle) (r + 1))
          = HurwitzZeta.cosZeta ((x : ℝ) : UnitAddCircle) (r + 1) /
            (2 * (Real.pi : ℂ)) ^ (r + 1) := by
        rw [div_eq_mul_inv, mul_comm]
      rwa [heq] at h0
    exact Filter.Tendsto.congr (fun N => (hC N).symm) hmul
  refine ⟨HurwitzZeta.cosZeta ((x : ℝ) : UnitAddCircle) (r + 1) /
    (2 * (Real.pi : ℂ)) ^ (r + 1), ⟨hConv, hId⟩, ?_⟩
  intro y hy
  exact tendsto_nhds_unique hy.1 hConv

end
end Entry16Kummercongruence
end MathlibExt.Analysis.Ramanujan.Part1Ch7
end
