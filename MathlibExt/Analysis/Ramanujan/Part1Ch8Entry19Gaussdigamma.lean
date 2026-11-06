/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import MathlibExt.Analysis.Calculus.EulerMaclaurinFormula
import MathlibExt.Analysis.Ramanujan.Part1Ch7Entry1Powersum

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 8, Entry 19

This file proves Ramanujan's asymptotic expansion for the binomial combination of log-power sums
in Entry 19 and identifies their constant terms with derivatives of the Riemann zeta function.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8

namespace Entry19Gaussdigamma

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry1Powersum

noncomputable section

def chapter8Entry19Approx (n x : ℕ) : ℝ :=
  (n.factorial : ℝ) * x -
    (((bernoulli (n + 1) : ℚ) : ℝ) /
      ((n + 1 : ℕ) * (x : ℝ) ^ n)) -
    ((n : ℝ) * ((bernoulli (n + 2) : ℚ) : ℝ) /
      (2 * (n + 2 : ℕ) * (x : ℝ) ^ (n + 1))) -
    ((n : ℝ) * ((n : ℝ) + 5 / 3) *
      ((bernoulli (n + 3) : ℚ) : ℝ) /
      (8 * (n + 3 : ℕ) * (x : ℝ) ^ (n + 2)))

def chapter8LogPowerSum (m x : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 x, Real.log (k : ℝ) ^ m

def chapter8LogPowerConstant (m : ℕ) : ℝ :=
  (-1 : ℝ) ^ m *
    iteratedDeriv m (fun s : ℝ => (riemannZeta (s : ℂ)).re) 0

def chapter8Psi (m x : ℕ) : ℝ :=
  chapter8LogPowerSum m x - chapter8LogPowerConstant m

def chapter8Entry19Combination (n x : ℕ) : ℝ :=
  ∑ k ∈ range (n + 1),
    (-1 : ℝ) ^ (n + k) * (n.choose k : ℝ) *
      Real.log (x : ℝ) ^ k * chapter8Psi (n - k) x

def chapter8LogPowerConstantApprox (m x : ℕ) : ℝ :=
  chapter8LogPowerSum m x -
    (∫ t in (1 : ℝ)..(x : ℝ), Real.log t ^ m) -
    (1 / 2 : ℝ) * Real.log (x : ℝ) ^ m +
    (-1 : ℝ) ^ (m + 1) * (m.factorial : ℝ)

private theorem ch8e19_iteratedDeriv_re (m : ℕ) (s : ℝ) (hs : s ≠ 1) :
    iteratedDeriv m (fun x : ℝ => (riemannZeta (x : ℂ)).re) s =
      (iteratedDeriv m riemannZeta (s : ℂ)).re := by
  revert s
  induction m with
  | zero => simp
  | succ m ih =>
      intro s hs
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      have heq : iteratedDeriv m (fun x : ℝ => (riemannZeta (x : ℂ)).re) =ᶠ[𝓝 s]
          fun x : ℝ => (iteratedDeriv m riemannZeta (x : ℂ)).re := by
        filter_upwards [eventually_ne_nhds hs] with x hx
        exact ih x hx
      rw [heq.deriv_eq]
      have hsC : (s : ℂ) ≠ 1 := by exact_mod_cast hs
      have hd : DifferentiableAt ℂ (iteratedDeriv m riemannZeta) (s : ℂ) := by
        rw [iteratedDeriv_eq_equiv_comp]
        exact
          (ContinuousMultilinearMap.piFieldEquiv ℂ (Fin m) ℂ).symm.differentiableAt.comp
            (s : ℂ)
            ((analyticOn_riemannZeta.iteratedFDeriv m (s : ℂ) hsC).differentiableAt)
      exact hd.hasDerivAt.real_of_complex.deriv

private noncomputable def ch8e19Kernel (p : ℕ) (x : ℝ) : ℝ :=
  bernoulliFun p (Int.fract x)

private theorem ch8e19Kernel_periodic (p : ℕ) :
    Function.Periodic (ch8e19Kernel p) 1 := by
  intro x
  simp [ch8e19Kernel, Int.fract_add_one]

private theorem ch8e19Kernel_continuous {p : ℕ} (hp : p ≠ 1) :
    Continuous (ch8e19Kernel p) := by
  change Continuous (fun x : ℝ => bernoulliFun p (Int.fract x))
  simpa [Function.comp_def] using
    (continuous_bernoulliFun p).continuousOn.comp_fract''
      (bernoulliFun_endpoints_eq_of_ne_one hp).symm

private theorem ch8e19Kernel_one (N : ℕ) (hN : 0 < N) :
    ch8e19Kernel (2 * N + 1) 1 = 0 := by
  have hodd : Odd (2 * N + 1) := ⟨N, by omega⟩
  have hgt : 1 < 2 * N + 1 := by omega
  simp [ch8e19Kernel, bernoulliFun_eval_zero,
    bernoulli_eq_zero_of_odd hodd hgt]

private noncomputable def ch8e19MellinBase (N : ℕ) (x : ℝ) : ℂ :=
  if 1 ≤ x then (ch8e19Kernel (2 * N + 1) x : ℂ) else 0

private theorem ch8e19MellinBase_continuous (N : ℕ) (hN : 0 < N) :
    Continuous (ch8e19MellinBase N) := by
  have hp : 2 * N + 1 ≠ 1 := by omega
  have hk : Continuous (fun x => (ch8e19Kernel (2 * N + 1) x : ℂ)) :=
    Complex.continuous_ofReal.comp (ch8e19Kernel_continuous hp)
  change Continuous (fun x : ℝ => if 1 ≤ x then
    (ch8e19Kernel (2 * N + 1) x : ℂ) else 0)
  refine hk.if_le continuous_const continuous_const continuous_id ?_
  intro x hx
  have : x = 1 := by linarith
  subst x
  simp [ch8e19Kernel_one N hN]

private theorem ch8e19MellinBase_locallyIntegrable (N : ℕ) (hN : 0 < N) :
    LocallyIntegrableOn (ch8e19MellinBase N) (Set.Ioi 0) :=
  (ch8e19MellinBase_continuous N hN).continuousOn.locallyIntegrableOn measurableSet_Ioi

private theorem ch8e19Kernel_norm_le (N : ℕ) (hN : 0 < N) :
    ∃ C : ℝ, ∀ x : ℝ, ‖ch8e19Kernel (2 * N + 1) x‖ ≤ C := by
  have hp : 2 * N + 1 ≠ 1 := by omega
  obtain ⟨C, hC⟩ := ((ch8e19Kernel_periodic (2 * N + 1)).isBounded_of_continuous
    one_ne_zero (ch8e19Kernel_continuous hp)).exists_norm_le
  exact ⟨C, fun x => hC _ ⟨x, rfl⟩⟩

private theorem ch8e19MellinBase_isBigO_atTop (N : ℕ) (hN : 0 < N) :
    ch8e19MellinBase N =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
  obtain ⟨C, hC⟩ := ch8e19Kernel_norm_le N hN
  refine isBigO_iff.mpr ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  simpa [ch8e19MellinBase, hx] using hC x

private theorem ch8e19MellinBase_isBigO_zero (N : ℕ) (b : ℝ) :
    ch8e19MellinBase N =O[𝓝[>] 0] (fun x : ℝ => x ^ (-b)) := by
  refine isBigO_iff.mpr ⟨0, ?_⟩
  have he : ∀ᶠ x : ℝ in 𝓝[>] 0, x < 1 :=
    Filter.Eventually.filter_mono inf_le_left (Iio_mem_nhds zero_lt_one)
  filter_upwards [he] with x hx
  simp [ch8e19MellinBase, not_le.mpr hx]

private noncomputable def ch8e19MellinIntegral (N : ℕ) (r : ℂ) : ℂ :=
  mellin (ch8e19MellinBase N) (r - (2 * N + 1 : ℕ) + 1)

private theorem ch8e19MellinIntegral_differentiableAt
    (N : ℕ) (hN : 0 < N) (r : ℂ) (hu : r.re < 2 * N) :
    DifferentiableAt ℂ (ch8e19MellinIntegral N) r := by
  let s : ℂ := r - (2 * N + 1 : ℕ) + 1
  have hs : s.re < 0 := by
    dsimp [s]
    norm_num [Nat.cast_add, Nat.cast_mul] at ⊢
    linarith
  have hm : DifferentiableAt ℂ (mellin (ch8e19MellinBase N)) s :=
    mellin_differentiableAt_of_isBigO_rpow
      (ch8e19MellinBase_locallyIntegrable N hN)
      (by simpa using ch8e19MellinBase_isBigO_atTop N hN)
      hs
      (ch8e19MellinBase_isBigO_zero N (s.re - 1))
      (by linarith)
  have hg : DifferentiableAt ℂ (fun z : ℂ => z - (2 * N + 1 : ℕ) + 1) r := by
    fun_prop
  unfold ch8e19MellinIntegral
  convert hm.comp r hg using 1
  rfl

private theorem ch8e19MellinIntegral_eq_integral
    (N : ℕ) (hN : 0 < N) (r : ℂ) :
    ch8e19MellinIntegral N r =
      ∫ x : ℝ in Set.Ioi 1,
        (x : ℂ) ^ (r - (2 * N + 1 : ℕ)) * (ch8e19Kernel (2 * N + 1) x : ℂ) := by
  unfold ch8e19MellinIntegral mellin
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Set.Ioi_subset_Ioi zero_le_one)]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    rw [show r - (2 * N + 1 : ℕ) + 1 - 1 = r - (2 * N + 1 : ℕ) by ring]
    simp [ch8e19MellinBase, hx.le, smul_eq_mul]
  · intro x hx
    rcases lt_or_eq_of_le (le_of_not_gt hx.2) with hlt | rfl
    · simp [ch8e19MellinBase, not_le.mpr hlt]
    · simp [ch8e19MellinBase, ch8e19Kernel_one N hN]

private noncomputable def ch8e19Tail (N : ℕ) (r : ℂ) (n : ℕ) : ℂ :=
  ∫ x : ℝ in Set.Ioi (n : ℝ),
    (x : ℂ) ^ (r - (2 * N + 1 : ℕ)) * (ch8e19Kernel (2 * N + 1) x : ℂ)

private theorem ch8e19Tail_integrable
    (N : ℕ) (hN : 0 < N) (r : ℂ) (hu : r.re < 2 * N) :
    IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (r - (2 * N + 1 : ℕ)) *
        (ch8e19Kernel (2 * N + 1) x : ℂ)) (Set.Ioi 1) := by
  let s : ℂ := r - (2 * N + 1 : ℕ) + 1
  have hs : s.re < 0 := by
    dsimp [s]
    norm_num [Nat.cast_add, Nat.cast_mul] at ⊢
    linarith
  have hconv : MellinConvergent (ch8e19MellinBase N) s :=
    mellinConvergent_of_isBigO_rpow
      (ch8e19MellinBase_locallyIntegrable N hN)
      (by simpa using ch8e19MellinBase_isBigO_atTop N hN) hs
      (ch8e19MellinBase_isBigO_zero N (s.re - 1)) (by linarith)
  rw [MellinConvergent] at hconv
  refine (hconv.mono_set (Set.Ioi_subset_Ioi zero_le_one)).congr_fun ?_ measurableSet_Ioi
  intro x hx
  have hsr : s - 1 = r - (2 * N + 1 : ℕ) := by simp [s]
  rw [hsr]
  simp [ch8e19MellinBase, hx.le, smul_eq_mul]

private theorem ch8e19Tail_norm_le_uniform (N : ℕ) (hN : 0 < N) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ r ∈ Metric.sphere (0 : ℂ) (1 / 2 : ℝ), ∀ x : ℕ, 1 ≤ x →
      ‖ch8e19Tail N r x‖ ≤
        D * Real.rpow (x : ℝ) (-2 * (N : ℝ) + 1 / 2) := by
  obtain ⟨C, hC⟩ := ch8e19Kernel_norm_le N hN
  have hC0 : 0 ≤ C := (norm_nonneg (ch8e19Kernel (2 * N + 1) 0)).trans (hC 0)
  let a : ℝ := -2 * (N : ℝ) - 1 / 2
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ha : a < -1 := by
    dsimp [a]
    linarith
  have hden : 0 < 2 * (N : ℝ) - 1 / 2 := by
    linarith
  let D : ℝ := C / (2 * (N : ℝ) - 1 / 2)
  refine ⟨D, div_nonneg hC0 hden.le, ?_⟩
  intro r hr x hx
  have hxpos : 0 < (x : ℝ) := by positivity
  have hrnorm : ‖r‖ = (1 / 2 : ℝ) := by
    simpa [Metric.mem_sphere] using hr
  have hre : r.re ≤ (1 / 2 : ℝ) := (Complex.re_le_norm r).trans hrnorm.le
  have hg : Integrable (fun t : ℝ ↦ C * t ^ a)
      (volume.restrict (Set.Ioi (x : ℝ))) :=
    (integrableOn_Ioi_rpow_of_lt ha hxpos).const_mul C
  have hpoint (t : ℝ) (ht : t ∈ Set.Ioi (x : ℝ)) :
      ‖(t : ℂ) ^ (r - (2 * N + 1 : ℕ)) *
          (ch8e19Kernel (2 * N + 1) t : ℂ)‖ ≤ C * t ^ a := by
    have htpos : 0 < t := hxpos.trans ht
    have ht_one : 1 ≤ t := by
      have hx_one : (1 : ℝ) ≤ x := by exact_mod_cast hx
      exact hx_one.trans ht.le
    have hexp : (r - (2 * N + 1 : ℕ)).re ≤ a := by
      dsimp [a]
      norm_num [Nat.cast_add, Nat.cast_mul]
      linarith
    calc
      ‖(t : ℂ) ^ (r - (2 * N + 1 : ℕ)) *
          (ch8e19Kernel (2 * N + 1) t : ℂ)‖ =
          t ^ (r - (2 * N + 1 : ℕ)).re *
            ‖ch8e19Kernel (2 * N + 1) t‖ := by
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos htpos, Complex.norm_real]
      _ ≤ t ^ a * C := by
        exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le ht_one hexp) (hC t)
          (norm_nonneg _) (Real.rpow_nonneg htpos.le _)
      _ = C * t ^ a := by ring
  have hnorm :
      ‖∫ t : ℝ in Set.Ioi (x : ℝ),
          (t : ℂ) ^ (r - (2 * N + 1 : ℕ)) *
            (ch8e19Kernel (2 * N + 1) t : ℂ)‖ ≤
        ∫ t : ℝ in Set.Ioi (x : ℝ), C * t ^ a :=
    MeasureTheory.norm_integral_le_of_norm_le hg
      ((ae_restrict_mem measurableSet_Ioi).mono hpoint)
  unfold ch8e19Tail
  calc
    ‖∫ t : ℝ in Set.Ioi (x : ℝ),
        (t : ℂ) ^ (r - (2 * N + 1 : ℕ)) *
          (ch8e19Kernel (2 * N + 1) t : ℂ)‖ ≤
      ∫ t : ℝ in Set.Ioi (x : ℝ), C * t ^ a := hnorm
    _ = C * (∫ t : ℝ in Set.Ioi (x : ℝ), t ^ a) := by
      rw [MeasureTheory.integral_const_mul]
    _ = C * (-(x : ℝ) ^ (a + 1) / (a + 1)) := by
      rw [integral_Ioi_rpow_of_lt ha hxpos]
    _ = D * Real.rpow (x : ℝ) (-2 * (N : ℝ) + 1 / 2) := by
      rw [Real.rpow_eq_pow]
      have ha1 : a + 1 = -(2 * (N : ℝ) - 1 / 2) := by
        dsimp [a]
        ring
      rw [ha1]
      dsimp [D]
      have hne : 2 * (N : ℝ) - 1 / 2 ≠ 0 := hden.ne'
      field_simp [hne]
      ring_nf

private theorem ch8e19_bernoulli_coeff (j : ℕ) :
    ((bernoulli j : ℚ) : ℝ) =
      if j = 1 then (-1 / 2 : ℝ) else (bernoulli j : ℝ) := by
  by_cases hj : j = 1
  · subst j
    simp [bernoulli_one]
  · simp [hj]

private theorem ch8e19_bernoulliFun_eq_sum (p : ℕ) (x : ℝ) :
    bernoulliFun p x =
      ∑ j ∈ Finset.range (p + 1), (Nat.choose p j : ℝ) *
        (if j = 1 then (-1 / 2 : ℝ) else (bernoulli j : ℝ)) * x ^ (p - j) := by
  rw [show bernoulliFun p x =
    Polynomial.eval x (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli p)) by rfl]
  rw [Polynomial.bernoulli_def, Polynomial.map_sum, Polynomial.eval_finsetSum]
  have hterm : ∀ i ∈ Finset.range (p + 1),
      Polynomial.eval x (Polynomial.map (algebraMap ℚ ℝ)
        (Polynomial.monomial i (bernoulli (p - i) * ↑(p.choose i)))) =
        ((bernoulli (p - i) : ℚ) : ℝ) * (Nat.choose p i : ℝ) * x ^ i := by
    intro i _
    rw [Polynomial.map_monomial, Polynomial.eval_monomial]
    simp only [map_mul, map_natCast, eq_ratCast]
  rw [Finset.sum_congr rfl hterm]
  have hrefl : (∑ i ∈ Finset.range (p + 1),
      ((bernoulli (p - i) : ℚ) : ℝ) * (Nat.choose p i : ℝ) * x ^ i) =
      ∑ j ∈ Finset.range (p + 1),
        ((bernoulli j : ℚ) : ℝ) * (Nat.choose p (p - j) : ℝ) * x ^ (p - j) := by
    rw [← Finset.sum_range_reflect (fun j => ((bernoulli j : ℚ) : ℝ) *
      (Nat.choose p (p - j) : ℝ) * x ^ (p - j)) (p + 1)]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [show p + 1 - 1 - i = p - i by omega, show p - (p - i) = i by omega]
  rw [hrefl]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  rw [← ch8e19_bernoulli_coeff j, Nat.choose_symm (by omega : j ≤ p)]
  ring

private theorem ch8e19Kernel_eq_of_spec
    (P : ℕ → ℝ → ℝ) (p : ℕ)
    (hper : ∀ (m : ℕ) (x : ℝ), P m (x + 1) = P m x)
    (hunit : ∀ x ∈ Set.Ico (0 : ℝ) 1, P p x =
      ∑ j ∈ Finset.range (p + 1), (Nat.choose p j : ℝ) *
        (if j = 1 then (-1 / 2 : ℝ) else (bernoulli j : ℝ)) * x ^ (p - j))
    (x : ℝ) :
    P p x = ch8e19Kernel p x := by
  have hp : Function.Periodic (P p) 1 := hper p
  have hfract : P p (Int.fract x) = P p x := by
    rw [Int.fract]
    simpa only [mul_one] using hp.sub_int_mul_eq (Int.floor x)
  rw [← hfract, hunit (Int.fract x) ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩]
  exact (ch8e19_bernoulliFun_eq_sum p (Int.fract x)).symm

private theorem ch8e19EulerMaclaurin_real
    (a b : ℤ) (p : ℕ) (f : ℝ → ℝ) (hab : a < b) (hp : 1 ≤ p)
    (hdf : ContDiffOn ℝ (p : WithTop ℕ∞) f (Set.Icc (a : ℝ) (b : ℝ))) :
    ∑ n ∈ Finset.Icc a b, f (n : ℝ) =
      (∫ x in (a : ℝ)..(b : ℝ), f x) + (f a + f b) / 2 +
        (∑ k ∈ Finset.Icc 1 (p / 2),
          (bernoulli (2 * k) : ℝ) / (Nat.factorial (2 * k) : ℝ) *
            (iteratedDerivWithin (2 * k - 1) f (Set.Icc (a : ℝ) (b : ℝ)) b -
              iteratedDerivWithin (2 * k - 1) f (Set.Icc (a : ℝ) (b : ℝ)) a)) +
        ((-1 : ℝ) ^ (p + 1) / (Nat.factorial p : ℝ) *
          (∫ x in (a : ℝ)..(b : ℝ), ch8e19Kernel p x *
            iteratedDerivWithin p f (Set.Icc (a : ℝ) (b : ℝ)) x)) := by
  obtain ⟨P, hper, hunit, hformula⟩ :=
    MetaMathlibExt.eulerMaclaurinFormula a b p f hab hp hdf
  simpa only [ch8e19Kernel_eq_of_spec P p hper hunit] using hformula

private theorem ch8e19_iteratedDerivWithin_re
    {f : ℝ → ℂ} {s : Set ℝ} {x : ℝ} (q : ℕ)
    (hf : ContDiffWithinAt ℝ q f s x) (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    iteratedDerivWithin q (fun y => (f y).re) s x =
      (iteratedDerivWithin q f s x).re := by
  change iteratedDerivWithin q (Complex.reCLM ∘ f) s x =
    Complex.reCLM (iteratedDerivWithin q f s x)
  unfold iteratedDerivWithin
  rw [Complex.reCLM.iteratedFDerivWithin_comp_left hf hs hx le_rfl]
  rfl

private theorem ch8e19_iteratedDerivWithin_im
    {f : ℝ → ℂ} {s : Set ℝ} {x : ℝ} (q : ℕ)
    (hf : ContDiffWithinAt ℝ q f s x) (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    iteratedDerivWithin q (fun y => (f y).im) s x =
      (iteratedDerivWithin q f s x).im := by
  change iteratedDerivWithin q (Complex.imCLM ∘ f) s x =
    Complex.imCLM (iteratedDerivWithin q f s x)
  unfold iteratedDerivWithin
  rw [Complex.imCLM.iteratedFDerivWithin_comp_left hf hs hx le_rfl]
  rfl

private theorem ch8e19EulerMaclaurin_complex
    (a b : ℤ) (p : ℕ) (f : ℝ → ℂ) (hab : a < b) (hp : 1 ≤ p) (hp1 : p ≠ 1)
    (hdf : ContDiffOn ℝ (p : WithTop ℕ∞) f (Set.Icc (a : ℝ) (b : ℝ))) :
    ∑ n ∈ Finset.Icc a b, f (n : ℝ) =
      (∫ x in (a : ℝ)..(b : ℝ), f x) + (f a + f b) / 2 +
        (∑ k ∈ Finset.Icc 1 (p / 2),
          ((bernoulli (2 * k) : ℝ) : ℂ) / (Nat.factorial (2 * k) : ℝ) *
            (iteratedDerivWithin (2 * k - 1) f (Set.Icc (a : ℝ) (b : ℝ)) b -
              iteratedDerivWithin (2 * k - 1) f (Set.Icc (a : ℝ) (b : ℝ)) a)) +
        ((((-1 : ℝ) ^ (p + 1) / (Nat.factorial p : ℝ) : ℝ) : ℂ) *
          (∫ x in (a : ℝ)..(b : ℝ), (ch8e19Kernel p x : ℂ) *
            iteratedDerivWithin p f (Set.Icc (a : ℝ) (b : ℝ)) x)) := by
  let s : Set ℝ := Set.Icc (a : ℝ) (b : ℝ)
  have habr : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  have hs : UniqueDiffOn ℝ s := uniqueDiffOn_Icc habr
  have hdfre : ContDiffOn ℝ (p : WithTop ℕ∞) (fun x => (f x).re) s := by
    change ContDiffOn ℝ (p : WithTop ℕ∞) (Complex.reCLM ∘ f) s
    exact hdf.continuousLinearMap_comp Complex.reCLM
  have hdfim : ContDiffOn ℝ (p : WithTop ℕ∞) (fun x => (f x).im) s := by
    change ContDiffOn ℝ (p : WithTop ℕ∞) (Complex.imCLM ∘ f) s
    exact hdf.continuousLinearMap_comp Complex.imCLM
  have hR := ch8e19EulerMaclaurin_real a b p (fun x => (f x).re) hab hp hdfre
  have hI := ch8e19EulerMaclaurin_real a b p (fun x => (f x).im) hab hp hdfim
  have hder_re (q : ℕ) (hq : q ≤ p) (x : ℝ) (hx : x ∈ s) :
      iteratedDerivWithin q (fun y => (f y).re) s x =
        (iteratedDerivWithin q f s x).re :=
    ch8e19_iteratedDerivWithin_re q ((hdf x hx).of_le (by exact_mod_cast hq)) hs hx
  have hder_im (q : ℕ) (hq : q ≤ p) (x : ℝ) (hx : x ∈ s) :
      iteratedDerivWithin q (fun y => (f y).im) s x =
        (iteratedDerivWithin q f s x).im :=
    ch8e19_iteratedDerivWithin_im q ((hdf x hx).of_le (by exact_mod_cast hq)) hs hx
  have hfint : IntervalIntegrable f volume (a : ℝ) (b : ℝ) :=
    (hdf.continuousOn.mono (by simp [Set.uIcc_of_le habr.le])).intervalIntegrable
  have hdcont : ContinuousOn (iteratedDerivWithin p f s) s :=
    hdf.continuousOn_iteratedDerivWithin le_rfl hs
  have hremint : IntervalIntegrable
      (fun x => (ch8e19Kernel p x : ℂ) * iteratedDerivWithin p f s x)
      volume (a : ℝ) (b : ℝ) :=
    (((Complex.continuous_ofReal.comp (ch8e19Kernel_continuous hp1)).continuousOn.mul
      hdcont).mono (by simp [s, Set.uIcc_of_le habr.le])).intervalIntegrable
  have hrem_re :
      (∫ x in (a : ℝ)..(b : ℝ), ch8e19Kernel p x *
          iteratedDerivWithin p (fun y => (f y).re) s x) =
        (∫ x in (a : ℝ)..(b : ℝ), (ch8e19Kernel p x : ℂ) *
          iteratedDerivWithin p f s x).re := by
    calc
      _ = ∫ x in (a : ℝ)..(b : ℝ),
          ((ch8e19Kernel p x : ℂ) * iteratedDerivWithin p f s x).re := by
        apply intervalIntegral.integral_congr
        intro x hx
        change ch8e19Kernel p x * iteratedDerivWithin p (fun y => (f y).re) s x =
          ((ch8e19Kernel p x : ℂ) * iteratedDerivWithin p f s x).re
        rw [hder_re p le_rfl x (by simpa [s, Set.uIcc_of_le habr.le] using hx)]
        simp
      _ = _ := intervalIntegral.intervalIntegral_re hremint
  have hrem_im :
      (∫ x in (a : ℝ)..(b : ℝ), ch8e19Kernel p x *
          iteratedDerivWithin p (fun y => (f y).im) s x) =
        (∫ x in (a : ℝ)..(b : ℝ), (ch8e19Kernel p x : ℂ) *
          iteratedDerivWithin p f s x).im := by
    calc
      _ = ∫ x in (a : ℝ)..(b : ℝ),
          ((ch8e19Kernel p x : ℂ) * iteratedDerivWithin p f s x).im := by
        apply intervalIntegral.integral_congr
        intro x hx
        change ch8e19Kernel p x * iteratedDerivWithin p (fun y => (f y).im) s x =
          ((ch8e19Kernel p x : ℂ) * iteratedDerivWithin p f s x).im
        rw [hder_im p le_rfl x (by simpa [s, Set.uIcc_of_le habr.le] using hx)]
        simp
      _ = _ := intervalIntegral.intervalIntegral_im hremint
  have hf_re : (∫ x in (a : ℝ)..(b : ℝ), f x).re =
      ∫ x in (a : ℝ)..(b : ℝ), (f x).re :=
    (intervalIntegral.intervalIntegral_re hfint).symm
  have hf_im : (∫ x in (a : ℝ)..(b : ℝ), f x).im =
      ∫ x in (a : ℝ)..(b : ℝ), (f x).im :=
    (intervalIntegral.intervalIntegral_im hfint).symm
  have hsum_re :
      (∑ k ∈ Finset.Icc 1 (p / 2),
        (bernoulli (2 * k) : ℝ) / (Nat.factorial (2 * k) : ℝ) *
          (iteratedDerivWithin (2 * k - 1) (fun x => (f x).re) s b -
            iteratedDerivWithin (2 * k - 1) (fun x => (f x).re) s a)) =
      ∑ k ∈ Finset.Icc 1 (p / 2),
        (((bernoulli (2 * k) : ℝ) : ℂ) / (Nat.factorial (2 * k) : ℝ) *
          (iteratedDerivWithin (2 * k - 1) f s b -
            iteratedDerivWithin (2 * k - 1) f s a)).re := by
    apply Finset.sum_congr rfl
    intro k hk
    have hq : 2 * k - 1 ≤ p := by
      have := (Finset.mem_Icc.mp hk).2
      omega
    rw [hder_re _ hq b (by simp [s, habr.le]), hder_re _ hq a (by simp [s, habr.le])]
    simp [Complex.mul_re]
  have hsum_im :
      (∑ k ∈ Finset.Icc 1 (p / 2),
        (bernoulli (2 * k) : ℝ) / (Nat.factorial (2 * k) : ℝ) *
          (iteratedDerivWithin (2 * k - 1) (fun x => (f x).im) s b -
            iteratedDerivWithin (2 * k - 1) (fun x => (f x).im) s a)) =
      ∑ k ∈ Finset.Icc 1 (p / 2),
        (((bernoulli (2 * k) : ℝ) : ℂ) / (Nat.factorial (2 * k) : ℝ) *
          (iteratedDerivWithin (2 * k - 1) f s b -
            iteratedDerivWithin (2 * k - 1) f s a)).im := by
    apply Finset.sum_congr rfl
    intro k hk
    have hq : 2 * k - 1 ≤ p := by
      have := (Finset.mem_Icc.mp hk).2
      omega
    rw [hder_im _ hq b (by simp [s, habr.le]), hder_im _ hq a (by simp [s, habr.le])]
    simp [Complex.mul_im]
  apply Complex.ext
  · simp only [Complex.re_sum, Complex.add_re, Complex.div_ofNat_re]
    rw [hf_re, ← hsum_re]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [← hrem_re]
    exact hR
  · simp only [Complex.im_sum, Complex.add_im, Complex.div_ofNat_im]
    rw [hf_im, ← hsum_im]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    rw [← hrem_im]
    simpa [s] using hI

private theorem ch8e19Falling_succ (r : ℂ) (q : ℕ) :
    chapter7FallingGammaRatio r (q + 1) =
      chapter7FallingGammaRatio r q * (r - (q : ℂ)) := by
  simp [chapter7FallingGammaRatio, Finset.prod_range_succ]

private theorem ch8e19_iteratedDeriv_cpow
    (r : ℂ) (q : ℕ) {x : ℝ} (hx : x ≠ 0) :
    iteratedDeriv q (fun y : ℝ => (y : ℂ) ^ r) x =
      chapter7FallingGammaRatio r q * (x : ℂ) ^ (r - (q : ℕ)) := by
  induction q generalizing x with
  | zero => simp [chapter7FallingGammaRatio]
  | succ q ih =>
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv q (fun y : ℝ => (y : ℂ) ^ r) =ᶠ[𝓝 x]
          fun y : ℝ => chapter7FallingGammaRatio r q * (y : ℂ) ^ (r - (q : ℕ)) := by
        filter_upwards [isOpen_ne.mem_nhds hx] with y hy
        exact ih hy
      rw [heq.deriv_eq]
      by_cases he : r - (q : ℕ) = 0
      · simp [he, ch8e19Falling_succ]
      · have hd := (hasDerivAt_ofReal_cpow_const hx he).const_mul
            (chapter7FallingGammaRatio r q)
        rw [hd.deriv, ch8e19Falling_succ]
        rw [show r - ((q + 1 : ℕ) : ℂ) = r - (q : ℂ) - 1 by
          push_cast
          ring]
        ring

private theorem ch8e19_cpow_contDiffAt
    (r : ℂ) {x : ℝ} (hx : 0 < x) {m : WithTop ℕ∞} :
    ContDiffAt ℝ m (fun y : ℝ => (y : ℂ) ^ r) x := by
  have hc : ContDiffAt ℂ m (fun z : ℂ => z ^ r) (x : ℂ) :=
    (analyticAt_id.cpow analyticAt_const (Complex.ofReal_mem_slitPlane.mpr hx)).contDiffAt
  exact (hc.restrict_scalars ℝ).comp x Complex.ofRealCLM.contDiff.contDiffAt

private theorem ch8e19_cpow_contDiffOn
    (r : ℂ) (p n : ℕ) :
    ContDiffOn ℝ (p : WithTop ℕ∞) (fun x : ℝ => (x : ℂ) ^ r)
      (Set.Icc 1 (n : ℝ)) := by
  intro x hx
  exact (ch8e19_cpow_contDiffAt r (lt_of_lt_of_le zero_lt_one hx.1)).contDiffWithinAt

private theorem ch8e19_iteratedDerivWithin_cpow
    (r : ℂ) (q n : ℕ) (hn : 1 < n) {x : ℝ} (hx : x ∈ Set.Icc 1 (n : ℝ)) :
    iteratedDerivWithin q (fun y : ℝ => (y : ℂ) ^ r) (Set.Icc 1 (n : ℝ)) x =
      chapter7FallingGammaRatio r q * (x : ℂ) ^ (r - (q : ℕ)) := by
  rw [iteratedDerivWithin_eq_iteratedDeriv
    (uniqueDiffOn_Icc (by exact_mod_cast hn))
    (ch8e19_cpow_contDiffAt r (lt_of_lt_of_le zero_lt_one hx.1)) hx]
  exact ch8e19_iteratedDeriv_cpow r q (ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1))

private noncomputable def ch8e19RemainderFactor (N : ℕ) (r : ℂ) : ℂ :=
  chapter7FallingGammaRatio r (2 * N + 1) / ((2 * N + 1).factorial : ℂ)

private noncomputable def ch8e19Constant (N : ℕ) (r : ℂ) : ℂ :=
  1 / 2 - 1 / (r + 1) - ∑ j ∈ Finset.range N, chapter7Entry1Term r 1 j +
    ch8e19RemainderFactor N r * ch8e19MellinIntegral N r

private theorem ch8e19_intervalIntegral_eq_mellin_sub_tail
    (N : ℕ) (hN : 0 < N) (r : ℂ) (hu : r.re < 2 * N) (n : ℕ) (hn : 1 < n) :
    (∫ x : ℝ in (1 : ℝ)..(n : ℝ),
        (x : ℂ) ^ (r - (2 * N + 1 : ℕ)) * (ch8e19Kernel (2 * N + 1) x : ℂ)) =
      ch8e19MellinIntegral N r - ch8e19Tail N r n := by
  let g : ℝ → ℂ := fun x => (x : ℂ) ^ (r - (2 * N + 1 : ℕ)) *
    (ch8e19Kernel (2 * N + 1) x : ℂ)
  have hIoi : IntegrableOn g (Set.Ioi 1) := ch8e19Tail_integrable N hN r hu
  have hIci : IntegrableOn g (Set.Ici 1) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr hIoi
  have hIciN : IntegrableOn g (Set.Ici (n : ℝ)) :=
    hIci.mono_set (Set.Ici_subset_Ici.mpr (by exact_mod_cast hn.le))
  have hsplit := intervalIntegral.integral_Ici_sub_Ici' hIci hIciN
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi,
    MeasureTheory.integral_Ici_eq_integral_Ioi] at hsplit
  calc
    (∫ x : ℝ in (1 : ℝ)..(n : ℝ), g x) =
        (∫ x : ℝ in Set.Ioi 1, g x) - ∫ x : ℝ in Set.Ioi (n : ℝ), g x := hsplit.symm
    _ = ch8e19MellinIntegral N r - ch8e19Tail N r n := by
      rw [ch8e19MellinIntegral_eq_integral N hN r]
      rfl

private theorem ch8e19_sum_int_eq_powerSum (r : ℂ) (n : ℕ) :
    (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), ((k : ℝ) : ℂ) ^ r) =
      chapter7PowerSum r n := by
  unfold chapter7PowerSum chapter7NatCpow
  rw [eq_comm]
  apply Finset.sum_bij (fun (k : ℕ) _ => (k : ℤ))
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  · intro k₁ hk₁ k₂ hk₂ h
    exact_mod_cast h
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    refine ⟨k.toNat, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · exact Int.toNat_of_nonneg (by omega)
  · intro k hk
    norm_cast

private theorem ch8e19_eulerMaclaurin_raw
    (r : ℂ) (N n : ℕ) (hr : r ≠ -1) (hN : 0 < N) (hu : r.re < 2 * N)
    (hn : 1 < n) :
    chapter7PowerSum r n =
      (chapter7NatCpow n (r + 1) - 1) / (r + 1) +
        (1 + chapter7NatCpow n r) / 2 +
        (∑ k ∈ Finset.Icc 1 N,
          (((bernoulli (2 * k) : ℚ) : ℂ) / ((2 * k).factorial : ℂ)) *
            chapter7FallingGammaRatio r (2 * k - 1) *
              (chapter7NatCpow n (r - (2 * k : ℕ) + 1) - 1)) +
        ch8e19RemainderFactor N r *
          (ch8e19MellinIntegral N r - ch8e19Tail N r n) := by
  let p := 2 * N + 1
  have hp : 1 ≤ p := by simp [p]
  have hp1 : p ≠ 1 := by omega
  have hab : (1 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  have hdf : ContDiffOn ℝ (p : WithTop ℕ∞) (fun x : ℝ => (x : ℂ) ^ r)
      (Set.Icc (1 : ℝ) (n : ℝ)) := ch8e19_cpow_contDiffOn r p n
  have hem := ch8e19EulerMaclaurin_complex (1 : ℤ) (n : ℤ) p
    (fun x : ℝ => (x : ℂ) ^ r) hab hp hp1
      (by simpa only [Int.cast_one, Int.cast_natCast] using hdf)
  simp only [Int.cast_one, Int.cast_natCast] at hem
  rw [ch8e19_sum_int_eq_powerSum r n] at hem
  have hpdiv : p / 2 = N := by omega
  rw [hpdiv] at hem
  have hle : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.le
  have hzero : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (n : ℝ) := by
    rw [Set.uIcc_of_le hle]
    intro h
    exact (not_le_of_gt zero_lt_one) h.1
  have hncast : (((n : ℝ) : ℂ)) = (n : ℂ) := Complex.ofReal_natCast n
  have hint : (∫ x : ℝ in (1 : ℝ)..(n : ℝ), (x : ℂ) ^ r) =
      (chapter7NatCpow n (r + 1) - 1) / (r + 1) := by
    rw [integral_cpow (Or.inr ⟨hr, hzero⟩)]
    rw [hncast, Complex.ofReal_one, Complex.one_cpow]
    rfl
  have hsum :
      (∑ k ∈ Finset.Icc 1 N,
        ((bernoulli (2 * k) : ℝ) : ℂ) / (Nat.factorial (2 * k) : ℝ) *
          (iteratedDerivWithin (2 * k - 1) (fun x : ℝ => (x : ℂ) ^ r)
              (Set.Icc (1 : ℝ) (n : ℝ)) n -
            iteratedDerivWithin (2 * k - 1) (fun x : ℝ => (x : ℂ) ^ r)
              (Set.Icc (1 : ℝ) (n : ℝ)) 1)) =
      ∑ k ∈ Finset.Icc 1 N,
        (((bernoulli (2 * k) : ℚ) : ℂ) / ((2 * k).factorial : ℂ)) *
          chapter7FallingGammaRatio r (2 * k - 1) *
            (chapter7NatCpow n (r - (2 * k : ℕ) + 1) - 1) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    rw [ch8e19_iteratedDerivWithin_cpow r (2 * k - 1) n hn
        (by exact ⟨by exact_mod_cast hn.le, le_rfl⟩),
      ch8e19_iteratedDerivWithin_cpow r (2 * k - 1) n hn
        (by exact ⟨le_rfl, by exact_mod_cast hn.le⟩)]
    rw [show r - ((2 * k - 1 : ℕ) : ℂ) = r - (2 * k : ℕ) + 1 by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * k)]
      push_cast
      ring]
    rw [hncast]
    unfold chapter7NatCpow
    norm_cast
    have hpow : (n : ℂ) ^ (r - (2 * k : ℕ) + 1) =
        Complex.cpow (n : ℂ) (r - (2 * k : ℕ) + 1) := rfl
    rw [hpow, Complex.one_cpow]
    ring
  have hrem :
      (∫ x : ℝ in (1 : ℝ)..(n : ℝ), (ch8e19Kernel p x : ℂ) *
        iteratedDerivWithin p (fun y : ℝ => (y : ℂ) ^ r)
          (Set.Icc (1 : ℝ) (n : ℝ)) x) =
      chapter7FallingGammaRatio r p *
        (ch8e19MellinIntegral N r - ch8e19Tail N r n) := by
    calc
      _ = ∫ x : ℝ in (1 : ℝ)..(n : ℝ), chapter7FallingGammaRatio r p *
          ((x : ℂ) ^ (r - (p : ℕ)) * (ch8e19Kernel p x : ℂ)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        change (ch8e19Kernel p x : ℂ) *
            iteratedDerivWithin p (fun y : ℝ => (y : ℂ) ^ r)
              (Set.Icc (1 : ℝ) (n : ℝ)) x =
          chapter7FallingGammaRatio r p *
            ((x : ℂ) ^ (r - (p : ℕ)) * (ch8e19Kernel p x : ℂ))
        have hx' : x ∈ Set.Icc (1 : ℝ) (n : ℝ) := by
          rcases Set.mem_uIcc.mp hx with hx | hx
          · exact hx
          · exact ⟨hle.trans hx.1, hx.2.trans hle⟩
        rw [ch8e19_iteratedDerivWithin_cpow r p n hn hx']
        ring
      _ = chapter7FallingGammaRatio r p *
          (∫ x : ℝ in (1 : ℝ)..(n : ℝ),
            (x : ℂ) ^ (r - (p : ℕ)) * (ch8e19Kernel p x : ℂ)) :=
        intervalIntegral.integral_const_mul _ _
      _ = _ := by
        rw [show p = 2 * N + 1 by rfl,
          ch8e19_intervalIntegral_eq_mellin_sub_tail N hN r hu n hn]
  rw [hint, hsum, hrem] at hem
  have hsign : (-1 : ℝ) ^ (p + 1) = 1 :=
    Even.neg_one_pow ⟨N + 1, by simp [p]; ring⟩
  have hend : (((1 : ℝ) : ℂ) ^ r + (((n : ℝ) : ℂ) ^ r)) / 2 =
      (1 + chapter7NatCpow n r) / 2 := by
    change (1 ^ r + (n : ℂ) ^ r) / 2 = (1 + chapter7NatCpow n r) / 2
    simp [chapter7NatCpow]
  rw [hend] at hem
  have hlast :
      ((((-1 : ℝ) ^ (p + 1) / (p.factorial : ℝ) : ℝ) : ℂ) *
          (chapter7FallingGammaRatio r p *
            (ch8e19MellinIntegral N r - ch8e19Tail N r n))) =
        ch8e19RemainderFactor N r *
          (ch8e19MellinIntegral N r - ch8e19Tail N r n) := by
    rw [hsign]
    simp only [one_div]
    unfold ch8e19RemainderFactor
    rw [show p = 2 * N + 1 by rfl]
    push_cast
    ring
  rw [hlast] at hem
  exact hem

private theorem ch8e19_sum_Icc_eq_range {M : Type*} [AddCommMonoid M]
    (N : ℕ) (f : ℕ → M) :
    (∑ k ∈ Finset.Icc 1 N, f k) = ∑ j ∈ Finset.range N, f (j + 1) := by
  rw [eq_comm]
  apply Finset.sum_bij (fun j _ => j + 1)
  · intro j hj
    simp only [Finset.mem_range, Finset.mem_Icc] at hj ⊢
    omega
  · intro j₁ hj₁ j₂ hj₂ h
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    refine ⟨k - 1, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro j hj
    rfl

private theorem ch8e19_exact_expansion
    (r : ℂ) (N n : ℕ) (hr : r ≠ -1) (hN : 0 < N) (hu : r.re < 2 * N)
    (hn : 1 < n) :
    chapter7PowerSum r n =
      ch8e19Constant N r + chapter7NatCpow n (r + 1) / (r + 1) +
        chapter7NatCpow n r / 2 +
        ∑ j ∈ Finset.range N, chapter7Entry1Term r n j -
          ch8e19RemainderFactor N r * ch8e19Tail N r n := by
  have hraw := ch8e19_eulerMaclaurin_raw r N n hr hN hu hn
  have hsum :
      (∑ k ∈ Finset.Icc 1 N,
        (((bernoulli (2 * k) : ℚ) : ℂ) / ((2 * k).factorial : ℂ)) *
          chapter7FallingGammaRatio r (2 * k - 1) *
            (chapter7NatCpow n (r - (2 * k : ℕ) + 1) - 1)) =
      (∑ j ∈ Finset.range N, chapter7Entry1Term r n j) -
        ∑ j ∈ Finset.range N, chapter7Entry1Term r 1 j := by
    rw [ch8e19_sum_Icc_eq_range]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [chapter7Entry1Term]
    have hone : chapter7NatCpow 1 (r - ((2 * (j + 1) : ℕ) : ℂ) + 1) = 1 := by
      simp [chapter7NatCpow]
    rw [hone]
    have he : r - ((2 * (j + 1) : ℕ) : ℂ) + 1 =
        r - ((2 * j + 2 : ℕ) : ℂ) + 1 := by
      push_cast
      ring
    rw [he]
    ring
  rw [hsum] at hraw
  unfold ch8e19Constant
  linear_combination hraw

private theorem ch8e19Tail_tendsto_zero (N : ℕ) (r : ℂ) :
    Tendsto (ch8e19Tail N r) atTop (𝓝 0) := by
  unfold ch8e19Tail
  exact MeasureTheory.tendsto_integral_Ioi_zero tendsto_natCast_atTop_atTop

private theorem ch8e19Constant_eq_zeta
    (N : ℕ) (hN : 0 < N) (r : ℂ) (hr : r ≠ -1) (hu : r.re < 2 * N) :
    ch8e19Constant N r = riemannZeta (-r) := by
  have hpow : Tendsto
      (fun n : ℕ => Real.rpow (n : ℝ) (r.re - 2 * (N : ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop
      (by linarith : 0 < 2 * (N : ℝ) - r.re)).comp tendsto_natCast_atTop_atTop
    convert h using 1
    funext n
    congr 1
    ring
  have hdiff :=
    (ramanujan_part1_ch7_entry1_powersum r N hr hN hu).trans_tendsto hpow
  have htail := ch8e19Tail_tendsto_zero N r
  have hrem : Tendsto
      (fun n : ℕ => ch8e19RemainderFactor N r * ch8e19Tail N r n)
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul htail
  have heq : ∀ᶠ n : ℕ in atTop,
      chapter7PowerSum r n - chapter7Entry1Approx r N n =
        (ch8e19Constant N r - riemannZeta (-r)) -
          ch8e19RemainderFactor N r * ch8e19Tail N r n := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    rw [ch8e19_exact_expansion r N n hr hN hu hn]
    unfold chapter7Entry1Approx
    ring
  have hzero : Tendsto
      (fun n : ℕ => (ch8e19Constant N r - riemannZeta (-r)) -
        ch8e19RemainderFactor N r * ch8e19Tail N r n) atTop (𝓝 0) :=
    hdiff.congr' heq
  have hconst : Tendsto
      (fun n : ℕ => (ch8e19Constant N r - riemannZeta (-r)) -
        ch8e19RemainderFactor N r * ch8e19Tail N r n)
      atTop (𝓝 (ch8e19Constant N r - riemannZeta (-r))) := by
    simpa using tendsto_const_nhds.sub hrem
  have := tendsto_nhds_unique hconst hzero
  linear_combination this

private theorem ch8e19_natCpow_eq_exp (k : ℕ) (hk : 0 < k) :
    chapter7NatCpow k =
      fun s : ℂ => Complex.exp (((Real.log (k : ℝ) : ℝ) : ℂ) * s) := by
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  funext s
  unfold chapter7NatCpow
  calc
    Complex.cpow (k : ℂ) s = Complex.exp (Complex.log (k : ℂ) * s) :=
      Complex.cpow_def_of_ne_zero hkC s
    _ = Complex.exp (((Real.log (k : ℝ) : ℝ) : ℂ) * s) := by
      rw [show (k : ℂ) = ((k : ℝ) : ℂ) by norm_cast]
      rw [← Complex.ofReal_log (by positivity : (0 : ℝ) ≤ k)]

private theorem ch8e19_iteratedDeriv_natCpow (m k : ℕ) (hk : 0 < k) :
    iteratedDeriv m (chapter7NatCpow k) 0 = ((Real.log (k : ℝ) : ℝ) : ℂ) ^ m := by
  rw [ch8e19_natCpow_eq_exp k hk, iteratedDeriv_cexp_const_mul]
  simp

private theorem ch8e19_iteratedDeriv_powerSum (m x : ℕ) :
    iteratedDeriv m (fun r : ℂ => chapter7PowerSum r x) 0 =
      (chapter8LogPowerSum m x : ℂ) := by
  have hfun : (fun r : ℂ => chapter7PowerSum r x) =
      ∑ k ∈ Finset.Icc 1 x, chapter7NatCpow k := by
    funext r
    simp [chapter7PowerSum]
  rw [hfun, iteratedDeriv_sum]
  · unfold chapter8LogPowerSum
    push_cast
    apply Finset.sum_congr rfl
    intro k hk
    rw [ch8e19_iteratedDeriv_natCpow m k (by
      have := (Finset.mem_Icc.mp hk).1
      omega)]
    norm_cast
  · intro k hk
    rw [ch8e19_natCpow_eq_exp k (by
      have := (Finset.mem_Icc.mp hk).1
      omega)]
    fun_prop

private noncomputable def ch8e19LogPrimitive : ℕ → ℝ → ℝ
  | 0 => fun x => x
  | m + 1 => fun x => x * Real.log x ^ (m + 1) - (m + 1) * ch8e19LogPrimitive m x

private theorem ch8e19LogPrimitive_one (m : ℕ) :
    ch8e19LogPrimitive m 1 = (-1 : ℝ) ^ m * m.factorial := by
  induction m with
  | zero => simp [ch8e19LogPrimitive]
  | succ m ih =>
      simp only [ch8e19LogPrimitive, Real.log_one, zero_pow (Nat.succ_ne_zero m), one_mul,
        zero_sub, ih, Nat.factorial_succ, pow_succ]
      push_cast
      ring

private theorem ch8e19LogPrimitive_hasDerivAt (m : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (ch8e19LogPrimitive m) (Real.log x ^ m) x := by
  induction m with
  | zero =>
      change HasDerivAt (fun y : ℝ ↦ y) 1 x
      exact hasDerivAt_id x
  | succ m ih =>
      have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
      have hmul := (hasDerivAt_id x).mul (hlog.pow (m + 1))
      have hsub := hmul.sub (ih.const_mul (m + 1 : ℝ))
      convert hsub using 1
      · funext y
        rfl
      · simp only [id_eq, Pi.pow_apply, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
        field_simp [hx.ne']
        ring

private theorem ch8e19_integral_log_pow (m : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in 1..x, Real.log t ^ m =
      ch8e19LogPrimitive m x - (-1 : ℝ) ^ m * m.factorial := by
  have hderiv : ∀ t ∈ Set.uIcc (1 : ℝ) x,
      HasDerivAt (ch8e19LogPrimitive m) (Real.log t ^ m) t := by
    intro t ht
    have ht_one : 1 ≤ t := by
      rw [Set.uIcc_of_le hx] at ht
      exact ht.1
    exact ch8e19LogPrimitive_hasDerivAt m (zero_lt_one.trans_le ht_one)
  have hcont : ContinuousOn (fun t : ℝ ↦ Real.log t ^ m) (Set.uIcc 1 x) := by
    intro t ht
    have ht_one : 1 ≤ t := by
      rw [Set.uIcc_of_le hx] at ht
      exact ht.1
    exact ((Real.continuousAt_log (zero_lt_one.trans_le ht_one).ne').pow m).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  exact congrArg (ch8e19LogPrimitive m x - ·) (ch8e19LogPrimitive_one m)

private theorem ch8e19_iteratedDeriv_add_one (i : ℕ) :
    iteratedDeriv i (fun r : ℂ ↦ r + 1) 0 =
      if i = 0 then 1 else if i = 1 then 1 else 0 := by
  rw [show (fun r : ℂ ↦ r + 1) = fun r ↦ 1 + r by funext r; ring]
  by_cases hi : i = 0
  · subst i
    simp
  · rw [iteratedDeriv_const_add (Nat.pos_of_ne_zero hi)]
    change iteratedDeriv i id 0 = _
    simpa [hi] using (iteratedDeriv_id (n := i) (x := (0 : ℂ)))

private theorem ch8e19_iteratedDeriv_add_one_mul (m : ℕ) (f : ℂ → ℂ)
    (hf : ContDiffAt ℂ (m + 1) f 0) :
    iteratedDeriv (m + 1) (fun r ↦ (r + 1) * f r) 0 =
      iteratedDeriv (m + 1) f 0 + (m + 1) * iteratedDeriv m f 0 := by
  rw [show (fun r ↦ (r + 1) * f r) = (fun r ↦ r + 1) * f by rfl,
    iteratedDeriv_mul (by fun_prop) hf]
  simp only [ch8e19_iteratedDeriv_add_one]
  have hsplit : ∀ i : ℕ,
      (((m + 1).choose i : ℂ) * (if i = 0 then 1 else if i = 1 then 1 else 0) *
        iteratedDeriv (m + 1 - i) f 0) =
      (if i = 0 then ((m + 1).choose i : ℂ) * iteratedDeriv (m + 1 - i) f 0 else 0) +
        (if i = 1 then ((m + 1).choose i : ℂ) * iteratedDeriv (m + 1 - i) f 0 else 0) := by
    intro i
    by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;> simp [hi0, hi1]
  calc
    _ = ∑ i ∈ Finset.range (m + 1 + 1),
        ((if i = 0 then ((m + 1).choose i : ℂ) * iteratedDeriv (m + 1 - i) f 0 else 0) +
          (if i = 1 then ((m + 1).choose i : ℂ) * iteratedDeriv (m + 1 - i) f 0 else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hsplit i
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
      simp

private theorem ch8e19_iteratedDeriv_natCpow_apply (m k : ℕ) (hk : 0 < k) (s : ℂ) :
    iteratedDeriv m (chapter7NatCpow k) s =
      ((Real.log (k : ℝ) : ℝ) : ℂ) ^ m * chapter7NatCpow k s := by
  rw [ch8e19_natCpow_eq_exp k hk, iteratedDeriv_cexp_const_mul]

private theorem ch8e19_mainTerm_contDiffAt (m x : ℕ) (hx : 0 < x) :
    ContDiffAt ℂ m (fun r : ℂ ↦ chapter7NatCpow x (r + 1) / (r + 1)) 0 := by
  rw [ch8e19_natCpow_eq_exp x hx]
  apply ContDiffAt.div
  · fun_prop
  · fun_prop
  · norm_num

private theorem ch8e19_iteratedDeriv_mainTerm (m x : ℕ) (hx : 0 < x) :
    iteratedDeriv m (fun r : ℂ ↦ chapter7NatCpow x (r + 1) / (r + 1)) 0 =
      (ch8e19LogPrimitive m x : ℂ) := by
  induction m with
  | zero =>
      simp [ch8e19LogPrimitive, chapter7NatCpow]
  | succ m ih =>
      let f : ℂ → ℂ := fun r ↦ chapter7NatCpow x (r + 1) / (r + 1)
      change iteratedDeriv m f 0 = (ch8e19LogPrimitive m x : ℂ) at ih
      have hcancel : (fun r : ℂ ↦ (r + 1) * f r) =ᶠ[nhds 0]
          (fun r ↦ chapter7NatCpow x (r + 1)) := by
        filter_upwards [eventually_ne_nhds (by norm_num : (0 : ℂ) ≠ -1)] with r hr
        have hr' : r + 1 ≠ 0 := by
          intro h
          apply hr
          linear_combination h
        dsimp [f]
        field_simp
      have hderiv := hcancel.iteratedDeriv_eq (m + 1)
      rw [ch8e19_iteratedDeriv_add_one_mul m f
        (ch8e19_mainTerm_contDiffAt (m + 1) x hx)] at hderiv
      rw [iteratedDeriv_comp_add_const] at hderiv
      simp only [zero_add] at hderiv
      rw [ch8e19_iteratedDeriv_natCpow_apply (m + 1) x hx 1] at hderiv
      simp only [natCast_log, chapter7NatCpow, cpow_eq_pow, cpow_one] at hderiv
      change iteratedDeriv (m + 1) f 0 = (ch8e19LogPrimitive (m + 1) x : ℂ)
      rw [ih] at hderiv
      rw [ch8e19LogPrimitive]
      push_cast
      linear_combination hderiv

private noncomputable def ch8e19Error (N x : ℕ) (r : ℂ) : ℂ :=
  chapter7PowerSum r x - riemannZeta (-r) -
    chapter7NatCpow x (r + 1) / (r + 1) - chapter7NatCpow x r / 2 -
      ∑ j ∈ Finset.range N, chapter7Entry1Term r x j

private theorem ch8e19_natCpow_differentiable (k : ℕ) (hk : 0 < k) :
    Differentiable ℂ (chapter7NatCpow k) := by
  rw [ch8e19_natCpow_eq_exp k hk]
  fun_prop

private theorem ch8e19_powerSum_differentiable (x : ℕ) :
    Differentiable ℂ (fun r ↦ chapter7PowerSum r x) := by
  unfold chapter7PowerSum
  apply Differentiable.fun_sum
  intro k hk
  exact ch8e19_natCpow_differentiable k (by
    have := (Finset.mem_Icc.mp hk).1
    omega)

private theorem ch8e19_falling_differentiable (q : ℕ) :
    Differentiable ℂ (fun r ↦ chapter7FallingGammaRatio r q) := by
  unfold chapter7FallingGammaRatio
  fun_prop

private theorem ch8e19_entry1Term_differentiable (x j : ℕ) (hx : 0 < x) :
    Differentiable ℂ (fun r ↦ chapter7Entry1Term r x j) := by
  unfold chapter7Entry1Term
  dsimp only
  apply Differentiable.mul
  · exact (differentiable_const _).mul (ch8e19_falling_differentiable _)
  · exact (ch8e19_natCpow_differentiable x hx).comp (by fun_prop)

private theorem ch8e19Error_diffContOnCl (N x : ℕ) (hx : 0 < x) :
    DiffContOnCl ℂ (ch8e19Error N x) (Metric.ball 0 (1 / 2 : ℝ)) := by
  apply DifferentiableOn.diffContOnCl_ball _ Set.Subset.rfl
  intro r hr
  have hrnorm : ‖r‖ ≤ (1 / 2 : ℝ) := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hr
  have hrneg : -r ≠ 1 := by
    intro h
    have : r = -1 := by simpa using congrArg Neg.neg h
    subst r
    norm_num at hrnorm
  have hrden : r + 1 ≠ 0 := by
    intro h
    have : r = -1 := by
      calc
        r = (r + 1) - 1 := by ring
        _ = -1 := by rw [h]; ring
    subst r
    norm_num at hrnorm
  unfold ch8e19Error
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.sub
  · apply DifferentiableAt.sub
    · apply DifferentiableAt.sub
      · apply DifferentiableAt.sub
        · exact ch8e19_powerSum_differentiable x r
        · exact (differentiableAt_riemannZeta hrneg).comp r (by fun_prop)
      · exact ((ch8e19_natCpow_differentiable x hx).differentiableAt.comp r
          (by fun_prop)).div
          (by fun_prop) hrden
    · exact ((ch8e19_natCpow_differentiable x hx) r).div_const 2
  · apply DifferentiableAt.fun_sum
    intro j hj
    exact ch8e19_entry1Term_differentiable x j hx r

private theorem ch8e19Error_eq_tail (N x : ℕ) (hN : 0 < N) (hx : 1 < x)
    {r : ℂ} (hr : ‖r‖ ≤ (1 / 2 : ℝ)) :
    ch8e19Error N x r = -ch8e19RemainderFactor N r * ch8e19Tail N r x := by
  have hrne : r ≠ -1 := by
    intro h
    subst r
    norm_num at hr
  have hre : r.re < 2 * N := by
    have := (Complex.re_le_norm r).trans hr
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  unfold ch8e19Error
  rw [ch8e19_exact_expansion r N x hrne hN hre hx,
    ch8e19Constant_eq_zeta N hN r hrne hre]
  ring

private noncomputable def ch8e19EntryCoeff (j : ℕ) (r : ℂ) : ℂ :=
  let k := j + 1
  (((bernoulli (2 * k) : ℚ) : ℂ) / ((2 * k).factorial : ℂ)) *
    chapter7FallingGammaRatio r (2 * k - 1)

private theorem ch8e19_entry1Term_eq_coeff (r : ℂ) (x j : ℕ) :
    chapter7Entry1Term r x j = ch8e19EntryCoeff j r *
      chapter7NatCpow x (r - (2 * (j + 1) : ℕ) + 1) := by
  rfl

private theorem ch8e19EntryCoeff_norm_le (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Metric.sphere (0 : ℂ) (1 / 2 : ℝ),
      ‖ch8e19EntryCoeff j r‖ ≤ C := by
  have hc : Continuous (ch8e19EntryCoeff j) := by
    unfold ch8e19EntryCoeff chapter7FallingGammaRatio
    fun_prop
  have hcompact : IsCompact
      (ch8e19EntryCoeff j '' Metric.sphere (0 : ℂ) (1 / 2 : ℝ)) :=
    (isCompact_sphere (0 : ℂ) (1 / 2 : ℝ)).image_of_continuousOn hc.continuousOn
  obtain ⟨C, hC⟩ := hcompact.isBounded.exists_norm_le
  have hsphere : ((1 / 2 : ℝ) : ℂ) ∈ Metric.sphere (0 : ℂ) (1 / 2 : ℝ) := by
    simp
  have hC0 : 0 ≤ C :=
    (norm_nonneg (ch8e19EntryCoeff j (1 / 2 : ℝ))).trans
      (hC _ ⟨_, hsphere, rfl⟩)
  exact ⟨C, hC0, fun r hr ↦ hC _ ⟨r, hr, rfl⟩⟩

private theorem ch8e19_entry1Term_norm_le_uniform (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Metric.sphere (0 : ℂ) (1 / 2 : ℝ), ∀ x : ℕ,
      1 ≤ x → ‖chapter7Entry1Term r x j‖ ≤
        C * Real.rpow (x : ℝ) (-2 * (j : ℝ) - 1 / 2) := by
  obtain ⟨C, hC0, hC⟩ := ch8e19EntryCoeff_norm_le j
  refine ⟨C, hC0, ?_⟩
  intro r hr x hx
  have hxpos : 0 < (x : ℝ) := by positivity
  have hxone : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hrnorm : ‖r‖ = (1 / 2 : ℝ) := by
    simpa [Metric.mem_sphere] using hr
  have hre : r.re ≤ (1 / 2 : ℝ) := (Complex.re_le_norm r).trans hrnorm.le
  rw [ch8e19_entry1Term_eq_coeff, norm_mul, chapter7NatCpow]
  rw [show (x : ℂ) = ((x : ℝ) : ℂ) by norm_cast]
  have hpow :
      ‖Complex.cpow ((x : ℝ) : ℂ) (r - (2 * (j + 1) : ℕ) + 1)‖ =
        Real.rpow (x : ℝ) (r - (2 * (j + 1) : ℕ) + 1).re :=
    Complex.norm_cpow_eq_rpow_re_of_pos hxpos _
  rw [hpow]
  have hexp : (r - (2 * (j + 1) : ℕ) + 1).re ≤ -2 * (j : ℝ) - 1 / 2 := by
    norm_num [Nat.cast_add, Nat.cast_mul]
    linarith
  exact mul_le_mul (hC r hr) (Real.rpow_le_rpow_of_exponent_le hxone hexp)
    (Real.rpow_nonneg hxpos.le _) hC0

private theorem ch8e19RemainderFactor_norm_le (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Metric.sphere (0 : ℂ) (1 / 2 : ℝ),
      ‖ch8e19RemainderFactor N r‖ ≤ C := by
  have hc : Continuous (ch8e19RemainderFactor N) := by
    unfold ch8e19RemainderFactor chapter7FallingGammaRatio
    fun_prop
  have hcompact : IsCompact
      (ch8e19RemainderFactor N '' Metric.sphere (0 : ℂ) (1 / 2 : ℝ)) :=
    (isCompact_sphere (0 : ℂ) (1 / 2 : ℝ)).image_of_continuousOn hc.continuousOn
  obtain ⟨C, hC⟩ := hcompact.isBounded.exists_norm_le
  have hsphere : ((1 / 2 : ℝ) : ℂ) ∈ Metric.sphere (0 : ℂ) (1 / 2 : ℝ) := by
    simp
  have hC0 : 0 ≤ C :=
    (norm_nonneg (ch8e19RemainderFactor N (1 / 2 : ℝ))).trans
      (hC _ ⟨_, hsphere, rfl⟩)
  exact ⟨C, hC0, fun r hr ↦ hC _ ⟨r, hr, rfl⟩⟩

private theorem ch8e19Error_zero_eq (x : ℕ) (r : ℂ) :
    ch8e19Error 0 x r = chapter7Entry1Term r x 0 + ch8e19Error 1 x r := by
  simp [ch8e19Error]

private theorem ch8e19Error_zero_norm_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Metric.sphere (0 : ℂ) (1 / 2 : ℝ), ∀ x : ℕ,
      1 < x → ‖ch8e19Error 0 x r‖ ≤ C * Real.rpow (x : ℝ) (-1 / 2) := by
  obtain ⟨CT, hCT0, hterm⟩ := ch8e19_entry1Term_norm_le_uniform 0
  obtain ⟨CR, hCR0, hfactor⟩ := ch8e19RemainderFactor_norm_le 1
  obtain ⟨D, hD0, htail⟩ := ch8e19Tail_norm_le_uniform 1 (by omega)
  refine ⟨CT + CR * D, add_nonneg hCT0 (mul_nonneg hCR0 hD0), ?_⟩
  intro r hr x hx
  have hxone : (1 : ℝ) ≤ x := by exact_mod_cast (le_of_lt hx)
  have hxnat : 1 ≤ x := le_of_lt hx
  have hrnorm : ‖r‖ ≤ (1 / 2 : ℝ) := by
    exact (le_of_eq (by simpa [Metric.mem_sphere] using hr))
  have hpow : Real.rpow (x : ℝ) (-2 * (1 : ℝ) + 1 / 2) ≤
      Real.rpow (x : ℝ) (-1 / 2) := by
    apply Real.rpow_le_rpow_of_exponent_le hxone
    norm_num
  have herr : ‖ch8e19Error 1 x r‖ ≤
      CR * D * Real.rpow (x : ℝ) (-1 / 2) := by
    rw [ch8e19Error_eq_tail 1 x (by omega) hx hrnorm, norm_mul, norm_neg]
    have htail' : ‖ch8e19Tail 1 r x‖ ≤
        D * Real.rpow (x : ℝ) (-2 * (1 : ℝ) + 1 / 2) := by
      convert htail r hr x hxnat using 1
      all_goals norm_num
    calc
      ‖ch8e19RemainderFactor 1 r‖ * ‖ch8e19Tail 1 r x‖ ≤
          CR * (D * Real.rpow (x : ℝ) (-2 * (1 : ℝ) + 1 / 2)) := by
        exact mul_le_mul (hfactor r hr) htail' (norm_nonneg _) hCR0
      _ ≤ CR * (D * Real.rpow (x : ℝ) (-1 / 2)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hD0) hCR0
      _ = CR * D * Real.rpow (x : ℝ) (-1 / 2) := by ring
  rw [ch8e19Error_zero_eq]
  calc
    ‖chapter7Entry1Term r x 0 + ch8e19Error 1 x r‖ ≤
        ‖chapter7Entry1Term r x 0‖ + ‖ch8e19Error 1 x r‖ := norm_add_le _ _
    _ ≤ CT * Real.rpow (x : ℝ) (-1 / 2) +
        CR * D * Real.rpow (x : ℝ) (-1 / 2) :=
      add_le_add (by
        convert hterm r hr x hxnat using 1
        all_goals ring_nf) herr
    _ = (CT + CR * D) * Real.rpow (x : ℝ) (-1 / 2) := by ring

private theorem ch8e19_iteratedDeriv_error_zero_isBigO (m : ℕ) :
    IsBigO atTop (fun x : ℕ ↦ iteratedDeriv m (ch8e19Error 0 x) 0)
      (fun x : ℕ ↦ Real.rpow (x : ℝ) (-1 / 2)) := by
  obtain ⟨C, hC0, hC⟩ := ch8e19Error_zero_norm_le
  refine isBigO_iff.mpr ⟨(m.factorial : ℝ) * C / (1 / 2 : ℝ) ^ m, ?_⟩
  filter_upwards [eventually_gt_atTop 1] with x hx
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    m (by norm_num : (0 : ℝ) < 1 / 2)
    (ch8e19Error_diffContOnCl 0 x (by omega))
    (fun r hr ↦ hC r hr x hx)
  calc
    ‖iteratedDeriv m (ch8e19Error 0 x) 0‖ ≤
        (m.factorial : ℝ) * (C * Real.rpow (x : ℝ) (-1 / 2)) /
          (1 / 2 : ℝ) ^ m := hcauchy
    _ = ((m.factorial : ℝ) * C / (1 / 2 : ℝ) ^ m) *
        ‖Real.rpow (x : ℝ) (-1 / 2)‖ := by
      have hnorm : ‖Real.rpow (x : ℝ) (-1 / 2)‖ =
          Real.rpow (x : ℝ) (-1 / 2) := by
        exact Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)
      rw [hnorm]
      ring

private theorem ch8e19_iteratedDeriv_error_zero_tendsto (m : ℕ) :
    Tendsto (fun x : ℕ ↦ iteratedDeriv m (ch8e19Error 0 x) 0) atTop (nhds 0) := by
  have hpow : Tendsto (fun x : ℕ ↦ Real.rpow (x : ℝ) (-1 / 2)) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop
    convert h using 1
    funext x
    congr 1
    ring
  exact (ch8e19_iteratedDeriv_error_zero_isBigO m).trans_tendsto hpow

private theorem ch8e19_zeta_neg_contDiffAt (m : ℕ) :
    ContDiffAt ℂ m (fun r : ℂ ↦ riemannZeta (-r)) 0 := by
  have hz : AnalyticAt ℂ riemannZeta 0 := analyticOn_riemannZeta 0 (by norm_num)
  have hz' : AnalyticAt ℂ riemannZeta (-(0 : ℂ)) := by simpa using hz
  have hn : AnalyticAt ℂ (fun r : ℂ ↦ -r) 0 := by fun_prop
  simpa [Function.comp_def] using
    (AnalyticAt.comp (f := fun r : ℂ ↦ -r) hz' hn).contDiffAt (n := (m : WithTop ℕ∞))

private theorem ch8e19_iteratedDeriv_error_zero (m x : ℕ) (hx : 0 < x) :
    iteratedDeriv m (ch8e19Error 0 x) 0 =
      (chapter8LogPowerSum m x : ℂ) -
        (-1 : ℂ) ^ m * iteratedDeriv m riemannZeta 0 -
        (ch8e19LogPrimitive m x : ℂ) -
        ((Real.log (x : ℝ) : ℝ) : ℂ) ^ m / 2 := by
  let p : ℂ → ℂ := fun r ↦ chapter7PowerSum r x
  let z : ℂ → ℂ := fun r ↦ riemannZeta (-r)
  let a : ℂ → ℂ := fun r ↦ chapter7NatCpow x (r + 1) / (r + 1)
  let b : ℂ → ℂ := fun r ↦ chapter7NatCpow x r / 2
  have hp : ContDiffAt ℂ m p 0 :=
    (ch8e19_powerSum_differentiable x).contDiff.contDiffAt
  have hz : ContDiffAt ℂ m z 0 := ch8e19_zeta_neg_contDiffAt m
  have ha : ContDiffAt ℂ m a 0 := ch8e19_mainTerm_contDiffAt m x hx
  have hb : ContDiffAt ℂ m b 0 :=
    ((ch8e19_natCpow_differentiable x hx).contDiff.div_const 2).contDiffAt
  have hpz : ContDiffAt ℂ m (p - z) 0 := hp.sub hz
  have hpza : ContDiffAt ℂ m (p - z - a) 0 := hpz.sub ha
  have herrfun : ch8e19Error 0 x = p - z - a - b := by
    funext r
    simp [ch8e19Error, p, z, a, b]
  rw [herrfun]
  rw [iteratedDeriv_sub hpza hb, iteratedDeriv_sub hpz ha, iteratedDeriv_sub hp hz]
  change iteratedDeriv m (fun r : ℂ ↦ chapter7PowerSum r x) 0 -
      iteratedDeriv m (fun r : ℂ ↦ riemannZeta (-r)) 0 -
      iteratedDeriv m (fun r : ℂ ↦ chapter7NatCpow x (r + 1) / (r + 1)) 0 -
      iteratedDeriv m (fun r : ℂ ↦ chapter7NatCpow x r / 2) 0 = _
  rw [ch8e19_iteratedDeriv_powerSum, iteratedDeriv_comp_neg,
    ch8e19_iteratedDeriv_mainTerm m x hx, iteratedDeriv_div_const,
    ch8e19_iteratedDeriv_natCpow m x hx]
  simp [smul_eq_mul]

private theorem ch8e19_constantApprox_sub_constant (m x : ℕ) (hx : 1 < x) :
    chapter8LogPowerConstantApprox m x - chapter8LogPowerConstant m =
      (iteratedDeriv m (ch8e19Error 0 x) 0).re := by
  rw [ch8e19_iteratedDeriv_error_zero m x (by omega)]
  unfold chapter8LogPowerConstantApprox chapter8LogPowerConstant
  rw [ch8e19_iteratedDeriv_re m 0 (by norm_num),
    ch8e19_integral_log_pow m (by exact_mod_cast (le_of_lt hx))]
  push_cast
  have hnegC : (-1 : ℂ) ^ m = (((-1 : ℝ) ^ m : ℝ) : ℂ) := by norm_cast
  have hnegRe : ((-1 : ℂ) ^ m).re = (-1 : ℝ) ^ m := by
    calc
      ((-1 : ℂ) ^ m).re = (((( -1 : ℝ) ^ m : ℝ) : ℂ)).re := congrArg Complex.re hnegC
      _ = _ := Complex.ofReal_re _
  have hnegIm : ((-1 : ℂ) ^ m).im = 0 := by
    calc
      ((-1 : ℂ) ^ m).im = (((( -1 : ℝ) ^ m : ℝ) : ℂ)).im := congrArg Complex.im hnegC
      _ = _ := Complex.ofReal_im _
  have hlogRe : (Complex.log (x : ℂ) ^ m).re = Real.log (x : ℝ) ^ m := by
    rw [show (x : ℂ) = ((x : ℝ) : ℂ) by norm_cast,
      ← Complex.ofReal_log (by positivity : (0 : ℝ) ≤ x)]
    norm_cast
  simp [Complex.mul_re, hnegRe, hnegIm, hlogRe]
  ring_nf

private theorem ch8e19_constantApprox_tendsto (m : ℕ) :
    Tendsto (chapter8LogPowerConstantApprox m) atTop
      (nhds (chapter8LogPowerConstant m)) := by
  have herr : Tendsto
      (fun x : ℕ ↦ (iteratedDeriv m (ch8e19Error 0 x) 0).re) atTop (nhds 0) := by
    have h := (Complex.continuous_re.tendsto 0).comp
      (ch8e19_iteratedDeriv_error_zero_tendsto m)
    exact h.congr' (Eventually.of_forall fun _ ↦ rfl)
  have hdiff : Tendsto
      (fun x : ℕ ↦ chapter8LogPowerConstantApprox m x - chapter8LogPowerConstant m)
      atTop (nhds 0) := by
    apply herr.congr'
    filter_upwards [eventually_gt_atTop 1] with x hx
    exact (ch8e19_constantApprox_sub_constant m x hx).symm
  have h : Tendsto
      (fun x : ℕ ↦ chapter8LogPowerConstant m +
        (chapter8LogPowerConstantApprox m x - chapter8LogPowerConstant m))
      atTop (nhds (chapter8LogPowerConstant m + 0)) := tendsto_const_nhds.add hdiff
  simpa only [add_zero] using h.congr' (Eventually.of_forall fun _ ↦ by ring)

private theorem ch8e19_iteratedDeriv_sub_nat (i q : ℕ) :
    iteratedDeriv i (fun r : ℂ ↦ r - q) 0 =
      if i = 0 then -(q : ℂ) else if i = 1 then 1 else 0 := by
  rw [show (fun r : ℂ ↦ r - q) = fun r ↦ -(q : ℂ) + r by funext r; ring]
  by_cases hi : i = 0
  · subst i
    simp
  · rw [iteratedDeriv_const_add (Nat.pos_of_ne_zero hi)]
    change iteratedDeriv i id 0 = _
    simpa [hi] using (iteratedDeriv_id (n := i) (x := (0 : ℂ)))

private theorem ch8e19_iteratedDeriv_mul_sub_nat (m q : ℕ) (f : ℂ → ℂ)
    (hf : ContDiffAt ℂ (m + 1) f 0) :
    iteratedDeriv (m + 1) (fun r ↦ f r * (r - q)) 0 =
      -(q : ℂ) * iteratedDeriv (m + 1) f 0 +
        (m + 1) * iteratedDeriv m f 0 := by
  rw [show (fun r : ℂ ↦ f r * (r - q)) = f * (fun r : ℂ ↦ r - q) by rfl,
    iteratedDeriv_mul hf (by fun_prop)]
  simp only [ch8e19_iteratedDeriv_sub_nat]
  have hsplit : ∀ i ∈ Finset.range (m + 1 + 1),
      (((m + 1).choose i : ℂ) * iteratedDeriv i f 0 *
        (if m + 1 - i = 0 then -(q : ℂ) else if m + 1 - i = 1 then 1 else 0)) =
      (if i = m + 1 then -(q : ℂ) * iteratedDeriv (m + 1) f 0 else 0) +
        (if i = m then ((m + 1 : ℕ) : ℂ) * iteratedDeriv m f 0 else 0) := by
    intro i hi
    simp only [Finset.mem_range] at hi
    by_cases hi1 : i = m + 1
    · subst i
      simp
      ring
    by_cases hi0 : i = m
    · subst i
      simp [Nat.choose_succ_self_right]
    have hne0 : m + 1 - i ≠ 0 := by omega
    have hne1 : m + 1 - i ≠ 1 := by omega
    simp [hi1, hi0, hne0, hne1]
  calc
    _ = ∑ i ∈ Finset.range (m + 1 + 1),
        ((if i = m + 1 then -(q : ℂ) * iteratedDeriv (m + 1) f 0 else 0) +
          (if i = m then ((m + 1 : ℕ) : ℂ) * iteratedDeriv m f 0 else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hsplit i hi
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
      simp

private theorem ch8e19_falling_deriv_succ (m q : ℕ) :
    iteratedDeriv (m + 1) (fun r ↦ chapter7FallingGammaRatio r (q + 1)) 0 =
      -(q : ℂ) * iteratedDeriv (m + 1) (fun r ↦ chapter7FallingGammaRatio r q) 0 +
        (m + 1) * iteratedDeriv m (fun r ↦ chapter7FallingGammaRatio r q) 0 := by
  rw [show (fun r ↦ chapter7FallingGammaRatio r (q + 1)) =
      fun r ↦ chapter7FallingGammaRatio r q * (r - q) by
    funext r
    exact ch8e19Falling_succ r q]
  exact ch8e19_iteratedDeriv_mul_sub_nat m q _
    ((ch8e19_falling_differentiable q).contDiff.contDiffAt)

private theorem ch8e19_falling_deriv_eq_zero_of_lt (q n : ℕ) (hqn : q < n) :
    iteratedDeriv n (fun r ↦ chapter7FallingGammaRatio r q) 0 = 0 := by
  induction q generalizing n with
  | zero =>
      have hn : 0 < n := hqn
      simp [chapter7FallingGammaRatio, iteratedDeriv_const, hn.ne']
  | succ q ih =>
      obtain _ | m := n
      · omega
      rw [ch8e19_falling_deriv_succ m q,
        ih (m + 1) (by omega), ih m (by omega)]
      ring

private theorem ch8e19_falling_deriv_diagonal (n : ℕ) :
    iteratedDeriv n (fun r ↦ chapter7FallingGammaRatio r n) 0 =
      (n.factorial : ℂ) := by
  induction n with
  | zero => simp [chapter7FallingGammaRatio]
  | succ n ih =>
      rw [ch8e19_falling_deriv_succ n n,
        ch8e19_falling_deriv_eq_zero_of_lt n (n + 1) (by omega), ih]
      rw [Nat.factorial_succ]
      push_cast
      ring

private theorem ch8e19_falling_deriv_next (n : ℕ) :
    iteratedDeriv n (fun r ↦ chapter7FallingGammaRatio r (n + 1)) 0 =
      -(n : ℂ) * (n + 1).factorial / 2 := by
  induction n with
  | zero => simp [chapter7FallingGammaRatio]
  | succ n ih =>
      rw [ch8e19_falling_deriv_succ n (n + 1),
        ch8e19_falling_deriv_diagonal (n + 1), ih]
      simp only [Nat.factorial_succ]
      push_cast
      ring_nf

private theorem ch8e19_falling_deriv_next_two (n : ℕ) :
    iteratedDeriv n (fun r ↦ chapter7FallingGammaRatio r (n + 2)) 0 =
      (n.factorial : ℂ) * n * (n + 1) * (n + 2) * (3 * n + 5) / 24 := by
  induction n with
  | zero => norm_num [chapter7FallingGammaRatio, Finset.prod_range_succ]
  | succ n ih =>
      rw [ch8e19_falling_deriv_succ n (n + 2),
        ch8e19_falling_deriv_next (n + 1), ih]
      simp only [Nat.factorial_succ]
      push_cast
      ring_nf

private theorem ch8e19_natCpow_neg_mul_add (x : ℕ) (hx : 0 < x) (r s : ℂ) :
    chapter7NatCpow x (-r) * chapter7NatCpow x (r + s) = chapter7NatCpow x s := by
  rw [ch8e19_natCpow_eq_exp x hx]
  rw [← Complex.exp_add]
  congr 1
  ring

private noncomputable def ch8e19ScaledError (N x : ℕ) (r : ℂ) : ℂ :=
  chapter7NatCpow x (-r) * ch8e19Error N x r

private noncomputable def ch8e19ScaledTerm (x j : ℕ) (r : ℂ) : ℂ :=
  chapter7NatCpow x (-r) * chapter7Entry1Term r x j

private noncomputable def ch8e19ScaledSum (x : ℕ) (r : ℂ) : ℂ :=
  chapter7NatCpow x (-r) * (chapter7PowerSum r x - riemannZeta (-r))

private theorem ch8e19ScaledTerm_eq (x j : ℕ) (hx : 0 < x) (r : ℂ) :
    ch8e19ScaledTerm x j r = ch8e19EntryCoeff j r *
      chapter7NatCpow x (-(2 * (j + 1) : ℕ) + 1) := by
  unfold ch8e19ScaledTerm
  rw [ch8e19_entry1Term_eq_coeff]
  have hcancel := ch8e19_natCpow_neg_mul_add x hx r
    (-((2 * (j + 1) : ℕ) : ℂ) + 1)
  rw [show r - ((2 * (j + 1) : ℕ) : ℂ) + 1 =
    r + (-((2 * (j + 1) : ℕ) : ℂ) + 1) by ring]
  calc
    chapter7NatCpow x (-r) *
        (ch8e19EntryCoeff j r *
          chapter7NatCpow x (r + (-((2 * (j + 1) : ℕ) : ℂ) + 1))) =
      ch8e19EntryCoeff j r * (chapter7NatCpow x (-r) *
        chapter7NatCpow x (r + (-((2 * (j + 1) : ℕ) : ℂ) + 1))) := by
      ring
    _ = _ := by rw [hcancel]

private theorem ch8e19ScaledSum_eq (N x : ℕ) (hx : 0 < x) (r : ℂ) :
    ch8e19ScaledSum x r = chapter7NatCpow x 1 / (r + 1) + 1 / 2 +
      ∑ j ∈ Finset.range N, ch8e19ScaledTerm x j r + ch8e19ScaledError N x r := by
  have herr : chapter7PowerSum r x - riemannZeta (-r) =
      chapter7NatCpow x (r + 1) / (r + 1) + chapter7NatCpow x r / 2 +
        ∑ j ∈ Finset.range N, chapter7Entry1Term r x j + ch8e19Error N x r := by
    unfold ch8e19Error
    ring
  unfold ch8e19ScaledSum ch8e19ScaledError ch8e19ScaledTerm
  rw [herr]
  rw [mul_add, mul_add, mul_add, Finset.mul_sum]
  have h1 := ch8e19_natCpow_neg_mul_add x hx r 1
  have h0 := ch8e19_natCpow_neg_mul_add x hx r 0
  rw [show chapter7NatCpow x (-r) * (chapter7NatCpow x (r + 1) / (r + 1)) =
      (chapter7NatCpow x (-r) * chapter7NatCpow x (r + 1)) / (r + 1) by ring,
    show chapter7NatCpow x (-r) * (chapter7NatCpow x r / 2) =
      (chapter7NatCpow x (-r) * chapter7NatCpow x (r + 0)) / 2 by ring_nf,
    h1, h0]
  simp [chapter7NatCpow]

private theorem ch8e19_iteratedDeriv_natCpow_neg (m x : ℕ) (hx : 0 < x) :
    iteratedDeriv m (fun r : ℂ ↦ chapter7NatCpow x (-r)) 0 =
      (((-1 : ℝ) ^ m * Real.log (x : ℝ) ^ m : ℝ) : ℂ) := by
  rw [iteratedDeriv_comp_neg]
  simp only [neg_zero]
  rw [ch8e19_iteratedDeriv_natCpow m x hx]
  simp [smul_eq_mul]

private theorem ch8e19_power_sub_zeta_contDiffAt (m x : ℕ) :
    ContDiffAt ℂ m (fun r : ℂ ↦ chapter7PowerSum r x - riemannZeta (-r)) 0 :=
  (ch8e19_powerSum_differentiable x).contDiff.contDiffAt.sub
    (ch8e19_zeta_neg_contDiffAt m)

private theorem ch8e19_power_sub_zeta_deriv_re (m x : ℕ) :
    (iteratedDeriv m (fun r : ℂ ↦ chapter7PowerSum r x - riemannZeta (-r)) 0).re =
      chapter8Psi m x := by
  change (iteratedDeriv m
    ((fun r : ℂ ↦ chapter7PowerSum r x) - (fun r : ℂ ↦ riemannZeta (-r))) 0).re = _
  rw [iteratedDeriv_sub
    ((ch8e19_powerSum_differentiable x).contDiff.contDiffAt)
    (ch8e19_zeta_neg_contDiffAt m), ch8e19_iteratedDeriv_powerSum,
    iteratedDeriv_comp_neg]
  have hnegC : (-1 : ℂ) ^ m = (((-1 : ℝ) ^ m : ℝ) : ℂ) := by norm_cast
  rw [hnegC]
  simp only [neg_zero, smul_eq_mul, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  unfold chapter8Psi chapter8LogPowerConstant
  rw [ch8e19_iteratedDeriv_re m 0 (by norm_num)]
  norm_num

private theorem ch8e19_combination_eq_scaled_deriv (n x : ℕ) (hx : 0 < x) :
    chapter8Entry19Combination n x =
      (-1 : ℝ) ^ n * (iteratedDeriv n (ch8e19ScaledSum x) 0).re := by
  have hf : ContDiffAt ℂ n (fun r : ℂ ↦ chapter7NatCpow x (-r)) 0 :=
    ((ch8e19_natCpow_differentiable x hx).comp (by fun_prop)).contDiff.contDiffAt
  have hg := ch8e19_power_sub_zeta_contDiffAt n x
  unfold ch8e19ScaledSum chapter8Entry19Combination
  rw [show (fun r : ℂ ↦ chapter7NatCpow x (-r) *
      (chapter7PowerSum r x - riemannZeta (-r))) =
      (fun r : ℂ ↦ chapter7NatCpow x (-r)) *
        (fun r : ℂ ↦ chapter7PowerSum r x - riemannZeta (-r)) by rfl,
    iteratedDeriv_mul hf hg]
  change (∑ k ∈ Finset.range (n + 1),
      (-1 : ℝ) ^ (n + k) * (n.choose k : ℝ) * Real.log (x : ℝ) ^ k *
        chapter8Psi (n - k) x) =
    (-1 : ℝ) ^ n * Complex.reCLM
      (∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) *
        iteratedDeriv k (fun r : ℂ ↦ chapter7NatCpow x (-r)) 0 *
        iteratedDeriv (n - k)
          (fun r : ℂ ↦ chapter7PowerSum r x - riemannZeta (-r)) 0)
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [ch8e19_iteratedDeriv_natCpow_neg k x hx]
  change _ = (-1 : ℝ) ^ n *
    (((n.choose k : ℂ) * (((-1 : ℝ) ^ k * Real.log (x : ℝ) ^ k : ℝ) : ℂ) *
      iteratedDeriv (n - k)
        (fun r : ℂ ↦ chapter7PowerSum r x - riemannZeta (-r)) 0).re)
  have hcoeff : (n.choose k : ℂ) *
      (((-1 : ℝ) ^ k * Real.log (x : ℝ) ^ k : ℝ) : ℂ) =
      (((n.choose k : ℝ) * ((-1 : ℝ) ^ k * Real.log (x : ℝ) ^ k) : ℝ) : ℂ) := by
    norm_cast
  rw [hcoeff]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul]
  rw [ch8e19_power_sub_zeta_deriv_re]
  rw [pow_add]
  ring

private theorem ch8e19ScaledError_diffContOnCl (N x : ℕ) (hx : 0 < x) :
    DiffContOnCl ℂ (ch8e19ScaledError N x) (Metric.ball 0 (1 / 2 : ℝ)) := by
  have hnat : Differentiable ℂ (fun r : ℂ ↦ chapter7NatCpow x (-r)) :=
    (ch8e19_natCpow_differentiable x hx).comp (by fun_prop)
  unfold ch8e19ScaledError
  simpa only [smul_eq_mul] using
    hnat.diffContOnCl.smul (ch8e19Error_diffContOnCl N x hx)

private theorem ch8e19ScaledError_norm_le (N : ℕ) (hN : 0 < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Metric.sphere (0 : ℂ) (1 / 2 : ℝ), ∀ x : ℕ,
      1 < x → ‖ch8e19ScaledError N x r‖ ≤
        C * Real.rpow (x : ℝ) (-2 * (N : ℝ) + 1) := by
  obtain ⟨CR, hCR0, hfactor⟩ := ch8e19RemainderFactor_norm_le N
  obtain ⟨D, hD0, htail⟩ := ch8e19Tail_norm_le_uniform N hN
  refine ⟨CR * D, mul_nonneg hCR0 hD0, ?_⟩
  intro r hr x hx
  have hxnat : 1 ≤ x := le_of_lt hx
  have hxpos : 0 < (x : ℝ) := by positivity
  have hxone : (1 : ℝ) ≤ x := by exact_mod_cast hxnat
  have hrnorm : ‖r‖ = (1 / 2 : ℝ) := by
    simpa [Metric.mem_sphere] using hr
  have hre : (-r).re ≤ (1 / 2 : ℝ) := by
    calc
      (-r).re ≤ ‖-r‖ := Complex.re_le_norm (-r)
      _ = _ := by simpa using hrnorm
  have hnat : ‖chapter7NatCpow x (-r)‖ ≤ Real.rpow (x : ℝ) (1 / 2) := by
    unfold chapter7NatCpow
    rw [show (x : ℂ) = ((x : ℝ) : ℂ) by norm_cast]
    have hcpow : ‖Complex.cpow ((x : ℝ) : ℂ) (-r)‖ =
        Real.rpow (x : ℝ) (-r).re :=
      Complex.norm_cpow_eq_rpow_re_of_pos hxpos _
    rw [hcpow]
    exact Real.rpow_le_rpow_of_exponent_le hxone hre
  have hrle : ‖r‖ ≤ (1 / 2 : ℝ) := hrnorm.le
  have herr : ‖ch8e19Error N x r‖ ≤
      CR * D * Real.rpow (x : ℝ) (-2 * (N : ℝ) + 1 / 2) := by
    rw [ch8e19Error_eq_tail N x hN hx hrle, norm_mul, norm_neg]
    have htail' : ‖ch8e19Tail N r x‖ ≤
        D * Real.rpow (x : ℝ) (-2 * (N : ℝ) + 1 / 2) := by
      convert htail r hr x hxnat using 1
    calc
      ‖ch8e19RemainderFactor N r‖ * ‖ch8e19Tail N r x‖ ≤
          CR * (D * Real.rpow (x : ℝ) (-2 * (N : ℝ) + 1 / 2)) :=
        mul_le_mul (hfactor r hr) htail' (norm_nonneg _) hCR0
      _ = CR * D * Real.rpow (x : ℝ) (-2 * (N : ℝ) + 1 / 2) := by ring
  unfold ch8e19ScaledError
  rw [norm_mul]
  calc
    ‖chapter7NatCpow x (-r)‖ * ‖ch8e19Error N x r‖ ≤
        Real.rpow (x : ℝ) (1 / 2) *
          (CR * D * Real.rpow (x : ℝ) (-2 * (N : ℝ) + 1 / 2)) :=
      mul_le_mul hnat herr (norm_nonneg _) (Real.rpow_nonneg hxpos.le _)
    _ = CR * D * Real.rpow (x : ℝ) (-2 * (N : ℝ) + 1) := by
      calc
        Real.rpow (x : ℝ) (1 / 2) *
            (CR * D * Real.rpow (x : ℝ) (-2 * (N : ℝ) + 1 / 2)) =
          CR * D * (Real.rpow (x : ℝ) (1 / 2) *
            Real.rpow (x : ℝ) (-2 * (N : ℝ) + 1 / 2)) := by ring
        _ = CR * D * Real.rpow (x : ℝ)
            ((1 / 2 : ℝ) + (-2 * (N : ℝ) + 1 / 2)) := by
          congr 1
          exact (Real.rpow_add hxpos (1 / 2) (-2 * (N : ℝ) + 1 / 2)).symm
        _ = _ := by
          congr 2
          ring

private theorem ch8e19_scaledError_deriv_isBigO_rpow (m N : ℕ) (hN : 0 < N) :
    IsBigO atTop (fun x : ℕ ↦ iteratedDeriv m (ch8e19ScaledError N x) 0)
      (fun x : ℕ ↦ Real.rpow (x : ℝ) (-2 * (N : ℝ) + 1)) := by
  obtain ⟨C, hC0, hC⟩ := ch8e19ScaledError_norm_le N hN
  refine isBigO_iff.mpr ⟨(m.factorial : ℝ) * C / (1 / 2 : ℝ) ^ m, ?_⟩
  filter_upwards [eventually_gt_atTop 1] with x hx
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    m (by norm_num : (0 : ℝ) < 1 / 2)
    (ch8e19ScaledError_diffContOnCl N x (by omega))
    (fun r hr ↦ hC r hr x hx)
  have hnorm : ‖Real.rpow (x : ℝ) (-2 * (N : ℝ) + 1)‖ =
      Real.rpow (x : ℝ) (-2 * (N : ℝ) + 1) :=
    Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)
  calc
    ‖iteratedDeriv m (ch8e19ScaledError N x) 0‖ ≤
        (m.factorial : ℝ) *
          (C * Real.rpow (x : ℝ) (-2 * (N : ℝ) + 1)) /
            (1 / 2 : ℝ) ^ m := hcauchy
    _ = ((m.factorial : ℝ) * C / (1 / 2 : ℝ) ^ m) *
        ‖Real.rpow (x : ℝ) (-2 * (N : ℝ) + 1)‖ := by
      rw [hnorm]
      ring

private theorem ch8e19_scaledError_deriv_isBigO (n : ℕ) :
    IsBigO atTop (fun x : ℕ ↦ iteratedDeriv n (ch8e19ScaledError (n + 2) x) 0)
      (fun x : ℕ ↦ 1 / (x : ℝ) ^ (n + 3)) := by
  have hstrong := ch8e19_scaledError_deriv_isBigO_rpow n (n + 2) (by omega)
  have hcompare :
      (fun x : ℕ ↦ Real.rpow (x : ℝ) (-2 * ((n + 2 : ℕ) : ℝ) + 1)) =O[atTop]
        (fun x : ℕ ↦ Real.rpow (x : ℝ) (-(((n + 3 : ℕ) : ℝ)))) := by
    refine isBigO_iff.mpr ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with x hx
    have hxone : (1 : ℝ) ≤ x := by exact_mod_cast hx
    have hexp : -2 * ((n + 2 : ℕ) : ℝ) + 1 ≤ -(((n + 3 : ℕ) : ℝ)) := by
      push_cast
      linarith
    have hle := Real.rpow_le_rpow_of_exponent_le hxone hexp
    have hs : ‖Real.rpow (x : ℝ) (-2 * ((n + 2 : ℕ) : ℝ) + 1)‖ =
        Real.rpow (x : ℝ) (-2 * ((n + 2 : ℕ) : ℝ) + 1) :=
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)
    have hw : ‖Real.rpow (x : ℝ) (-(((n + 3 : ℕ) : ℝ)))‖ =
        Real.rpow (x : ℝ) (-(((n + 3 : ℕ) : ℝ))) :=
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)
    rw [hs, hw, one_mul]
    exact hle
  have h := hstrong.trans hcompare
  have heq : (fun x : ℕ ↦ Real.rpow (x : ℝ) (-(((n + 3 : ℕ) : ℝ)))) =
      fun x : ℕ ↦ 1 / (x : ℝ) ^ (n + 3) := by
    funext x
    have hx0 : (0 : ℝ) ≤ x := by positivity
    calc
      Real.rpow (x : ℝ) (-(((n + 3 : ℕ) : ℝ))) =
          (Real.rpow (x : ℝ) (((n + 3 : ℕ) : ℝ)))⁻¹ :=
        Real.rpow_neg hx0 _
      _ = ((x : ℝ) ^ (n + 3))⁻¹ := by
        exact congrArg Inv.inv (Real.rpow_natCast (x : ℝ) (n + 3))
      _ = 1 / (x : ℝ) ^ (n + 3) := by rw [one_div]
  rw [heq] at h
  exact h

private theorem ch8e19EntryCoeff_eq (j : ℕ) (r : ℂ) :
    ch8e19EntryCoeff j r =
      (((bernoulli (2 * j + 2) : ℚ) : ℂ) / ((2 * j + 2).factorial : ℂ)) *
        chapter7FallingGammaRatio r (2 * j + 1) := by
  unfold ch8e19EntryCoeff
  dsimp only
  congr 2

private theorem ch8e19_iteratedDeriv_scaledTerm (n x j : ℕ) (hx : 0 < x) :
    iteratedDeriv n (ch8e19ScaledTerm x j) 0 =
      (((bernoulli (2 * j + 2) : ℚ) : ℂ) / ((2 * j + 2).factorial : ℂ)) *
        iteratedDeriv n (fun r : ℂ ↦ chapter7FallingGammaRatio r (2 * j + 1)) 0 *
          chapter7NatCpow x (-(2 * j + 1 : ℕ)) := by
  have hfun : ch8e19ScaledTerm x j = fun r : ℂ ↦
      ((((bernoulli (2 * j + 2) : ℚ) : ℂ) / ((2 * j + 2).factorial : ℂ)) *
        chapter7FallingGammaRatio r (2 * j + 1)) *
          chapter7NatCpow x (-(2 * j + 1 : ℕ)) := by
    funext r
    rw [ch8e19ScaledTerm_eq x j hx r, ch8e19EntryCoeff_eq]
    congr 2
    push_cast
    ring
  rw [hfun, iteratedDeriv_mul_const_field, iteratedDeriv_const_mul_field]

private theorem ch8e19_iteratedDeriv_mainScaledTerm (n x : ℕ) :
    iteratedDeriv n (fun r : ℂ ↦ chapter7NatCpow x 1 / (r + 1)) 0 =
      (x : ℂ) * (-1 : ℂ) ^ n * n.factorial := by
  have hpow : chapter7NatCpow x 1 = (x : ℂ) := by
    simp [chapter7NatCpow]
  rw [show (fun r : ℂ ↦ chapter7NatCpow x 1 / (r + 1)) =
      fun r : ℂ ↦ (x : ℂ) * (r + 1)⁻¹ by funext r; rw [hpow]; ring,
    iteratedDeriv_const_mul_field]
  have hinv := congrFun (iter_deriv_inv_linear n (1 : ℂ) 1) 0
  rw [iteratedDeriv_eq_iterate]
  have hinv' : deriv^[n] (fun r : ℂ ↦ (r + 1)⁻¹) 0 =
      (-1 : ℂ) ^ n * n.factorial := by
    simpa using hinv
  rw [hinv']
  ring

private theorem ch8e19_rpow_neg_nat_eq_reciprocal (x q : ℕ) :
    Real.rpow (x : ℝ) (-((q : ℕ) : ℝ)) = 1 / (x : ℝ) ^ q := by
  have hx0 : (0 : ℝ) ≤ x := by positivity
  calc
    Real.rpow (x : ℝ) (-((q : ℕ) : ℝ)) =
        (Real.rpow (x : ℝ) ((q : ℕ) : ℝ))⁻¹ := Real.rpow_neg hx0 _
    _ = ((x : ℝ) ^ q)⁻¹ := congrArg Inv.inv (Real.rpow_natCast (x : ℝ) q)
    _ = 1 / (x : ℝ) ^ q := by rw [one_div]

private theorem ch8e19_natCpow_neg_norm (x q : ℕ) (hx : 0 < x) :
    ‖chapter7NatCpow x (-(q : ℕ))‖ =
      Real.rpow (x : ℝ) (-((q : ℕ) : ℝ)) := by
  unfold chapter7NatCpow
  simpa using Complex.norm_natCast_cpow_of_pos hx (-(q : ℕ) : ℂ)

private theorem ch8e19_natCpow_neg_eq (x q : ℕ) :
    chapter7NatCpow x (-(q : ℕ)) = (((1 / (x : ℝ) ^ q : ℝ)) : ℂ) := by
  unfold chapter7NatCpow
  calc
    (x : ℂ) ^ (-(q : ℕ) : ℂ) = ((x : ℂ) ^ (q : ℂ))⁻¹ :=
      Complex.cpow_neg _ _
    _ = ((x : ℂ) ^ q)⁻¹ := congrArg Inv.inv (Complex.cpow_natCast (x : ℂ) q)
    _ = (((1 / (x : ℝ) ^ q : ℝ)) : ℂ) := by
      simp [one_div, Complex.ofReal_inv]

private theorem ch8e19_iteratedDeriv_scaledTerm_eq_zero_of_lt
    (n x j : ℕ) (hx : 0 < x) (hj : 2 * j + 1 < n) :
    iteratedDeriv n (ch8e19ScaledTerm x j) 0 = 0 := by
  rw [ch8e19_iteratedDeriv_scaledTerm n x j hx,
    ch8e19_falling_deriv_eq_zero_of_lt (2 * j + 1) n hj]
  ring

private theorem ch8e19_iteratedDeriv_scaledTerm_isBigO
    (n j : ℕ) (hj : n + 3 ≤ 2 * j + 1) :
    IsBigO atTop (fun x : ℕ ↦ iteratedDeriv n (ch8e19ScaledTerm x j) 0)
      (fun x : ℕ ↦ 1 / (x : ℝ) ^ (n + 3)) := by
  let C : ℂ :=
    (((bernoulli (2 * j + 2) : ℚ) : ℂ) / ((2 * j + 2).factorial : ℂ)) *
      iteratedDeriv n (fun r : ℂ ↦ chapter7FallingGammaRatio r (2 * j + 1)) 0
  refine isBigO_iff.mpr ⟨‖C‖, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hxone : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hexp : -(((2 * j + 1 : ℕ) : ℝ)) ≤ -(((n + 3 : ℕ) : ℝ)) := by
    exact neg_le_neg (by exact_mod_cast hj)
  have hle := Real.rpow_le_rpow_of_exponent_le hxone hexp
  have htarget : ‖1 / (x : ℝ) ^ (n + 3)‖ =
      Real.rpow (x : ℝ) (-(((n + 3 : ℕ) : ℝ))) := by
    rw [Real.norm_of_nonneg (by positivity),
      ch8e19_rpow_neg_nat_eq_reciprocal]
  rw [ch8e19_iteratedDeriv_scaledTerm n x j hx]
  change ‖C * chapter7NatCpow x (-(2 * j + 1 : ℕ))‖ ≤
    ‖C‖ * ‖1 / (x : ℝ) ^ (n + 3)‖
  rw [norm_mul, ch8e19_natCpow_neg_norm x (2 * j + 1) hx, htarget]
  exact mul_le_mul_of_nonneg_left hle (norm_nonneg C)

private theorem ch8e19ScaledTerm_contDiffAt (n x j : ℕ) (hx : 0 < x) :
    ContDiffAt ℂ n (ch8e19ScaledTerm x j) 0 := by
  rw [show ch8e19ScaledTerm x j = fun r : ℂ ↦ ch8e19EntryCoeff j r *
      chapter7NatCpow x (-(2 * (j + 1) : ℕ) + 1) by
    funext r
    exact ch8e19ScaledTerm_eq x j hx r]
  unfold ch8e19EntryCoeff chapter7FallingGammaRatio
  fun_prop

private theorem ch8e19ScaledError_contDiffAt (n N x : ℕ) (hx : 0 < x) :
    ContDiffAt ℂ n (ch8e19ScaledError N x) 0 := by
  have hana : AnalyticAt ℂ (ch8e19ScaledError N x) 0 :=
    ((ch8e19ScaledError_diffContOnCl N x hx).differentiableOn.analyticOnNhd
      Metric.isOpen_ball) 0 (by simp)
  exact hana.contDiffAt

private theorem ch8e19_combination_eq_expansion (n x : ℕ) (hx : 0 < x) :
    chapter8Entry19Combination n x =
      (n.factorial : ℝ) * x + (if n = 0 then 1 / 2 else 0) +
        (-1 : ℝ) ^ n *
          (∑ j ∈ Finset.range (n + 2),
            iteratedDeriv n (ch8e19ScaledTerm x j) 0).re +
        (-1 : ℝ) ^ n *
          (iteratedDeriv n (ch8e19ScaledError (n + 2) x) 0).re := by
  rw [ch8e19_combination_eq_scaled_deriv n x hx]
  have hfun : ch8e19ScaledSum x = fun r : ℂ ↦
      chapter7NatCpow x 1 / (r + 1) + 1 / 2 +
        ∑ j ∈ Finset.range (n + 2), ch8e19ScaledTerm x j r +
          ch8e19ScaledError (n + 2) x r := by
    funext r
    exact ch8e19ScaledSum_eq (n + 2) x hx r
  rw [hfun]
  have hmain : ContDiffAt ℂ n
      (fun r : ℂ ↦ chapter7NatCpow x 1 / (r + 1)) 0 := by
    fun_prop (disch := norm_num)
  have hconst : ContDiffAt ℂ n (fun _ : ℂ ↦ (1 / 2 : ℂ)) 0 := by fun_prop
  have hterms : ContDiffAt ℂ n
      (fun r : ℂ ↦ ∑ j ∈ Finset.range (n + 2), ch8e19ScaledTerm x j r) 0 := by
    exact ContDiffAt.sum fun j _ ↦ ch8e19ScaledTerm_contDiffAt n x j hx
  have herr := ch8e19ScaledError_contDiffAt n (n + 2) x hx
  have hmainconst : ContDiffAt ℂ n
      ((fun r : ℂ ↦ chapter7NatCpow x 1 / (r + 1)) + fun _ ↦ 1 / 2) 0 :=
    hmain.add hconst
  have hleft : ContDiffAt ℂ n
      (((fun r : ℂ ↦ chapter7NatCpow x 1 / (r + 1)) + fun _ ↦ 1 / 2) +
        fun r ↦ ∑ j ∈ Finset.range (n + 2), ch8e19ScaledTerm x j r) 0 :=
    hmainconst.add hterms
  change (-1 : ℝ) ^ n *
      (iteratedDeriv n
        (((fun r : ℂ ↦ chapter7NatCpow x 1 / (r + 1)) + fun _ ↦ 1 / 2) +
          (fun r ↦ ∑ j ∈ Finset.range (n + 2), ch8e19ScaledTerm x j r) +
            ch8e19ScaledError (n + 2) x) 0).re = _
  rw [iteratedDeriv_add hleft herr,
    iteratedDeriv_add hmainconst hterms,
    iteratedDeriv_add hmain hconst,
    iteratedDeriv_fun_sum (fun j _ ↦ ch8e19ScaledTerm_contDiffAt n x j hx),
    ch8e19_iteratedDeriv_mainScaledTerm]
  by_cases hn : n = 0
  · subst n
    simp
  · rw [iteratedDeriv_const]
    simp only [hn, ↓reduceIte]
    have hnegC : (-1 : ℂ) ^ n = (((-1 : ℝ) ^ n : ℝ) : ℂ) := by norm_cast
    simp only [Complex.add_re, Complex.zero_re]
    rw [hnegC]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    norm_num [hn]
    have hsign : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
      rw [← pow_add]
      simp [show n + n = 2 * n by omega, pow_mul]
    have hmainreal :
        (x : ℝ) * (-1 : ℝ) ^ n * (n.factorial : ℝ) * (-1 : ℝ) ^ n =
          (n.factorial : ℝ) * x := by
      calc
        _ = (n.factorial : ℝ) * x * ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) := by ring
        _ = _ := by rw [hsign]; ring
    linear_combination hmainreal

private noncomputable def ch8e19CorrectionTerm (n j x : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * (iteratedDeriv n (ch8e19ScaledTerm x j) 0).re

private theorem ch8e19CorrectionTerm_eq_zero_of_lt
    (n x j : ℕ) (hx : 0 < x) (hj : 2 * j + 1 < n) :
    ch8e19CorrectionTerm n j x = 0 := by
  unfold ch8e19CorrectionTerm
  rw [ch8e19_iteratedDeriv_scaledTerm_eq_zero_of_lt n x j hx hj]
  simp

private theorem ch8e19CorrectionTerm_isBigO
    (n j : ℕ) (hj : n + 3 ≤ 2 * j + 1) :
    IsBigO atTop (ch8e19CorrectionTerm n j)
      (fun x : ℕ ↦ 1 / (x : ℝ) ^ (n + 3)) := by
  obtain ⟨C, hC⟩ := isBigO_iff.mp (ch8e19_iteratedDeriv_scaledTerm_isBigO n j hj)
  refine isBigO_iff.mpr ⟨C, ?_⟩
  filter_upwards [hC] with x hx
  calc
    ‖ch8e19CorrectionTerm n j x‖ ≤
        ‖iteratedDeriv n (ch8e19ScaledTerm x j) 0‖ := by
      unfold ch8e19CorrectionTerm
      rw [norm_mul, norm_pow]
      norm_num
      exact Complex.abs_re_le_norm _
    _ ≤ C * ‖1 / (x : ℝ) ^ (n + 3)‖ := hx

private theorem ch8e19_iteratedDeriv_scaledTerm_re (n x j : ℕ) (hx : 0 < x) :
    (iteratedDeriv n (ch8e19ScaledTerm x j) 0).re =
      (((bernoulli (2 * j + 2) : ℚ) : ℝ) / ((2 * j + 2).factorial : ℝ)) *
        (iteratedDeriv n
          (fun r : ℂ ↦ chapter7FallingGammaRatio r (2 * j + 1)) 0).re *
            (1 / (x : ℝ) ^ (2 * j + 1)) := by
  rw [ch8e19_iteratedDeriv_scaledTerm n x j hx, ch8e19_natCpow_neg_eq]
  have hcoeff :
      (((bernoulli (2 * j + 2) : ℚ) : ℂ) / ((2 * j + 2).factorial : ℂ)) =
        (((((bernoulli (2 * j + 2) : ℚ) : ℝ) /
          ((2 * j + 2).factorial : ℝ) : ℝ)) : ℂ) := by
    norm_cast
  rw [hcoeff]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

private theorem ch8e19CorrectionTerm_even_main (a x : ℕ) (hx : 0 < x) :
    ch8e19CorrectionTerm (2 * a) a x =
      -((2 * a : ℕ) : ℝ) * (((bernoulli (2 * a + 2) : ℚ) : ℝ)) /
        (2 * ((2 * a + 2 : ℕ) : ℝ) * (x : ℝ) ^ (2 * a + 1)) := by
  unfold ch8e19CorrectionTerm
  rw [ch8e19_iteratedDeriv_scaledTerm_re (2 * a) x a hx]
  have hfall :
      (iteratedDeriv (2 * a)
        (fun r : ℂ ↦ chapter7FallingGammaRatio r (2 * a + 1)) 0).re =
          -((2 * a : ℕ) : ℝ) * (((2 * a + 1).factorial : ℕ) : ℝ) / 2 := by
    rw [ch8e19_falling_deriv_next (2 * a)]
    norm_num
  rw [hfall]
  simp only [pow_mul, neg_one_sq, one_pow]
  have hfact : (2 * a + 2).factorial = (2 * a + 2) * (2 * a + 1).factorial := by
    rw [show 2 * a + 2 = (2 * a + 1) + 1 by omega, Nat.factorial_succ]
  rw [hfact]
  field_simp [show (x : ℝ) ≠ 0 by positivity]
  push_cast
  ring

private theorem ch8e19CorrectionTerm_odd_first (a x : ℕ) (hx : 0 < x) :
    ch8e19CorrectionTerm (2 * a + 1) a x =
      -(((bernoulli (2 * a + 2) : ℚ) : ℝ)) /
        (((2 * a + 2 : ℕ) : ℝ) * (x : ℝ) ^ (2 * a + 1)) := by
  unfold ch8e19CorrectionTerm
  rw [ch8e19_iteratedDeriv_scaledTerm_re (2 * a + 1) x a hx]
  have hfall :
      (iteratedDeriv (2 * a + 1)
        (fun r : ℂ ↦ chapter7FallingGammaRatio r (2 * a + 1)) 0).re =
          (((2 * a + 1).factorial : ℕ) : ℝ) := by
    rw [ch8e19_falling_deriv_diagonal (2 * a + 1)]
    norm_num
  rw [hfall]
  simp only [pow_add, pow_mul, neg_one_sq, one_pow]
  norm_num
  have hfact : (2 * a + 2).factorial = (2 * a + 2) * (2 * a + 1).factorial := by
    rw [show 2 * a + 2 = (2 * a + 1) + 1 by omega, Nat.factorial_succ]
  rw [hfact]
  field_simp [show (x : ℝ) ≠ 0 by positivity]
  push_cast
  ring

private theorem ch8e19CorrectionTerm_odd_third (a x : ℕ) (hx : 0 < x) :
    ch8e19CorrectionTerm (2 * a + 1) (a + 1) x =
      -(((2 * a + 1 : ℕ) : ℝ) * (((2 * a + 1 : ℕ) : ℝ) + 5 / 3) *
          (((bernoulli (2 * a + 4) : ℚ) : ℝ))) /
        (8 * ((2 * a + 4 : ℕ) : ℝ) * (x : ℝ) ^ (2 * a + 3)) := by
  unfold ch8e19CorrectionTerm
  rw [ch8e19_iteratedDeriv_scaledTerm_re (2 * a + 1) x (a + 1) hx]
  have hfall :
      (iteratedDeriv (2 * a + 1)
        (fun r : ℂ ↦ chapter7FallingGammaRatio r ((2 * a + 1) + 2)) 0).re =
          (((2 * a + 1).factorial : ℕ) : ℝ) * (2 * a + 1) *
            (2 * a + 2) * (2 * a + 3) * (3 * (2 * a + 1) + 5) / 24 := by
    rw [ch8e19_falling_deriv_next_two (2 * a + 1)]
    norm_num
    left
    ring
  rw [show 2 * (a + 1) + 1 = (2 * a + 1) + 2 by omega, hfall]
  simp only [pow_add, pow_mul, neg_one_sq, one_pow]
  norm_num
  rw [show (2 * (a + 1) + 2).factorial =
      (2 * a + 4) * (2 * a + 3) * (2 * a + 2) * (2 * a + 1).factorial by
    rw [show 2 * (a + 1) + 2 = (((2 * a + 1) + 1) + 1) + 1 by omega,
      Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    ring]
  field_simp [show (x : ℝ) ≠ 0 by positivity]
  push_cast
  ring_nf

private noncomputable def ch8e19FirstCorrection (n x : ℕ) : ℝ :=
  -(((bernoulli (n + 1) : ℚ) : ℝ) /
    ((n + 1 : ℕ) * (x : ℝ) ^ n))

private noncomputable def ch8e19SecondCorrection (n x : ℕ) : ℝ :=
  -((n : ℝ) * ((bernoulli (n + 2) : ℚ) : ℝ) /
    (2 * (n + 2 : ℕ) * (x : ℝ) ^ (n + 1)))

private noncomputable def ch8e19ThirdCorrection (n x : ℕ) : ℝ :=
  -((n : ℝ) * ((n : ℝ) + 5 / 3) *
    ((bernoulli (n + 3) : ℚ) : ℝ) /
      (8 * (n + 3 : ℕ) * (x : ℝ) ^ (n + 2)))

private theorem ch8e19Approx_eq_corrections (n x : ℕ) :
    chapter8Entry19Approx n x =
      (n.factorial : ℝ) * x + ch8e19FirstCorrection n x +
        ch8e19SecondCorrection n x + ch8e19ThirdCorrection n x := by
  unfold chapter8Entry19Approx ch8e19FirstCorrection ch8e19SecondCorrection
    ch8e19ThirdCorrection
  ring

private theorem ch8e19FirstCorrection_even_eq_zero (a x : ℕ) (ha : 0 < a) :
    ch8e19FirstCorrection (2 * a) x = 0 := by
  have hodd : Odd (2 * a + 1) := ⟨a, by omega⟩
  have hgt : 1 < 2 * a + 1 := by omega
  unfold ch8e19FirstCorrection
  rw [show 2 * a + 1 = 2 * a + 1 by rfl, bernoulli_eq_zero_of_odd hodd hgt]
  norm_num

private theorem ch8e19ThirdCorrection_even_eq_zero (a x : ℕ) :
    ch8e19ThirdCorrection (2 * a) x = 0 := by
  have hodd : Odd (2 * a + 3) := ⟨a + 1, by omega⟩
  have hgt : 1 < 2 * a + 3 := by omega
  unfold ch8e19ThirdCorrection
  rw [show 2 * a + 3 = 2 * a + 3 by rfl, bernoulli_eq_zero_of_odd hodd hgt]
  norm_num

private theorem ch8e19SecondCorrection_odd_eq_zero (a x : ℕ) :
    ch8e19SecondCorrection (2 * a + 1) x = 0 := by
  have hodd : Odd (2 * a + 3) := ⟨a + 1, by omega⟩
  have hgt : 1 < 2 * a + 3 := by omega
  unfold ch8e19SecondCorrection
  rw [show 2 * a + 1 + 2 = 2 * a + 3 by omega,
    bernoulli_eq_zero_of_odd hodd hgt]
  norm_num

private theorem ch8e19_correction_even_isBigO (a : ℕ) :
    IsBigO atTop
      (fun x : ℕ ↦
        ∑ j ∈ Finset.range (2 * a + 2), ch8e19CorrectionTerm (2 * a) j x -
          ch8e19SecondCorrection (2 * a) x)
      (fun x : ℕ ↦ 1 / (x : ℝ) ^ (2 * a + 3)) := by
  let A : ℕ → ℕ → ℝ := fun j x ↦
    ch8e19CorrectionTerm (2 * a) j x -
      if j = a then ch8e19SecondCorrection (2 * a) x else 0
  have hA : ∀ j ∈ Finset.range (2 * a + 2),
      IsBigO atTop (A j) (fun x : ℕ ↦ 1 / (x : ℝ) ^ (2 * a + 3)) := by
    intro j hj
    by_cases hjlt : j < a
    · have heq : (fun _ : ℕ ↦ (0 : ℝ)) =ᶠ[atTop] A j := by
        filter_upwards [eventually_gt_atTop 0] with x hx
        dsimp [A]
        rw [ch8e19CorrectionTerm_eq_zero_of_lt (2 * a) x j hx (by omega)]
        simp [ne_of_lt hjlt]
      exact (isBigO_zero _ _).congr' heq (Eventually.of_forall fun _ ↦ rfl)
    by_cases hjeq : j = a
    · subst j
      have heq : (fun _ : ℕ ↦ (0 : ℝ)) =ᶠ[atTop] A a := by
        filter_upwards [eventually_gt_atTop 0] with x hx
        dsimp [A]
        rw [ch8e19CorrectionTerm_even_main a x hx]
        simp [ch8e19SecondCorrection]
        ring
      exact (isBigO_zero _ _).congr' heq (Eventually.of_forall fun _ ↦ rfl)
    · have hjgt : a < j := by omega
      have h := ch8e19CorrectionTerm_isBigO (2 * a) j (by omega)
      simpa [A, hjeq] using h
  have hsum := Asymptotics.IsBigO.sum hA
  refine hsum.congr' ?_ (Eventually.of_forall fun _ ↦ rfl)
  apply Eventually.of_forall
  intro x
  simp only [A, Finset.sum_sub_distrib, Finset.sum_apply]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_range, show a < 2 * a + 2 by omega, ↓reduceIte]

private theorem ch8e19_correction_odd_isBigO (a : ℕ) :
    IsBigO atTop
      (fun x : ℕ ↦
        (∑ j ∈ Finset.range (2 * a + 3), ch8e19CorrectionTerm (2 * a + 1) j x) -
          ch8e19FirstCorrection (2 * a + 1) x -
            ch8e19ThirdCorrection (2 * a + 1) x)
      (fun x : ℕ ↦ 1 / (x : ℝ) ^ (2 * a + 4)) := by
  let A : ℕ → ℕ → ℝ := fun j x ↦
    ch8e19CorrectionTerm (2 * a + 1) j x -
      (if j = a then ch8e19FirstCorrection (2 * a + 1) x else 0) -
        (if j = a + 1 then ch8e19ThirdCorrection (2 * a + 1) x else 0)
  have hA : ∀ j ∈ Finset.range (2 * a + 3),
      IsBigO atTop (A j) (fun x : ℕ ↦ 1 / (x : ℝ) ^ (2 * a + 4)) := by
    intro j hj
    by_cases hjlt : j < a
    · have heq : (fun _ : ℕ ↦ (0 : ℝ)) =ᶠ[atTop] A j := by
        filter_upwards [eventually_gt_atTop 0] with x hx
        dsimp [A]
        rw [ch8e19CorrectionTerm_eq_zero_of_lt (2 * a + 1) x j hx (by omega)]
        simp [ne_of_lt hjlt, show j ≠ a + 1 by omega]
      exact (isBigO_zero _ _).congr' heq (Eventually.of_forall fun _ ↦ rfl)
    by_cases hja : j = a
    · subst j
      have heq : (fun _ : ℕ ↦ (0 : ℝ)) =ᶠ[atTop] A a := by
        filter_upwards [eventually_gt_atTop 0] with x hx
        dsimp [A]
        rw [ch8e19CorrectionTerm_odd_first a x hx]
        simp [ch8e19FirstCorrection]
        ring
      exact (isBigO_zero _ _).congr' heq (Eventually.of_forall fun _ ↦ rfl)
    by_cases hjas : j = a + 1
    · subst j
      have heq : (fun _ : ℕ ↦ (0 : ℝ)) =ᶠ[atTop] A (a + 1) := by
        filter_upwards [eventually_gt_atTop 0] with x hx
        dsimp [A]
        rw [ch8e19CorrectionTerm_odd_third a x hx]
        simp [ch8e19ThirdCorrection]
        ring
      exact (isBigO_zero _ _).congr' heq (Eventually.of_forall fun _ ↦ rfl)
    · have hjgt : a + 1 < j := by omega
      have h := ch8e19CorrectionTerm_isBigO (2 * a + 1) j (by omega)
      simpa [A, hja, hjas] using h
  have hsum := Asymptotics.IsBigO.sum hA
  refine hsum.congr' ?_ (Eventually.of_forall fun _ ↦ rfl)
  apply Eventually.of_forall
  intro x
  simp only [A, Finset.sum_sub_distrib, Finset.sum_apply]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_range, show a < 2 * a + 3 by omega,
    show a + 1 < 2 * a + 3 by omega, ↓reduceIte]

private theorem ch8e19_scaledError_re_isBigO (n : ℕ) :
    IsBigO atTop
      (fun x : ℕ ↦ (-1 : ℝ) ^ n *
        (iteratedDeriv n (ch8e19ScaledError (n + 2) x) 0).re)
      (fun x : ℕ ↦ 1 / (x : ℝ) ^ (n + 3)) := by
  obtain ⟨C, hC⟩ := isBigO_iff.mp (ch8e19_scaledError_deriv_isBigO n)
  refine isBigO_iff.mpr ⟨C, ?_⟩
  filter_upwards [hC] with x hx
  calc
    ‖(-1 : ℝ) ^ n *
        (iteratedDeriv n (ch8e19ScaledError (n + 2) x) 0).re‖ ≤
        ‖iteratedDeriv n (ch8e19ScaledError (n + 2) x) 0‖ := by
      rw [norm_mul, norm_pow]
      norm_num
      exact Complex.abs_re_le_norm _
    _ ≤ C * ‖1 / (x : ℝ) ^ (n + 3)‖ := hx

private theorem ch8e19_falling_zero (q : ℕ) (hq : 0 < q) :
    chapter7FallingGammaRatio 0 q = 0 := by
  unfold chapter7FallingGammaRatio
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hq)
  simp

private theorem ch8e19CorrectionTerm_zero (j x : ℕ) (hx : 0 < x) :
    ch8e19CorrectionTerm 0 j x = 0 := by
  unfold ch8e19CorrectionTerm
  rw [ch8e19_iteratedDeriv_scaledTerm_re 0 x j hx]
  simp [ch8e19_falling_zero (2 * j + 1) (by omega)]

private theorem ch8e19_corrections_isBigO (n : ℕ) :
    IsBigO atTop
      (fun x : ℕ ↦
        (if n = 0 then 1 / 2 else 0) +
            (∑ j ∈ Finset.range (n + 2), ch8e19CorrectionTerm n j x) -
          ch8e19FirstCorrection n x - ch8e19SecondCorrection n x -
            ch8e19ThirdCorrection n x)
      (fun x : ℕ ↦ 1 / (x : ℝ) ^ (n + 3)) := by
  by_cases hn : n = 0
  · subst n
    have heq : (fun _ : ℕ ↦ (0 : ℝ)) =ᶠ[atTop] fun x : ℕ ↦
        (if (0 : ℕ) = 0 then 1 / 2 else 0) +
            (∑ j ∈ Finset.range (0 + 2), ch8e19CorrectionTerm 0 j x) -
          ch8e19FirstCorrection 0 x - ch8e19SecondCorrection 0 x -
            ch8e19ThirdCorrection 0 x := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      have hsum : ∑ j ∈ Finset.range (0 + 2), ch8e19CorrectionTerm 0 j x = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        exact ch8e19CorrectionTerm_zero j x hx
      rw [hsum]
      simp [ch8e19FirstCorrection, ch8e19SecondCorrection, ch8e19ThirdCorrection,
        bernoulli_one]
      norm_num
    exact (isBigO_zero _ _).congr' heq (Eventually.of_forall fun _ ↦ rfl)
  rcases Nat.even_or_odd n with heven | hodd
  · obtain ⟨a, ha⟩ := heven
    have hnrep : n = 2 * a := by omega
    rw [hnrep] at hn ⊢
    have ha0 : 0 < a := by omega
    have h := ch8e19_correction_even_isBigO a
    refine h.congr' (Eventually.of_forall fun x ↦ ?_)
      (Eventually.of_forall fun _ ↦ rfl)
    change
      (∑ j ∈ Finset.range (2 * a + 2), ch8e19CorrectionTerm (2 * a) j x) -
          ch8e19SecondCorrection (2 * a) x =
        (if 2 * a = 0 then 1 / 2 else 0) +
              (∑ j ∈ Finset.range (2 * a + 2), ch8e19CorrectionTerm (2 * a) j x) -
            ch8e19FirstCorrection (2 * a) x - ch8e19SecondCorrection (2 * a) x -
          ch8e19ThirdCorrection (2 * a) x
    rw [ch8e19FirstCorrection_even_eq_zero a x ha0,
      ch8e19ThirdCorrection_even_eq_zero]
    simp only [show 2 * a ≠ 0 by omega, ↓reduceIte, zero_add, sub_zero]
  · obtain ⟨a, ha⟩ := hodd
    have hnrep : n = 2 * a + 1 := by omega
    rw [hnrep] at hn ⊢
    have h := ch8e19_correction_odd_isBigO a
    refine h.congr' (Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall fun _ ↦ rfl)
    change
      (∑ j ∈ Finset.range (2 * a + 3), ch8e19CorrectionTerm (2 * a + 1) j x) -
          ch8e19FirstCorrection (2 * a + 1) x - ch8e19ThirdCorrection (2 * a + 1) x =
        (if 2 * a + 1 = 0 then 1 / 2 else 0) +
              (∑ j ∈ Finset.range (2 * a + 1 + 2),
                ch8e19CorrectionTerm (2 * a + 1) j x) -
            ch8e19FirstCorrection (2 * a + 1) x -
          ch8e19SecondCorrection (2 * a + 1) x -
            ch8e19ThirdCorrection (2 * a + 1) x
    rw [ch8e19SecondCorrection_odd_eq_zero]
    simp only [show 2 * a + 1 ≠ 0 by omega, ↓reduceIte, zero_add, sub_zero]

private theorem ch8e19_sum_correction_eq (n x : ℕ) :
    ∑ j ∈ Finset.range (n + 2), ch8e19CorrectionTerm n j x =
      (-1 : ℝ) ^ n *
        (∑ j ∈ Finset.range (n + 2),
          iteratedDeriv n (ch8e19ScaledTerm x j) 0).re := by
  unfold ch8e19CorrectionTerm
  change (∑ j ∈ Finset.range (n + 2),
      (-1 : ℝ) ^ n * (iteratedDeriv n (ch8e19ScaledTerm x j) 0).re) =
    (-1 : ℝ) ^ n * Complex.reCLM
      (∑ j ∈ Finset.range (n + 2), iteratedDeriv n (ch8e19ScaledTerm x j) 0)
  rw [map_sum, Finset.mul_sum]
  rfl

private theorem ch8e19_combination_sub_approx_isBigO (n : ℕ) :
    IsBigO atTop
      (fun x : ℕ ↦ chapter8Entry19Combination n x - chapter8Entry19Approx n x)
      (fun x : ℕ ↦ 1 / (x : ℝ) ^ (n + 3)) := by
  have h := (ch8e19_corrections_isBigO n).add (ch8e19_scaledError_re_isBigO n)
  refine h.congr' ?_ (Eventually.of_forall fun _ ↦ rfl)
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [ch8e19_combination_eq_expansion n x hx, ch8e19Approx_eq_corrections,
    ← ch8e19_sum_correction_eq]
  ring

/-- **Ramanujan's asymptotic expansion of a binomial combination of log-power sums.** For natural
numbers $m$ and $x$ let $S_m(x) = \sum_{k=1}^{x} (\log k)^m$, let $c_m = (-1)^m \zeta^{(m)}(0)$,
where $\zeta^{(m)}(0)$ is the $m$-th derivative at $0$ of the real function
$s \mapsto \operatorname{Re} \zeta(s)$, and let $\psi_m(x) = S_m(x) - c_m$. Let $n$ be a natural
number. Then for every $m \le n$,
$$S_m(x) - \int_1^x (\log t)^m \, dt - \frac{(\log x)^m}{2} + (-1)^{m+1} m! \to c_m$$
as $x \to \infty$ through the natural numbers, and
$$\sum_{k=0}^{n} (-1)^{n+k} \binom{n}{k} (\log x)^k \psi_{n-k}(x) = n! \, x -
\frac{B_{n+1}}{(n+1) x^n} - \frac{n B_{n+2}}{2 (n+2) x^{n+1}} -
\frac{n (n + 5/3) B_{n+3}}{8 (n+3) x^{n+2}} + O\left(\frac{1}{x^{n+3}}\right)$$
as $x \to \infty$ through the natural numbers, where $B_j$ are the Bernoulli numbers with
$B_1 = -1/2$.

Proof: Analytic continuation of ζ to `re s > -1` by Euler–Maclaurin, Cauchy estimates for the
remainder's derivatives, and the Euler–Maclaurin tail expansion of the log-power sums.

Proves `Wanted` entry `ramanujan_part1_ch8_entry19_gaussdigamma`.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 8.
-/
theorem ramanujan_part1_ch8_entry19_gaussdigamma (n : ℕ) :
    (∀ m ≤ n,
      Tendsto (chapter8LogPowerConstantApprox m) atTop
        (𝓝 (chapter8LogPowerConstant m))) ∧
      IsBigO atTop
        (fun x : ℕ =>
          chapter8Entry19Combination n x - chapter8Entry19Approx n x)
        (fun x : ℕ => 1 / (x : ℝ) ^ (n + 3)) := by
  exact ⟨fun m _ ↦ ch8e19_constantApprox_tendsto m,
    ch8e19_combination_sub_approx_isBigO n⟩

end

end Entry19Gaussdigamma

end MathlibExt.Analysis.Ramanujan.Part1Ch8
