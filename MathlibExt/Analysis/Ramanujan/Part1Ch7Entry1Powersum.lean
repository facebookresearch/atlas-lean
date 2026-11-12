/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.LSeries.RiemannZeta

import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.Analysis.Calculus.EulerMaclaurinFormula

/-!
# Ramanujan's asymptotic expansion for power sums

This file proves the Euler--Maclaurin asymptotic expansion of finite sums of arbitrary complex
powers, including the identification of the constant term with the Riemann zeta function.
-/

@[expose] public section

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry1Powersum

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter7NatCpow (n : ℕ) (r : ℂ) : ℂ :=
  Complex.cpow (n : ℂ) r

/-- The power of one used in the Chapter 7 expansion is one. -/
@[simp]
private theorem ch7Entry1NatCpow_one (r : ℂ) : chapter7NatCpow 1 r = 1 := by
  simp [chapter7NatCpow]

/-- The norm of a positive natural complex power is the corresponding real power. -/
private theorem ch7Entry1NatCpow_norm_of_pos {n : ℕ} (hn : 0 < n) (r : ℂ) :
    ‖chapter7NatCpow n r‖ = Real.rpow (n : ℝ) r.re := by
  exact Complex.norm_natCast_cpow_of_pos hn r

def chapter7FallingGammaRatio (r : ℂ) (q : ℕ) : ℂ :=
  ∏ j ∈ range q, (r - (j : ℂ))

def chapter7Entry1Term (r : ℂ) (n j : ℕ) : ℂ :=
  let k := j + 1
  (((bernoulli (2 * k) : ℚ) : ℂ) / ((2 * k).factorial : ℂ)) *
    chapter7FallingGammaRatio r (2 * k - 1) *
      chapter7NatCpow n (r - (2 * k : ℕ) + 1)

def chapter7Entry1Approx (r : ℂ) (N n : ℕ) : ℂ :=
  riemannZeta (-r) + chapter7NatCpow n (r + 1) / (r + 1) +
    chapter7NatCpow n r / 2 + ∑ j ∈ range N, chapter7Entry1Term r n j

def chapter7PowerSum (r : ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Icc 1 n, chapter7NatCpow k r

private noncomputable def ch7Entry1Kernel (p : ℕ) (x : ℝ) : ℝ :=
  bernoulliFun p (Int.fract x)

private theorem ch7Entry1Kernel_periodic (p : ℕ) :
    Function.Periodic (ch7Entry1Kernel p) 1 := by
  intro x
  simp [ch7Entry1Kernel, Int.fract_add_one]

private theorem ch7Entry1Kernel_continuous {p : ℕ} (hp : p ≠ 1) :
    Continuous (ch7Entry1Kernel p) := by
  change Continuous (fun x : ℝ => bernoulliFun p (Int.fract x))
  simpa [Function.comp_def] using
    (continuous_bernoulliFun p).continuousOn.comp_fract''
      (bernoulliFun_endpoints_eq_of_ne_one hp).symm

private theorem ch7Entry1Kernel_one (N : ℕ) (hN : 0 < N) :
    ch7Entry1Kernel (2 * N + 1) 1 = 0 := by
  have hodd : Odd (2 * N + 1) := ⟨N, by omega⟩
  have hgt : 1 < 2 * N + 1 := by omega
  simp [ch7Entry1Kernel, bernoulliFun_eval_zero,
    bernoulli_eq_zero_of_odd hodd hgt]

private noncomputable def ch7Entry1MellinBase (N : ℕ) (x : ℝ) : ℂ :=
  if 1 ≤ x then (ch7Entry1Kernel (2 * N + 1) x : ℂ) else 0

private theorem ch7Entry1MellinBase_continuous (N : ℕ) (hN : 0 < N) :
    Continuous (ch7Entry1MellinBase N) := by
  have hp : 2 * N + 1 ≠ 1 := by omega
  have hk : Continuous (fun x => (ch7Entry1Kernel (2 * N + 1) x : ℂ)) :=
    Complex.continuous_ofReal.comp (ch7Entry1Kernel_continuous hp)
  change Continuous (fun x : ℝ => if 1 ≤ x then
    (ch7Entry1Kernel (2 * N + 1) x : ℂ) else 0)
  refine hk.if_le continuous_const continuous_const continuous_id ?_
  intro x hx
  have : x = 1 := by linarith
  subst x
  simp [ch7Entry1Kernel_one N hN]

private theorem ch7Entry1MellinBase_locallyIntegrable (N : ℕ) (hN : 0 < N) :
    LocallyIntegrableOn (ch7Entry1MellinBase N) (Set.Ioi 0) :=
  (ch7Entry1MellinBase_continuous N hN).continuousOn.locallyIntegrableOn measurableSet_Ioi

private theorem ch7Entry1Kernel_norm_le (N : ℕ) (hN : 0 < N) :
    ∃ C : ℝ, ∀ x : ℝ, ‖ch7Entry1Kernel (2 * N + 1) x‖ ≤ C := by
  have hp : 2 * N + 1 ≠ 1 := by omega
  obtain ⟨C, hC⟩ := ((ch7Entry1Kernel_periodic (2 * N + 1)).isBounded_of_continuous
    one_ne_zero (ch7Entry1Kernel_continuous hp)).exists_norm_le
  exact ⟨C, fun x => hC _ ⟨x, rfl⟩⟩

private theorem ch7Entry1MellinBase_isBigO_atTop (N : ℕ) (hN : 0 < N) :
    ch7Entry1MellinBase N =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
  obtain ⟨C, hC⟩ := ch7Entry1Kernel_norm_le N hN
  refine isBigO_iff.mpr ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  simpa [ch7Entry1MellinBase, hx] using hC x

private theorem ch7Entry1MellinBase_isBigO_zero (N : ℕ) (b : ℝ) :
    ch7Entry1MellinBase N =O[𝓝[>] 0] (fun x : ℝ => x ^ (-b)) := by
  refine isBigO_iff.mpr ⟨0, ?_⟩
  have he : ∀ᶠ x : ℝ in 𝓝[>] 0, x < 1 :=
    Filter.Eventually.filter_mono inf_le_left (Iio_mem_nhds zero_lt_one)
  filter_upwards [he] with x hx
  simp [ch7Entry1MellinBase, not_le.mpr hx]

private noncomputable def ch7Entry1MellinIntegral (N : ℕ) (r : ℂ) : ℂ :=
  mellin (ch7Entry1MellinBase N) (r - (2 * N + 1 : ℕ) + 1)

private theorem ch7Entry1MellinIntegral_differentiableAt
    (N : ℕ) (hN : 0 < N) (r : ℂ) (hu : r.re < 2 * N) :
    DifferentiableAt ℂ (ch7Entry1MellinIntegral N) r := by
  let s : ℂ := r - (2 * N + 1 : ℕ) + 1
  have hs : s.re < 0 := by
    dsimp [s]
    norm_num [Nat.cast_add, Nat.cast_mul] at ⊢
    linarith
  have hm : DifferentiableAt ℂ (mellin (ch7Entry1MellinBase N)) s :=
    mellin_differentiableAt_of_isBigO_rpow
      (ch7Entry1MellinBase_locallyIntegrable N hN)
      (by simpa using ch7Entry1MellinBase_isBigO_atTop N hN)
      hs
      (ch7Entry1MellinBase_isBigO_zero N (s.re - 1))
      (by linarith)
  have hg : DifferentiableAt ℂ (fun z : ℂ => z - (2 * N + 1 : ℕ) + 1) r := by
    fun_prop
  unfold ch7Entry1MellinIntegral
  convert hm.comp r hg using 1
  rfl

private theorem ch7Entry1MellinIntegral_eq_integral
    (N : ℕ) (hN : 0 < N) (r : ℂ) :
    ch7Entry1MellinIntegral N r =
      ∫ x : ℝ in Set.Ioi 1,
        (x : ℂ) ^ (r - (2 * N + 1 : ℕ)) * (ch7Entry1Kernel (2 * N + 1) x : ℂ) := by
  unfold ch7Entry1MellinIntegral mellin
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Set.Ioi_subset_Ioi zero_le_one)]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    rw [show r - (2 * N + 1 : ℕ) + 1 - 1 = r - (2 * N + 1 : ℕ) by ring]
    simp [ch7Entry1MellinBase, hx.le, smul_eq_mul]
  · intro x hx
    rcases lt_or_eq_of_le (le_of_not_gt hx.2) with hlt | rfl
    · simp [ch7Entry1MellinBase, not_le.mpr hlt]
    · simp [ch7Entry1MellinBase, ch7Entry1Kernel_one N hN]

private theorem ch7Entry1Tail_integrable
    (N : ℕ) (hN : 0 < N) (r : ℂ) (hu : r.re < 2 * N) :
    IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (r - (2 * N + 1 : ℕ)) *
        (ch7Entry1Kernel (2 * N + 1) x : ℂ)) (Set.Ioi 1) := by
  let s : ℂ := r - (2 * N + 1 : ℕ) + 1
  have hs : s.re < 0 := by
    dsimp [s]
    norm_num [Nat.cast_add, Nat.cast_mul] at ⊢
    linarith
  have hconv : MellinConvergent (ch7Entry1MellinBase N) s :=
    mellinConvergent_of_isBigO_rpow
      (ch7Entry1MellinBase_locallyIntegrable N hN)
      (by simpa using ch7Entry1MellinBase_isBigO_atTop N hN) hs
      (ch7Entry1MellinBase_isBigO_zero N (s.re - 1)) (by linarith)
  rw [MellinConvergent] at hconv
  refine (hconv.mono_set (Set.Ioi_subset_Ioi zero_le_one)).congr_fun ?_ measurableSet_Ioi
  intro x hx
  have hsr : s - 1 = r - (2 * N + 1 : ℕ) := by simp [s]
  rw [hsr]
  simp [ch7Entry1MellinBase, hx.le, smul_eq_mul]

private theorem ch7Entry1Falling_succ (r : ℂ) (q : ℕ) :
    chapter7FallingGammaRatio r (q + 1) =
      chapter7FallingGammaRatio r q * (r - (q : ℂ)) := by
  simp [chapter7FallingGammaRatio, Finset.prod_range_succ]

private theorem ch7Entry1_iteratedDeriv_cpow
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
      · simp [he, ch7Entry1Falling_succ]
      · have hd := (hasDerivAt_ofReal_cpow_const hx he).const_mul
            (chapter7FallingGammaRatio r q)
        rw [hd.deriv]
        rw [ch7Entry1Falling_succ]
        rw [show r - ((q + 1 : ℕ) : ℂ) = r - (q : ℂ) - 1 by
          push_cast
          ring]
        ring

private theorem ch7Entry1_cpow_contDiffAt
    (r : ℂ) {x : ℝ} (hx : 0 < x) {m : WithTop ℕ∞} :
    ContDiffAt ℝ m (fun y : ℝ => (y : ℂ) ^ r) x := by
  have hc : ContDiffAt ℂ m (fun z : ℂ => z ^ r) (x : ℂ) :=
    (analyticAt_id.cpow analyticAt_const (Complex.ofReal_mem_slitPlane.mpr hx)).contDiffAt
  exact (hc.restrict_scalars ℝ).comp x Complex.ofRealCLM.contDiff.contDiffAt

private theorem ch7Entry1_cpow_contDiffOn
    (r : ℂ) (p n : ℕ) :
    ContDiffOn ℝ (p : WithTop ℕ∞) (fun x : ℝ => (x : ℂ) ^ r)
      (Set.Icc 1 (n : ℝ)) := by
  intro x hx
  exact (ch7Entry1_cpow_contDiffAt r (lt_of_lt_of_le zero_lt_one hx.1)).contDiffWithinAt

private theorem ch7Entry1_iteratedDerivWithin_cpow
    (r : ℂ) (q n : ℕ) (hn : 1 < n) {x : ℝ} (hx : x ∈ Set.Icc 1 (n : ℝ)) :
    iteratedDerivWithin q (fun y : ℝ => (y : ℂ) ^ r) (Set.Icc 1 (n : ℝ)) x =
      chapter7FallingGammaRatio r q * (x : ℂ) ^ (r - (q : ℕ)) := by
  rw [iteratedDerivWithin_eq_iteratedDeriv
    (uniqueDiffOn_Icc (by exact_mod_cast hn))
    (ch7Entry1_cpow_contDiffAt r (lt_of_lt_of_le zero_lt_one hx.1)) hx]
  exact ch7Entry1_iteratedDeriv_cpow r q (ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1))

private theorem ch7Entry1_bernoulli_coeff (j : ℕ) :
    ((bernoulli j : ℚ) : ℝ) =
      if j = 1 then (-1 / 2 : ℝ) else (bernoulli j : ℝ) := by
  by_cases hj : j = 1
  · subst j
    simp [bernoulli_one]
  · simp [hj]

private theorem ch7Entry1_bernoulliFun_eq_sum (p : ℕ) (x : ℝ) :
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
    have e1 : p + 1 - 1 - i = p - i := by omega
    have e2 : p - (p - i) = i := by omega
    rw [e1, e2]
  rw [hrefl]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  rw [← ch7Entry1_bernoulli_coeff j, Nat.choose_symm (by omega : j ≤ p)]
  ring

private theorem ch7Entry1Kernel_eq_of_spec
    (P : ℕ → ℝ → ℝ) (p : ℕ)
    (hper : ∀ (m : ℕ) (x : ℝ), P m (x + 1) = P m x)
    (hunit : ∀ x ∈ Set.Ico (0 : ℝ) 1, P p x =
      ∑ j ∈ Finset.range (p + 1), (Nat.choose p j : ℝ) *
        (if j = 1 then (-1 / 2 : ℝ) else (bernoulli j : ℝ)) * x ^ (p - j))
    (x : ℝ) :
    P p x = ch7Entry1Kernel p x := by
  have hp : Function.Periodic (P p) 1 := hper p
  have hfract : P p (Int.fract x) = P p x := by
    rw [Int.fract]
    simpa only [mul_one] using hp.sub_int_mul_eq (Int.floor x)
  rw [← hfract, hunit (Int.fract x) ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩]
  exact (ch7Entry1_bernoulliFun_eq_sum p (Int.fract x)).symm

private theorem ch7Entry1EulerMaclaurin_real
    (a b : ℤ) (p : ℕ) (f : ℝ → ℝ) (hab : a < b) (hp : 1 ≤ p)
    (hdf : ContDiffOn ℝ (p : WithTop ℕ∞) f (Set.Icc (a : ℝ) (b : ℝ))) :
    ∑ n ∈ Finset.Icc a b, f (n : ℝ) =
      (∫ x in (a : ℝ)..(b : ℝ), f x) + (f a + f b) / 2 +
        (∑ k ∈ Finset.Icc 1 (p / 2),
          (bernoulli (2 * k) : ℝ) / (Nat.factorial (2 * k) : ℝ) *
            (iteratedDerivWithin (2 * k - 1) f (Set.Icc (a : ℝ) (b : ℝ)) b -
              iteratedDerivWithin (2 * k - 1) f (Set.Icc (a : ℝ) (b : ℝ)) a)) +
        ((-1 : ℝ) ^ (p + 1) / (Nat.factorial p : ℝ) *
          (∫ x in (a : ℝ)..(b : ℝ), ch7Entry1Kernel p x *
            iteratedDerivWithin p f (Set.Icc (a : ℝ) (b : ℝ)) x)) := by
  obtain ⟨P, hper, hunit, hformula⟩ :=
    MetaMathlibExt.eulerMaclaurinFormula a b p f hab hp hdf
  simpa only [ch7Entry1Kernel_eq_of_spec P p hper hunit] using hformula

private theorem ch7Entry1_iteratedDerivWithin_re
    {f : ℝ → ℂ} {s : Set ℝ} {x : ℝ} (q : ℕ)
    (hf : ContDiffWithinAt ℝ q f s x) (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    iteratedDerivWithin q (fun y => (f y).re) s x =
      (iteratedDerivWithin q f s x).re := by
  change iteratedDerivWithin q (Complex.reCLM ∘ f) s x =
    Complex.reCLM (iteratedDerivWithin q f s x)
  unfold iteratedDerivWithin
  rw [Complex.reCLM.iteratedFDerivWithin_comp_left hf hs hx le_rfl]
  rfl

private theorem ch7Entry1_iteratedDerivWithin_im
    {f : ℝ → ℂ} {s : Set ℝ} {x : ℝ} (q : ℕ)
    (hf : ContDiffWithinAt ℝ q f s x) (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    iteratedDerivWithin q (fun y => (f y).im) s x =
      (iteratedDerivWithin q f s x).im := by
  change iteratedDerivWithin q (Complex.imCLM ∘ f) s x =
    Complex.imCLM (iteratedDerivWithin q f s x)
  unfold iteratedDerivWithin
  rw [Complex.imCLM.iteratedFDerivWithin_comp_left hf hs hx le_rfl]
  rfl

private theorem ch7Entry1EulerMaclaurin_complex
    (a b : ℤ) (p : ℕ) (f : ℝ → ℂ) (hab : a < b) (hp : 1 ≤ p) (hp1 : p ≠ 1)
    (hdf : ContDiffOn ℝ (p : WithTop ℕ∞) f (Set.Icc (a : ℝ) (b : ℝ))) :
    ∑ n ∈ Finset.Icc a b, f (n : ℝ) =
      (∫ x in (a : ℝ)..(b : ℝ), f x) + (f a + f b) / 2 +
        (∑ k ∈ Finset.Icc 1 (p / 2),
          ((bernoulli (2 * k) : ℝ) : ℂ) / (Nat.factorial (2 * k) : ℝ) *
            (iteratedDerivWithin (2 * k - 1) f (Set.Icc (a : ℝ) (b : ℝ)) b -
              iteratedDerivWithin (2 * k - 1) f (Set.Icc (a : ℝ) (b : ℝ)) a)) +
        ((((-1 : ℝ) ^ (p + 1) / (Nat.factorial p : ℝ) : ℝ) : ℂ) *
          (∫ x in (a : ℝ)..(b : ℝ), (ch7Entry1Kernel p x : ℂ) *
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
  have hR := ch7Entry1EulerMaclaurin_real a b p (fun x => (f x).re) hab hp hdfre
  have hI := ch7Entry1EulerMaclaurin_real a b p (fun x => (f x).im) hab hp hdfim
  have hder_re (q : ℕ) (hq : q ≤ p) (x : ℝ) (hx : x ∈ s) :
      iteratedDerivWithin q (fun y => (f y).re) s x =
        (iteratedDerivWithin q f s x).re :=
    ch7Entry1_iteratedDerivWithin_re q ((hdf x hx).of_le (by exact_mod_cast hq)) hs hx
  have hder_im (q : ℕ) (hq : q ≤ p) (x : ℝ) (hx : x ∈ s) :
      iteratedDerivWithin q (fun y => (f y).im) s x =
        (iteratedDerivWithin q f s x).im :=
    ch7Entry1_iteratedDerivWithin_im q ((hdf x hx).of_le (by exact_mod_cast hq)) hs hx
  have hfint : IntervalIntegrable f volume (a : ℝ) (b : ℝ) :=
    (hdf.continuousOn.mono (by simp [Set.uIcc_of_le habr.le])).intervalIntegrable
  have hdcont : ContinuousOn (iteratedDerivWithin p f s) s :=
    hdf.continuousOn_iteratedDerivWithin le_rfl hs
  have hremint : IntervalIntegrable
      (fun x => (ch7Entry1Kernel p x : ℂ) * iteratedDerivWithin p f s x)
      volume (a : ℝ) (b : ℝ) :=
    (((Complex.continuous_ofReal.comp (ch7Entry1Kernel_continuous hp1)).continuousOn.mul
      hdcont).mono (by simp [s, Set.uIcc_of_le habr.le])).intervalIntegrable
  have hrem_re :
      (∫ x in (a : ℝ)..(b : ℝ), ch7Entry1Kernel p x *
          iteratedDerivWithin p (fun y => (f y).re) s x) =
        (∫ x in (a : ℝ)..(b : ℝ), (ch7Entry1Kernel p x : ℂ) *
          iteratedDerivWithin p f s x).re := by
    calc
      _ = ∫ x in (a : ℝ)..(b : ℝ),
          ((ch7Entry1Kernel p x : ℂ) * iteratedDerivWithin p f s x).re := by
        apply intervalIntegral.integral_congr
        intro x hx
        change ch7Entry1Kernel p x *
            iteratedDerivWithin p (fun y => (f y).re) s x =
          ((ch7Entry1Kernel p x : ℂ) * iteratedDerivWithin p f s x).re
        rw [hder_re p le_rfl x (by simpa [s, Set.uIcc_of_le habr.le] using hx)]
        simp
      _ = _ := intervalIntegral.intervalIntegral_re hremint
  have hrem_im :
      (∫ x in (a : ℝ)..(b : ℝ), ch7Entry1Kernel p x *
          iteratedDerivWithin p (fun y => (f y).im) s x) =
        (∫ x in (a : ℝ)..(b : ℝ), (ch7Entry1Kernel p x : ℂ) *
          iteratedDerivWithin p f s x).im := by
    calc
      _ = ∫ x in (a : ℝ)..(b : ℝ),
          ((ch7Entry1Kernel p x : ℂ) * iteratedDerivWithin p f s x).im := by
        apply intervalIntegral.integral_congr
        intro x hx
        change ch7Entry1Kernel p x *
            iteratedDerivWithin p (fun y => (f y).im) s x =
          ((ch7Entry1Kernel p x : ℂ) * iteratedDerivWithin p f s x).im
        rw [hder_im p le_rfl x (by simpa [s, Set.uIcc_of_le habr.le] using hx)]
        simp
      _ = _ := intervalIntegral.intervalIntegral_im hremint
  have hf_re : (∫ x in (a : ℝ)..(b : ℝ), f x).re =
      ∫ x in (a : ℝ)..(b : ℝ), (f x).re := by
    exact (intervalIntegral.intervalIntegral_re hfint).symm
  have hf_im : (∫ x in (a : ℝ)..(b : ℝ), f x).im =
      ∫ x in (a : ℝ)..(b : ℝ), (f x).im := by
    exact (intervalIntegral.intervalIntegral_im hfint).symm
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

private theorem ch7Entry1_sum_int_eq_powerSum (r : ℂ) (n : ℕ) :
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

private theorem ch7Entry1_sum_Icc_eq_range {M : Type*} [AddCommMonoid M]
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

private noncomputable def ch7Entry1Tail (N : ℕ) (r : ℂ) (n : ℕ) : ℂ :=
  ∫ x : ℝ in Set.Ioi (n : ℝ),
    (x : ℂ) ^ (r - (2 * N + 1 : ℕ)) * (ch7Entry1Kernel (2 * N + 1) x : ℂ)

private noncomputable def ch7Entry1RemainderFactor (N : ℕ) (r : ℂ) : ℂ :=
  chapter7FallingGammaRatio r (2 * N + 1) / ((2 * N + 1).factorial : ℂ)

private noncomputable def ch7Entry1Constant (N : ℕ) (r : ℂ) : ℂ :=
  1 / 2 - 1 / (r + 1) - ∑ j ∈ Finset.range N, chapter7Entry1Term r 1 j +
    ch7Entry1RemainderFactor N r * ch7Entry1MellinIntegral N r

private theorem ch7Entry1_intervalIntegral_eq_mellin_sub_tail
    (N : ℕ) (hN : 0 < N) (r : ℂ) (hu : r.re < 2 * N) (n : ℕ) (hn : 1 < n) :
    (∫ x : ℝ in (1 : ℝ)..(n : ℝ),
        (x : ℂ) ^ (r - (2 * N + 1 : ℕ)) *
          (ch7Entry1Kernel (2 * N + 1) x : ℂ)) =
      ch7Entry1MellinIntegral N r - ch7Entry1Tail N r n := by
  let g : ℝ → ℂ := fun x => (x : ℂ) ^ (r - (2 * N + 1 : ℕ)) *
    (ch7Entry1Kernel (2 * N + 1) x : ℂ)
  have hIoi : IntegrableOn g (Set.Ioi 1) := ch7Entry1Tail_integrable N hN r hu
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
    _ = ch7Entry1MellinIntegral N r - ch7Entry1Tail N r n := by
      rw [ch7Entry1MellinIntegral_eq_integral N hN r]
      rfl

private theorem ch7Entry1_eulerMaclaurin_raw
    (r : ℂ) (N n : ℕ) (hr : r ≠ -1) (hN : 0 < N) (hu : r.re < 2 * N)
    (hn : 1 < n) :
    chapter7PowerSum r n =
      (chapter7NatCpow n (r + 1) - 1) / (r + 1) +
        (1 + chapter7NatCpow n r) / 2 +
        (∑ k ∈ Finset.Icc 1 N,
          (((bernoulli (2 * k) : ℚ) : ℂ) / ((2 * k).factorial : ℂ)) *
            chapter7FallingGammaRatio r (2 * k - 1) *
              (chapter7NatCpow n (r - (2 * k : ℕ) + 1) - 1)) +
        ch7Entry1RemainderFactor N r *
          (ch7Entry1MellinIntegral N r - ch7Entry1Tail N r n) := by
  let p := 2 * N + 1
  have hp : 1 ≤ p := by simp [p]
  have hp1 : p ≠ 1 := by omega
  have hab : (1 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  have hdf : ContDiffOn ℝ (p : WithTop ℕ∞) (fun x : ℝ => (x : ℂ) ^ r)
      (Set.Icc (1 : ℝ) (n : ℝ)) := ch7Entry1_cpow_contDiffOn r p n
  have hem := ch7Entry1EulerMaclaurin_complex (1 : ℤ) (n : ℤ) p
    (fun x : ℝ => (x : ℂ) ^ r) hab hp hp1
      (by simpa only [Int.cast_one, Int.cast_natCast] using hdf)
  simp only [Int.cast_one, Int.cast_natCast] at hem
  rw [ch7Entry1_sum_int_eq_powerSum r n] at hem
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
    rw [ch7Entry1_iteratedDerivWithin_cpow r (2 * k - 1) n hn
        (by exact ⟨by exact_mod_cast hn.le, le_rfl⟩),
      ch7Entry1_iteratedDerivWithin_cpow r (2 * k - 1) n hn
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
      (∫ x : ℝ in (1 : ℝ)..(n : ℝ), (ch7Entry1Kernel p x : ℂ) *
        iteratedDerivWithin p (fun y : ℝ => (y : ℂ) ^ r)
          (Set.Icc (1 : ℝ) (n : ℝ)) x) =
      chapter7FallingGammaRatio r p *
        (ch7Entry1MellinIntegral N r - ch7Entry1Tail N r n) := by
    calc
      _ = ∫ x : ℝ in (1 : ℝ)..(n : ℝ), chapter7FallingGammaRatio r p *
          ((x : ℂ) ^ (r - (p : ℕ)) * (ch7Entry1Kernel p x : ℂ)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        change (ch7Entry1Kernel p x : ℂ) *
            iteratedDerivWithin p (fun y : ℝ => (y : ℂ) ^ r)
              (Set.Icc (1 : ℝ) (n : ℝ)) x =
          chapter7FallingGammaRatio r p *
            ((x : ℂ) ^ (r - (p : ℕ)) * (ch7Entry1Kernel p x : ℂ))
        have hx' : x ∈ Set.Icc (1 : ℝ) (n : ℝ) := by
          have hle : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.le
          rcases Set.mem_uIcc.mp hx with hx | hx
          · exact hx
          · exact ⟨hle.trans hx.1, hx.2.trans hle⟩
        rw [ch7Entry1_iteratedDerivWithin_cpow r p n hn hx']
        ring
      _ = chapter7FallingGammaRatio r p *
          (∫ x : ℝ in (1 : ℝ)..(n : ℝ),
            (x : ℂ) ^ (r - (p : ℕ)) * (ch7Entry1Kernel p x : ℂ)) :=
        intervalIntegral.integral_const_mul _ _
      _ = _ := by
        rw [show p = 2 * N + 1 by rfl,
          ch7Entry1_intervalIntegral_eq_mellin_sub_tail N hN r hu n hn]
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
            (ch7Entry1MellinIntegral N r - ch7Entry1Tail N r n))) =
        ch7Entry1RemainderFactor N r *
          (ch7Entry1MellinIntegral N r - ch7Entry1Tail N r n) := by
    rw [hsign]
    simp only [one_div]
    unfold ch7Entry1RemainderFactor
    rw [show p = 2 * N + 1 by rfl]
    push_cast
    ring
  rw [hlast] at hem
  exact hem

private theorem ch7Entry1_exact_expansion
    (r : ℂ) (N n : ℕ) (hr : r ≠ -1) (hN : 0 < N) (hu : r.re < 2 * N)
    (hn : 1 < n) :
    chapter7PowerSum r n =
      ch7Entry1Constant N r + chapter7NatCpow n (r + 1) / (r + 1) +
        chapter7NatCpow n r / 2 +
        ∑ j ∈ Finset.range N, chapter7Entry1Term r n j -
          ch7Entry1RemainderFactor N r * ch7Entry1Tail N r n := by
  have hraw := ch7Entry1_eulerMaclaurin_raw r N n hr hN hu hn
  have hsum :
      (∑ k ∈ Finset.Icc 1 N,
        (((bernoulli (2 * k) : ℚ) : ℂ) / ((2 * k).factorial : ℂ)) *
          chapter7FallingGammaRatio r (2 * k - 1) *
            (chapter7NatCpow n (r - (2 * k : ℕ) + 1) - 1)) =
      (∑ j ∈ Finset.range N, chapter7Entry1Term r n j) -
        ∑ j ∈ Finset.range N, chapter7Entry1Term r 1 j := by
    rw [ch7Entry1_sum_Icc_eq_range]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [chapter7Entry1Term]
    simp only [ch7Entry1NatCpow_one]
    have he : r - ((2 * (j + 1) : ℕ) : ℂ) + 1 =
        r - ((2 * j + 2 : ℕ) : ℂ) + 1 := by
      push_cast
      ring
    rw [he]
    ring
  rw [hsum] at hraw
  unfold ch7Entry1Constant
  linear_combination hraw

private theorem ch7Entry1NatCpow_tendsto_zero (s : ℂ) (hs : s.re < 0) :
    Tendsto (fun n : ℕ => chapter7NatCpow n s) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := (tendsto_rpow_neg_atTop (by linarith : 0 < -s.re)).comp
    tendsto_natCast_atTop_atTop
  convert h using 1
  funext n
  cases n with
  | zero =>
      have hs0 : s ≠ 0 := by
        intro h0
        subst s
        norm_num at hs
      dsimp only [chapter7NatCpow, Function.comp_apply, Nat.cast_zero, neg_neg]
      norm_num only [Nat.cast_zero, neg_neg]
      have hz : Complex.cpow 0 s = 0 := by simp [Complex.cpow_def, hs0]
      rw [hz, norm_zero, Real.zero_rpow hs.ne]
  | succ n =>
      rw [ch7Entry1NatCpow_norm_of_pos (Nat.succ_pos n)]
      simp

private theorem ch7Entry1PowerSum_tendsto_zeta (r : ℂ) (hr : r.re < -1) :
    Tendsto (chapter7PowerSum r) atTop (𝓝 (riemannZeta (-r))) := by
  have hs : 1 < (-r).re := by
    change 1 < -r.re
    linarith
  let f : ℕ → ℂ := fun n => 1 / (n + 1 : ℂ) ^ (-r)
  have hfsum : Summable f := by
    let g : ℕ → ℂ := fun k => 1 / (k : ℂ) ^ (-r)
    have hfg : f = fun n => g (n + 1) := by
      funext n
      change 1 / (n + 1 : ℂ) ^ (-r) = 1 / ((n + 1 : ℕ) : ℂ) ^ (-r)
      rw [Nat.cast_add, Nat.cast_one]
    rw [hfg]
    exact (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs)
  have hf : HasSum f (riemannZeta (-r)) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    exact hfsum.hasSum
  have heq (n : ℕ) : f n = chapter7NatCpow (n + 1) r := by
    dsimp [f, chapter7NatCpow]
    rw [Complex.cpow_neg]
    simp only [one_div, inv_inv]
    simp only [Nat.cast_add, Nat.cast_one]
  have hsum : HasSum (fun n => chapter7NatCpow (n + 1) r) (riemannZeta (-r)) :=
    hf.congr_fun fun n => (heq n).symm
  refine hsum.tendsto_sum_nat.congr' (Eventually.of_forall fun n => ?_)
  unfold chapter7PowerSum
  exact (ch7Entry1_sum_Icc_eq_range n (chapter7NatCpow · r)).symm

private theorem ch7Entry1Tail_tendsto_zero (N : ℕ) (r : ℂ) :
    Tendsto (ch7Entry1Tail N r) atTop (𝓝 0) := by
  unfold ch7Entry1Tail
  exact MeasureTheory.tendsto_integral_Ioi_zero tendsto_natCast_atTop_atTop

private theorem ch7Entry1Term_tendsto_zero (r : ℂ) (j : ℕ) (hr : r.re < -1) :
    Tendsto (fun n : ℕ => chapter7Entry1Term r n j) atTop (𝓝 0) := by
  have he : (r - (2 * (j + 1) : ℕ) + 1).re < 0 := by
    norm_num [Nat.cast_add, Nat.cast_mul]
    linarith
  have hp := ch7Entry1NatCpow_tendsto_zero (r - (2 * (j + 1) : ℕ) + 1) he
  have ht : Tendsto (fun n : ℕ =>
      ((((bernoulli (2 * (j + 1)) : ℚ) : ℂ) / ((2 * (j + 1)).factorial : ℂ)) *
        chapter7FallingGammaRatio r (2 * (j + 1) - 1)) *
          chapter7NatCpow n (r - (2 * (j + 1) : ℕ) + 1)) atTop
      (𝓝 (((((bernoulli (2 * (j + 1)) : ℚ) : ℂ) / ((2 * (j + 1)).factorial : ℂ)) *
        chapter7FallingGammaRatio r (2 * (j + 1) - 1)) * 0)) :=
    tendsto_const_nhds.mul hp
  simpa only [chapter7Entry1Term, mul_zero] using ht

private theorem ch7Entry1Terms_tendsto_zero (r : ℂ) (N : ℕ) (hr : r.re < -1) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range N, chapter7Entry1Term r n j)
      atTop (𝓝 0) := by
  simpa only [Finset.sum_const_zero] using
    tendsto_finsetSum (Finset.range N) (fun j _ => ch7Entry1Term_tendsto_zero r j hr)

private theorem ch7Entry1Constant_eq_zeta_of_re_lt_neg_one
    (N : ℕ) (hN : 0 < N) (r : ℂ) (hr : r.re < -1) :
    ch7Entry1Constant N r = riemannZeta (-r) := by
  have hrn : r ≠ -1 := by
    intro h
    subst r
    norm_num at hr
  have hu : r.re < 2 * N := by
    have : (0 : ℝ) < 2 * N := by positivity
    linarith
  have hpow1 : Tendsto (fun n : ℕ => chapter7NatCpow n (r + 1) / (r + 1))
      atTop (𝓝 0) := by
    have h := ch7Entry1NatCpow_tendsto_zero (r + 1) (by
      norm_num
      linarith)
    simpa using h.div_const (r + 1)
  have hpow0 : Tendsto (fun n : ℕ => chapter7NatCpow n r / 2) atTop (𝓝 0) := by
    simpa using (ch7Entry1NatCpow_tendsto_zero r (by linarith)).div_const 2
  have hterms := ch7Entry1Terms_tendsto_zero r N hr
  have htail := ch7Entry1Tail_tendsto_zero N r
  have hrem : Tendsto
      (fun n : ℕ => ch7Entry1RemainderFactor N r * ch7Entry1Tail N r n)
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul htail
  have hrhs : Tendsto (fun n : ℕ =>
      ch7Entry1Constant N r + chapter7NatCpow n (r + 1) / (r + 1) +
        chapter7NatCpow n r / 2 +
        ∑ j ∈ Finset.range N, chapter7Entry1Term r n j -
          ch7Entry1RemainderFactor N r * ch7Entry1Tail N r n)
      atTop (𝓝 (ch7Entry1Constant N r)) := by
    simpa using (((tendsto_const_nhds.add hpow1).add hpow0).add hterms).sub hrem
  have heq : ∀ᶠ n : ℕ in atTop,
      (ch7Entry1Constant N r + chapter7NatCpow n (r + 1) / (r + 1) +
        chapter7NatCpow n r / 2 +
        ∑ j ∈ Finset.range N, chapter7Entry1Term r n j -
          ch7Entry1RemainderFactor N r * ch7Entry1Tail N r n) =
        chapter7PowerSum r n := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    exact (ch7Entry1_exact_expansion r N n hrn hN hu hn).symm
  have hconst : Tendsto (chapter7PowerSum r) atTop (𝓝 (ch7Entry1Constant N r)) :=
    hrhs.congr' heq
  exact tendsto_nhds_unique hconst (ch7Entry1PowerSum_tendsto_zeta r hr)

private theorem ch7Entry1Falling_differentiable (q : ℕ) :
    Differentiable ℂ (fun r => chapter7FallingGammaRatio r q) := by
  unfold chapter7FallingGammaRatio
  fun_prop

private theorem ch7Entry1Term_one_differentiableAt (j : ℕ) (r : ℂ) :
    DifferentiableAt ℂ (fun z => chapter7Entry1Term z 1 j) r := by
  simpa only [chapter7Entry1Term, ch7Entry1NatCpow_one, mul_one] using
    (ch7Entry1Falling_differentiable (2 * (j + 1) - 1)).differentiableAt.const_mul
      (((bernoulli (2 * (j + 1)) : ℚ) : ℂ) / ((2 * (j + 1)).factorial : ℂ))

private theorem ch7Entry1Constant_differentiableAt
    (N : ℕ) (hN : 0 < N) (r : ℂ) (hr : r ≠ -1) (hu : r.re < 2 * N) :
    DifferentiableAt ℂ (ch7Entry1Constant N) r := by
  have hm := ch7Entry1MellinIntegral_differentiableAt N hN r hu
  have hr1 : r + 1 ≠ 0 := by
    intro h
    apply hr
    linear_combination h
  have hinv : DifferentiableAt ℂ (fun z : ℂ => 1 / (z + 1)) r := by
    fun_prop
  have hsum : DifferentiableAt ℂ
      (fun z => ∑ j ∈ Finset.range N, chapter7Entry1Term z 1 j) r :=
    by
      convert DifferentiableAt.sum (u := Finset.range N)
        (fun j _ => ch7Entry1Term_one_differentiableAt j r) using 1
      funext z
      simp only [Finset.sum_apply]
  have hfactor : DifferentiableAt ℂ (ch7Entry1RemainderFactor N) r := by
    unfold ch7Entry1RemainderFactor
    exact (ch7Entry1Falling_differentiable (2 * N + 1)).differentiableAt.div_const _
  unfold ch7Entry1Constant
  exact (((differentiableAt_const (c := (1 / 2 : ℂ))).sub hinv).sub hsum).add
    (hfactor.mul hm)

private theorem ch7Entry1Zeta_differentiableAt (r : ℂ) (hr : r ≠ -1) :
    DifferentiableAt ℂ (fun z => riemannZeta (-z)) r := by
  have hnr : -r ≠ 1 := by
    intro h
    apply hr
    calc
      r = -(-r) := by ring
      _ = -1 := by rw [h]
  exact (differentiableAt_riemannZeta hnr).comp r (by fun_prop)

private theorem ch7Entry1Constant_eq_zeta_on_convex
    (N : ℕ) (hN : 0 < N) (U : Set ℂ) (hUopen : IsOpen U) (hUconv : Convex ℝ U)
    (hUre : ∀ z ∈ U, z.re < 2 * N) (hUne : ∀ z ∈ U, z ≠ -1)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (heq : ch7Entry1Constant N =ᶠ[𝓝 z₀] fun z => riemannZeta (-z)) :
    Set.EqOn (ch7Entry1Constant N) (fun z => riemannZeta (-z)) U := by
  have hf : DifferentiableOn ℂ (ch7Entry1Constant N) U := fun z hz =>
    (ch7Entry1Constant_differentiableAt N hN z (hUne z hz) (hUre z hz)).differentiableWithinAt
  have hg : DifferentiableOn ℂ (fun z => riemannZeta (-z)) U := fun z hz =>
    (ch7Entry1Zeta_differentiableAt z (hUne z hz)).differentiableWithinAt
  exact (hf.analyticOnNhd hUopen).eqOn_of_preconnected_of_eventuallyEq
    (hg.analyticOnNhd hUopen) hUconv.isPreconnected hz₀ heq

private theorem ch7Entry1Constant_eq_zeta
    (N : ℕ) (hN : 0 < N) (r : ℂ) (hr : r ≠ -1) (hu : r.re < 2 * N) :
    ch7Entry1Constant N r = riemannZeta (-r) := by
  let Uu : Set ℂ := {z | z.re < (2 * N : ℝ)} ∩ {z | 0 < z.im}
  have hUuOpen : IsOpen Uu := by
    dsimp [Uu]
    exact (isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hUuConv : Convex ℝ Uu := by
    dsimp [Uu]
    exact (convex_halfSpace_re_lt (2 * N : ℝ)).inter (convex_halfSpace_im_gt 0)
  have hUuNe : ∀ z ∈ Uu, z ≠ -1 := by
    intro z hz he
    subst z
    norm_num [Uu] at hz
  let zu : ℂ := -2 + Complex.I
  have hzu : zu ∈ Uu := by
    dsimp [zu, Uu]
    constructor
    · norm_num
      have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      linarith
    · norm_num
  have heventu : ch7Entry1Constant N =ᶠ[𝓝 zu] fun z => riemannZeta (-z) := by
    have hbaseOpen : IsOpen {z : ℂ | z.re < -1} :=
      isOpen_lt Complex.continuous_re continuous_const
    have hzbase : zu ∈ {z : ℂ | z.re < -1} := by
      dsimp [zu]
      norm_num
    filter_upwards [hbaseOpen.eventually_mem hzbase] with z hz
    exact ch7Entry1Constant_eq_zeta_of_re_lt_neg_one N hN z hz
  have hequ : Set.EqOn (ch7Entry1Constant N) (fun z => riemannZeta (-z)) Uu :=
    ch7Entry1Constant_eq_zeta_on_convex N hN Uu hUuOpen hUuConv
      (fun _ hz => hz.1) hUuNe hzu heventu
  let Ul : Set ℂ := {z | z.re < (2 * N : ℝ)} ∩ {z | z.im < 0}
  have hUlOpen : IsOpen Ul := by
    dsimp [Ul]
    exact (isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hUlConv : Convex ℝ Ul := by
    dsimp [Ul]
    exact (convex_halfSpace_re_lt (2 * N : ℝ)).inter (convex_halfSpace_im_lt 0)
  have hUlNe : ∀ z ∈ Ul, z ≠ -1 := by
    intro z hz he
    subst z
    norm_num [Ul] at hz
  let zl : ℂ := -2 - Complex.I
  have hzl : zl ∈ Ul := by
    dsimp [zl, Ul]
    constructor
    · norm_num
      have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      linarith
    · norm_num
  have heventl : ch7Entry1Constant N =ᶠ[𝓝 zl] fun z => riemannZeta (-z) := by
    have hbaseOpen : IsOpen {z : ℂ | z.re < -1} :=
      isOpen_lt Complex.continuous_re continuous_const
    have hzbase : zl ∈ {z : ℂ | z.re < -1} := by
      dsimp [zl]
      norm_num
    filter_upwards [hbaseOpen.eventually_mem hzbase] with z hz
    exact ch7Entry1Constant_eq_zeta_of_re_lt_neg_one N hN z hz
  have heql : Set.EqOn (ch7Entry1Constant N) (fun z => riemannZeta (-z)) Ul :=
    ch7Entry1Constant_eq_zeta_on_convex N hN Ul hUlOpen hUlConv
      (fun _ hz => hz.1) hUlNe hzl heventl
  let Ud : Set ℂ := {z | (-1 : ℝ) < z.re} ∩ {z | z.re < (2 * N : ℝ)}
  have hUdOpen : IsOpen Ud := by
    dsimp [Ud]
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hUdConv : Convex ℝ Ud := by
    dsimp [Ud]
    exact (convex_halfSpace_re_gt (-1)).inter (convex_halfSpace_re_lt (2 * N : ℝ))
  have hUdNe : ∀ z ∈ Ud, z ≠ -1 := by
    intro z hz he
    subst z
    norm_num [Ud] at hz
  have hIu : Complex.I ∈ Uu := by
    dsimp [Uu]
    constructor
    · norm_num
      positivity
    · norm_num
  have hId : Complex.I ∈ Ud := by
    dsimp [Ud]
    constructor
    · norm_num
    · norm_num
      positivity
  have heventd : ch7Entry1Constant N =ᶠ[𝓝 Complex.I] fun z => riemannZeta (-z) :=
    (hUuOpen.eventually_mem hIu).mono fun z hz => hequ hz
  have heqd : Set.EqOn (ch7Entry1Constant N) (fun z => riemannZeta (-z)) Ud :=
    ch7Entry1Constant_eq_zeta_on_convex N hN Ud hUdOpen hUdConv
      (fun _ hz => hz.2) hUdNe hId heventd
  rcases lt_trichotomy r.re (-1) with hlt | hre | hgt
  · exact ch7Entry1Constant_eq_zeta_of_re_lt_neg_one N hN r hlt
  · have him0 : r.im ≠ 0 := by
      intro him
      apply hr
      apply Complex.ext
      · simpa using hre
      · simp [him]
    rcases lt_or_gt_of_ne him0 with him | him
    · exact heql ⟨hu, him⟩
    · exact hequ ⟨hu, him⟩
  · exact heqd ⟨hgt, hu⟩

private theorem ch7Entry1Tail_isBigO
    (N : ℕ) (hN : 0 < N) (r : ℂ) (hu : r.re < 2 * N) :
    IsBigO atTop (ch7Entry1Tail N r)
      (fun n : ℕ => Real.rpow (n : ℝ) (r.re - 2 * (N : ℝ))) := by
  let a : ℝ := r.re - 2 * (N : ℝ) - 1
  have ha : a < -1 := by
    dsimp [a]
    linarith
  have hab : a + 1 = r.re - 2 * (N : ℝ) := by
    dsimp [a]
    ring
  have hden : 0 < 2 * (N : ℝ) - r.re := by linarith
  obtain ⟨C, hC⟩ := ch7Entry1Kernel_norm_le N hN
  let D : ℝ := C / (2 * (N : ℝ) - r.re)
  refine Asymptotics.isBigO_iff.mpr ⟨D, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hg : Integrable (fun x : ℝ => C * x ^ a)
      (volume.restrict (Set.Ioi (n : ℝ))) :=
    (integrableOn_Ioi_rpow_of_lt ha hnpos).const_mul C
  have hexp : (r - (2 * N + 1 : ℕ)).re = a := by
    dsimp [a]
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring
  have hpoint (x : ℝ) (hx : x ∈ Set.Ioi (n : ℝ)) :
      ‖(x : ℂ) ^ (r - (2 * N + 1 : ℕ)) *
          (ch7Entry1Kernel (2 * N + 1) x : ℂ)‖ ≤ C * x ^ a := by
    have hxpos : 0 < x := hnpos.trans hx
    calc
      ‖(x : ℂ) ^ (r - (2 * N + 1 : ℕ)) *
          (ch7Entry1Kernel (2 * N + 1) x : ℂ)‖ =
          x ^ a * ‖ch7Entry1Kernel (2 * N + 1) x‖ := by
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos, hexp,
          Complex.norm_real]
      _ ≤ x ^ a * C :=
        mul_le_mul_of_nonneg_left (hC x) (Real.rpow_nonneg hxpos.le a)
      _ = C * x ^ a := by ring
  have hnorm :
      ‖∫ x : ℝ in Set.Ioi (n : ℝ),
          (x : ℂ) ^ (r - (2 * N + 1 : ℕ)) *
            (ch7Entry1Kernel (2 * N + 1) x : ℂ)‖ ≤
        ∫ x : ℝ in Set.Ioi (n : ℝ), C * x ^ a := by
    exact MeasureTheory.norm_integral_le_of_norm_le hg
      ((ae_restrict_mem measurableSet_Ioi).mono hpoint)
  unfold ch7Entry1Tail
  calc
    ‖∫ x : ℝ in Set.Ioi (n : ℝ),
        (x : ℂ) ^ (r - (2 * N + 1 : ℕ)) *
          (ch7Entry1Kernel (2 * N + 1) x : ℂ)‖ ≤
        ∫ x : ℝ in Set.Ioi (n : ℝ), C * x ^ a := hnorm
    _ = C * (∫ x : ℝ in Set.Ioi (n : ℝ), x ^ a) := by
      rw [MeasureTheory.integral_const_mul]
    _ = C * (-(n : ℝ) ^ (a + 1) / (a + 1)) := by
      rw [integral_Ioi_rpow_of_lt ha hnpos]
    _ = D * ‖Real.rpow (n : ℝ) (r.re - 2 * (N : ℝ))‖ := by
      rw [Real.rpow_eq_pow, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hnpos.le _), hab]
      dsimp [D]
      have hb0 : r.re - 2 * (N : ℝ) ≠ 0 := by linarith
      field_simp [hb0, ne_of_gt hden]
      ring

/-- **Ramanujan's asymptotic expansion of power sums.** Let $r \in \mathbb{C}$ with $r \ne -1$,
and let $N$ be a positive integer with $\mathrm{Re}\, r < 2N$. For natural $n$ put
$A_N(n) = \zeta(-r) + \frac{n^{r+1}}{r+1} + \frac{n^r}{2} + \sum_{k=1}^{N} T_k(n)$, where
$T_k(n) = \frac{B_{2k}}{(2k)!}\, r(r-1)\cdots(r-2k+2)\, n^{r-2k+1}$ (a product of $2k - 1$
factors), $\zeta$ is the Riemann zeta function, $B_{2k}$ are the Bernoulli numbers and complex
powers are principal. Then $\sum_{k=1}^{n} k^r - A_N(n) = O(n^{\mathrm{Re}\, r - 2N})$ as
$n \to \infty$.

Proof: Euler--Maclaurin gives the expansion with an integrable periodic-kernel tail. The constant is
identified with the Riemann zeta function first in its convergent half-plane, then everywhere needed
by analytic continuation.

Proves `Wanted` entry `ramanujan_part1_ch7_entry1_powersum`.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 7, Entry 1.
-/
theorem ramanujan_part1_ch7_entry1_powersum
    (r : ℂ) (N : ℕ) (hr : r ≠ -1) (hN : 0 < N) (hu : r.re < 2 * N) :
    IsBigO atTop
      (fun n : ℕ => chapter7PowerSum r n - chapter7Entry1Approx r N n)
      (fun n : ℕ => Real.rpow (n : ℝ) (r.re - 2 * (N : ℝ))) := by
  have htail := (ch7Entry1Tail_isBigO N hN r hu).const_mul_left
    (ch7Entry1RemainderFactor N r)
  have hrem := htail.neg_left
  refine hrem.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [eventually_gt_atTop 1] with n hn
  rw [ch7Entry1_exact_expansion r N n hr hN hu hn,
    ch7Entry1Constant_eq_zeta N hN r hr hu]
  unfold chapter7Entry1Approx
  ring

end

end Entry1Powersum

end MathlibExt.Analysis.Ramanujan.Part1Ch7
