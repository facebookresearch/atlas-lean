/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Numerical.Certified
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open MathlibExt.Analysis.Numerical.Certified

/-! ### Interval certificates -/

-- `e` is certified in `[2718/1000, 2719/1000]`, of width `1/1000` (at most the required `1/100`).
example : expOneInterval = ⟨2718 / 1000, 2719 / 1000⟩ ∧ expOneInterval.width = 1 / 1000 := by
  refine ⟨expOneInterval_eq, ?_⟩
  rw [expOneInterval_eq, RatInterval.width]
  norm_num

example : Real.exp 1 ∈ Set.Icc (2718 / 1000 : ℝ) (2719 / 1000) := by
  have h := encloses_expOneInterval
  rw [expOneInterval_eq] at h
  norm_num [RatInterval.Encloses] at h ⊢
  exact h

-- Before rounding, the eight-term Taylor enclosure of `e` has width below `1/10000`.
example : (expInterval 1 8).width ≤ 1 / 10000 := by
  rw [expInterval_width]
  norm_num [expRemainderBound, Nat.factorial]

-- A negative rational point: `exp (-1)` is certified in `[367/1000, 368/1000]`.
example : ((expInterval (-1) 8).roundOut 3).Encloses (Real.exp (-1)) ∧
    (expInterval (-1) 8).roundOut 3 = ⟨367 / 1000, 368 / 1000⟩ := by
  refine ⟨?_, ?_⟩
  · have h := (encloses_expInterval (q := -1) (by norm_num) (n := 8) (by norm_num)).roundOut 3
    rwa [Rat.cast_neg, Rat.cast_one] at h
  · norm_num [expInterval, expPartialSum, expRemainderBound, Finset.sum_range_succ,
      Nat.factorial, RatInterval.roundOut]

-- Outward rounding moves the endpoints of `[1/3, 2/3]` down and up to `[33/100, 67/100]`, and
-- those of `[-1/3, -1/3]` to `[-34/100, -33/100]`.
example : (⟨1 / 3, 2 / 3⟩ : RatInterval).roundOut 2 = ⟨33 / 100, 67 / 100⟩ ∧
    (⟨-1 / 3, -1 / 3⟩ : RatInterval).roundOut 2 = ⟨-34 / 100, -33 / 100⟩ := by
  norm_num [RatInterval.roundOut]

-- Rounding `e` outward to three decimals widens its Taylor enclosure by at most `2/1000`.
example : expOneInterval.width ≤ (expInterval 1 8).width + 2 / 10 ^ 3 :=
  RatInterval.width_roundOut_le _ _

private lemma sqrt_two_encloses :
    (⟨1414 / 1000, 1415 / 1000⟩ : RatInterval).Encloses (Real.sqrt 2) := by
  have h := encloses_sqrt (q := 2) (a := 1414 / 1000) (b := 1415 / 1000) (by norm_num)
    (by norm_num) (by norm_num)
  rwa [Rat.cast_ofNat] at h

-- `√2` is certified in `[1414/1000, 1415/1000]` by the exact checks `1.414² ≤ 2 ≤ 1.415²`.
example : (1414 / 1000 : ℝ) ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ 1415 / 1000 := by
  have h := sqrt_two_encloses
  norm_num [RatInterval.Encloses] at h ⊢
  exact h

-- Interval arithmetic: enclosures of `e + √2`, `-e` and `e - √2`; the width of the difference is
-- the sum `2/1000` of the two widths.
example : (expOneInterval.add ⟨1414 / 1000, 1415 / 1000⟩).Encloses (Real.exp 1 + Real.sqrt 2) ∧
    expOneInterval.neg.Encloses (-Real.exp 1) ∧
    (expOneInterval.sub ⟨1414 / 1000, 1415 / 1000⟩).Encloses (Real.exp 1 - Real.sqrt 2) :=
  ⟨encloses_expOneInterval.add sqrt_two_encloses, encloses_expOneInterval.neg,
    encloses_expOneInterval.sub sqrt_two_encloses⟩

example : expOneInterval.add ⟨1414 / 1000, 1415 / 1000⟩ = ⟨4132 / 1000, 4134 / 1000⟩ ∧
    expOneInterval.neg = ⟨-(2719 / 1000), -(2718 / 1000)⟩ ∧
    (expOneInterval.sub ⟨1414 / 1000, 1415 / 1000⟩).width = 2 / 1000 := by
  rw [expOneInterval_eq]
  norm_num [RatInterval.add, RatInterval.neg, RatInterval.sub, RatInterval.width]

-- Sign certificates: `2 ≤ e ≤ 3`, read off one endpoint of the enclosures of `e - 2` and `e - 3`.
example : 2 ≤ Real.exp 1 ∧ Real.exp 1 ≤ 3 := by
  have h₂ := (encloses_expOneInterval.sub (RatInterval.encloses_ofRat 2)).nonneg (by
    rw [expOneInterval_eq]
    norm_num)
  have h₃ := (encloses_expOneInterval.sub (RatInterval.encloses_ofRat 3)).nonpos (by
    rw [expOneInterval_eq]
    norm_num)
  push_cast at h₂ h₃
  constructor <;> linarith

/-! ### Root bracketing and uniqueness -/

private lemma add_exp_sub_two_one : 0 ≤ (1 : ℝ) + Real.exp 1 - 2 := by
  linarith [Real.add_one_le_exp 1]

-- Bracketing: `x + exp x - 2` is `-1` at `0` and nonnegative at `1`, so it has a root in `[0, 1]`.
example : ∃ c ∈ Set.Icc (0 : ℝ) 1, c + Real.exp c - 2 = 0 :=
  exists_root_of_nonpos_of_nonneg (f := fun x : ℝ => x + Real.exp x - 2) (by norm_num)
    (by fun_prop) (by norm_num) add_exp_sub_two_one

-- Sign-flipped bracketing: `cos 1 > 0 > cos 2`, so `cos` has a root in `[1, 2]`.
example : ∃ c ∈ Set.Icc (1 : ℝ) 2, Real.cos c = 0 :=
  exists_root_of_nonneg_of_nonpos (by norm_num) Real.continuous_cos.continuousOn
    Real.cos_one_pos.le Real.cos_two_neg.le

-- Strictly decreasing case: `cos` has exactly one root in `[1, 2]`.
example : ∃! c, c ∈ Set.Icc (1 : ℝ) 2 ∧ Real.cos c = 0 :=
  existsUnique_root_of_strictAntiOn (by norm_num) Real.continuous_cos.continuousOn
    (Real.strictAntiOn_cos.mono (Set.Icc_subset_Icc (by norm_num) Real.two_le_pi))
    Real.cos_one_pos.le Real.cos_two_neg.le

private lemma cube_sub_two_strictMonoOn :
    StrictMonoOn (fun x : ℝ => x ^ 3 - 2) (Set.Icc 1 2) := by
  intro x hx y _ hxy
  have := pow_lt_pow_left₀ hxy (by linarith [hx.1]) (by norm_num : 3 ≠ 0)
  simp only
  linarith

-- Bracketing and uniqueness: `x³ - 2` has exactly one root in `[1, 2]`.
example : ∃! c, c ∈ Set.Icc (1 : ℝ) 2 ∧ c ^ 3 - 2 = 0 :=
  existsUnique_root_of_strictMonoOn (f := fun x : ℝ => x ^ 3 - 2) (by norm_num) (by fun_prop)
    cube_sub_two_strictMonoOn (by norm_num) (by norm_num)

-- Uniqueness alone needs only strict monotonicity: two solutions of `x + exp x = 2` coincide.
example {x y : ℝ} (hx : x + Real.exp x - 2 = 0) (hy : y + Real.exp y - 2 = 0) : x = y :=
  root_unique_of_strictMonoOn (equilibrium_strictMono.strictMonoOn Set.univ) trivial trivial hx hy

/-! ### Certified bisection -/

-- The recorded run is exact rational arithmetic: ten steps from `[0, 1]` end in
-- `[453/1024, 227/512]`.
example : bisectRun equilibriumDecisions ⟨0, 1⟩ = ⟨453 / 1024, 227 / 512⟩ :=
  bisectRun_equilibriumDecisions

-- The same width from the general theorem: `(1 - 0) / 2 ^ 10`.
example : (bisectRun equilibriumDecisions ⟨0, 1⟩).width = 1 / 2 ^ 10 := by
  rw [bisectRun_width]
  norm_num [equilibriumDecisions, RatInterval.width]

-- Zero steps return the initial bracket, and the empty run is certified.
example (f : ℝ → ℝ) (I : RatInterval) : bisectRun [] I = I ∧ SignCertified f [] I :=
  ⟨rfl, trivial⟩

-- A root at a midpoint certifies both decisions: `x - 1/2` vanishes at the midpoint of `[0, 1]`.
example : SignCertified (fun x : ℝ => x - 1 / 2) [true] ⟨0, 1⟩ ∧
    SignCertified (fun x : ℝ => x - 1 / 2) [false] ⟨0, 1⟩ := by
  norm_num [SignCertified, RatInterval.mid]

-- The certificate is not vacuous: `false` is rejected at the first midpoint `1/2` of `[0, 1]`,
-- where `x + exp x - 2 > 0`.
example : ¬ SignCertified (fun x : ℝ => x + Real.exp x - 2) [false] ⟨0, 1⟩ := by
  have h := (encloses_expInterval (q := 1 / 2) (by norm_num [abs_le]) (n := 6) (by norm_num)).1
  norm_num [expInterval, expPartialSum, expRemainderBound, Finset.sum_range_succ, Nat.factorial,
    abs_of_nonneg] at h
  norm_num [SignCertified, RatInterval.mid]
  linarith

-- Certified decisions always exist: five steps on `[1, 2]` for `x³ - 2` leave a bracket of
-- width `1/32` that encloses a root.
example : ∃ ds : List Bool, ds.length = 5 ∧ (bisectRun ds ⟨1, 2⟩).width = 1 / 32 ∧
    ∃ c, (bisectRun ds ⟨1, 2⟩).Encloses c ∧ c ^ 3 - 2 = 0 := by
  obtain ⟨ds, hlen, hcert⟩ := exists_signCertified (fun x : ℝ => x ^ 3 - 2) 5 ⟨1, 2⟩
  obtain ⟨hw, -, -, hroot⟩ := bisectRun_width_and_root (f := fun x : ℝ => x ^ 3 - 2)
    (a := 1) (b := 2) (by norm_num) (by fun_prop) (by norm_num) (by norm_num) ds hcert
  refine ⟨ds, hlen, ?_, hroot⟩
  rw [hw, hlen]
  norm_num

-- Localization from strict monotonicity: every solution of `x + exp x = 2` in `[0, 1]` lies in
-- the recorded bracket `[453/1024, 227/512]`.
example {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hfx : x + Real.exp x = 2) :
    (⟨453 / 1024, 227 / 512⟩ : RatInterval).Encloses x := by
  have h := encloses_bisectRun_of_strictMonoOn (f := fun x : ℝ => x + Real.exp x - 2)
    (a := 0) (b := 1) (by norm_num) (equilibrium_strictMono.strictMonoOn _) (by norm_num)
    (by simpa using add_exp_sub_two_one) equilibriumDecisions signCertified_equilibrium
    (show x ∈ Set.Icc ((0 : ℚ) : ℝ) ((1 : ℚ) : ℝ) by simpa using hx)
    (show x + Real.exp x - 2 = 0 by linarith)
  rwa [bisectRun_equilibriumDecisions] at h

/-! ### Quadrature and Taylor truncation bounds -/

private lemma exp_le_three {x : ℝ} (hx : x ≤ 1) : Real.exp x ≤ 3 := by
  have h := encloses_expOneInterval.2
  rw [expOneInterval_eq] at h
  have h' : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp.2 hx
  norm_num at h
  linarith

private lemma abs_iteratedDeriv_exp_le {x : ℝ} (hx : |x| ≤ 1) (n : ℕ) :
    ∀ y ∈ Set.uIoo 0 x, |iteratedDeriv n Real.exp y| ≤ 3 := by
  intro y hy
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp, abs_of_pos (Real.exp_pos y)]
  have hy' := Set.uIoo_subset_uIcc_self hy
  rw [Set.mem_uIcc] at hy'
  have hx1 := (abs_le.1 hx).2
  apply exp_le_three
  rcases hy' with ⟨-, h⟩ | ⟨-, h⟩ <;> linarith

-- Trapezoidal rule for `exp` on `[0, 1]` with four subintervals: `|exp''| ≤ 3` on the interval
-- gives error at most `1 ^ 3 * 3 / (12 * 4 ^ 2) = 1/64`.
example : |trapezoidal_error Real.exp 4 0 1| ≤ 1 / 64 := by
  have hζ : ∀ x ∈ Set.uIcc (0 : ℝ) 1, |iteratedDerivWithin 2 Real.exp (Set.uIcc 0 1) x| ≤ 3 := by
    intro x hx
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (by norm_num))
      Real.contDiff_exp.contDiffAt hx, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
      abs_of_pos (Real.exp_pos x)]
    rw [Set.uIcc_of_le (by norm_num)] at hx
    exact exp_le_three hx.2
  have h := abs_trapezoidal_error_le Real.contDiff_exp.contDiffOn hζ (N := 4) (by norm_num)
  norm_num at h
  linarith

-- The Lagrange bound with `n = 0` is the mean value inequality `|exp x - 1| ≤ 3 |x|` for `|x| ≤ 1`.
example {x : ℝ} (hx : |x| ≤ 1) : |Real.exp x - 1| ≤ 3 * |x| := by
  have h := abs_sub_taylorWithinEval_le (f := Real.exp) (x₀ := 0) (x := x) (n := 0)
    Real.contDiff_exp.contDiffOn (abs_iteratedDeriv_exp_le hx (0 + 1))
  simpa [taylor_within_zero_eval] using h

-- Taylor truncation for `exp` at `0` to degree two: `|exp x - (1 + x + x² / 2)| ≤ 3 |x|³ / 6`
-- for `|x| ≤ 1`, from `|exp'''| ≤ 3` between `0` and `x`.
example {x : ℝ} (hx : |x| ≤ 1) : |Real.exp x - (1 + x + x ^ 2 / 2)| ≤ 3 * |x| ^ 3 / 6 := by
  have h := abs_sub_taylor_sum_le (f := Real.exp) (x₀ := 0) (x := x) (n := 2) Real.contDiff_exp
    (abs_iteratedDeriv_exp_le hx (2 + 1))
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDeriv_eq_iterate,
    Real.iter_deriv_exp, Real.exp_zero, sub_zero] at h
  norm_num [Nat.factorial] at h
  convert h using 2
  ring

/-! ### Error budgets -/

-- A Lipschitz model `d ↦ 3 d`: numerical error `1/100` at the measured datum `2`, data
-- uncertainty `1/100`, conditioning constant `3`.
example {dTrue : ℝ} (hdata : |2 - dTrue| ≤ 1 / 100) :
    |(601 / 100 : ℝ) - 3 * dTrue| ≤ 1 / 100 + 3 * (1 / 100) := by
  have hF : LipschitzOnWith 3 (fun d : ℝ => 3 * d) Set.univ := by
    refine LipschitzWith.lipschitzOnWith (LipschitzWith.of_dist_le_mul fun x y => ?_)
    simp only [Real.dist_eq, NNReal.coe_ofNat]
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  have h := abs_sub_le_numerical_add_data_of_lipschitzOnWith hF (approx := 601 / 100)
    (εnum := 1 / 100) trivial trivial (by norm_num) hdata
  simpa using h

-- A small residual alone is not an error bound: `x ↦ x / 1000` has residual `1/1000` at `1`,
-- yet `1` is at distance `1` from the root `0`.
example : ∃ g : ℝ → ℝ, g 0 = 0 ∧ |g 1| ≤ 1 / 1000 ∧ 1 / 1000 < |(1 : ℝ) - 0| :=
  ⟨fun x => x / 1000, by norm_num, by norm_num, by norm_num⟩

-- With the conditioning constant `m = 1/1000` made explicit, the same residual gives the sharp
-- error bound `(1/1000) / (1/1000) = 1`.
example : |(1 : ℝ) - 0| ≤ (1 / 1000) / (1 / 1000) := by
  refine abs_sub_root_le_of_residual (g := fun x : ℝ => x / 1000) (s := Set.univ)
    (by norm_num) (fun y _ z _ => le_of_eq ?_) trivial trivial (by norm_num) (by norm_num)
  rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 1000)]
  ring

/-! ### Provenance capstone -/

private lemma capstone_root_eq :
    equilibriumCapstone.root + Real.exp equilibriumCapstone.root = 2 := by
  have h : equilibriumCapstone.root + Real.exp equilibriumCapstone.root - 2 = 0 :=
    equilibriumCapstone.apply_root_eq_zero
  linarith

-- The record is complete: units, data version, tolerance, the lemmas used, and the recorded
-- exact computation (initial bracket and decisions).
example : equilibriumCapstone.provenance.units = "SI; dimensionless" ∧
    equilibriumCapstone.provenance.dataVersion =
      "exact rational constant c = 2, no measured data" ∧
    equilibriumCapstone.provenance.tolerance = 1 / 1000 ∧
    equilibriumCapstone.provenance.lemmas =
      [``Real.exp_bound, ``intermediate_value_Icc, ``StrictMonoOn.injOn] ∧
    equilibriumCapstone.bracket = ⟨0, 1⟩ ∧ equilibriumCapstone.decisions = equilibriumDecisions :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- The certified enclosure is the tenth bisection bracket: width `1/1024`, midpoint `907/2048`.
example : equilibriumCapstone.enclosure = ⟨453 / 1024, 227 / 512⟩ ∧
    equilibriumCapstone.enclosure.width = 1 / 1024 ∧
    equilibriumCapstone.enclosure.mid = 907 / 2048 := by
  refine ⟨equilibriumCapstone_enclosure, ?_, ?_⟩ <;> rw [equilibriumCapstone_enclosure]
  · norm_num [RatInterval.width]
  · norm_num [RatInterval.mid]

-- The root solves `x + exp x = 2`, is the only solution in `[0, 1]`, and by strict monotonicity
-- the only real solution.
example : equilibriumCapstone.root + Real.exp equilibriumCapstone.root = 2 :=
  capstone_root_eq

example {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hfx : x + Real.exp x = 2) :
    x = equilibriumCapstone.root :=
  equilibriumCapstone.eq_root (show x ∈ Set.Icc ((0 : ℚ) : ℝ) ((1 : ℚ) : ℝ) by simpa using hx)
    (show x + Real.exp x - 2 = 0 by linarith)

example {x : ℝ} (hfx : x + Real.exp x = 2) : x = equilibriumCapstone.root :=
  equilibrium_strictMono.injective (show x + Real.exp x - 2 =
    equilibriumCapstone.root + Real.exp equilibriumCapstone.root - 2 by
    linarith [capstone_root_eq])

-- The reported midpoint `907/2048` is within half the tolerance of the root.
example : |equilibriumCapstone.root - 907 / 2048| ≤ 1 / 2000 := by
  have h := equilibriumCapstone.abs_sub_mid_le
  have htol : equilibriumCapstone.provenance.tolerance = 1 / 1000 := rfl
  rw [equilibriumCapstone_enclosure, htol] at h
  norm_num [RatInterval.mid] at h ⊢
  exact h

-- Uniqueness is only claimed on the initial bracket: `x² - 2` has two real roots, and its positive
-- root `√2` is certified on `[1, 2]` in `[11/8, 23/16]` by four steps.
private noncomputable def sqrtTwoRoot : CertifiedRoot (fun x : ℝ => x ^ 2 - 2) :=
  CertifiedRoot.ofBisection (a := 1) (b := 2) (by norm_num) (by fun_prop)
    (fun x hx y _ hxy => by
      have hx₁ : (1 : ℝ) ≤ x := by exact_mod_cast hx.1
      have := pow_lt_pow_left₀ hxy (by linarith) (by norm_num : 2 ≠ 0)
      linarith)
    (by norm_num) (by norm_num) [true, false, false, true]
    (by norm_num [SignCertified, bisectStep, RatInterval.mid])
    { units := "SI; dimensionless"
      dataVersion := "exact rational constant 2"
      tolerance := 1 / 16
      lemmas := [``intermediate_value_Icc, ``StrictMonoOn.injOn] }
    (by norm_num)

example : sqrtTwoRoot.enclosure = ⟨11 / 8, 23 / 16⟩ ∧ sqrtTwoRoot.root = Real.sqrt 2 := by
  constructor
  · change bisectRun [true, false, false, true] ⟨1, 2⟩ = _
    norm_num [bisectRun, bisectStep, RatInterval.mid]
  · have h : sqrtTwoRoot.root ^ 2 - 2 = 0 := sqrtTwoRoot.apply_root_eq_zero
    have hm : sqrtTwoRoot.root ∈ Set.Icc ((1 : ℚ) : ℝ) ((2 : ℚ) : ℝ) := sqrtTwoRoot.root_mem
    push_cast at hm
    exact ((Real.sqrt_eq_iff_eq_sq (by norm_num) (by linarith [hm.1])).2 (by linarith)).symm

-- A hypothetical measured variant, outside the capstone record (whose data are exact): if the
-- constant `2` were a measurement of an unknown `cTrue` with uncertainty `1/1000`, the reported
-- midpoint would be within `1/2048` (certified numerical error) plus `1 * (1/1000)` (conditioning
-- constant `1` times data uncertainty) of the true solution `xTrue`.
example {cTrue xTrue : ℝ} (hdata : |(2 : ℝ) - cTrue| ≤ 1 / 1000)
    (hx : xTrue + Real.exp xTrue = cTrue) :
    |(907 / 2048 : ℝ) - xTrue| ≤ 1 / 2048 + 1 * (1 / 1000) := by
  have hnum : |(907 / 2048 : ℝ) - equilibriumCapstone.root| ≤ 1 / 2048 := by
    have h := equilibriumCapstone.encloses_root.abs_sub_mid_le
    rw [show bisectRun equilibriumCapstone.decisions equilibriumCapstone.bracket =
      ⟨453 / 1024, 227 / 512⟩ from bisectRun_equilibriumDecisions, abs_sub_comm] at h
    norm_num [RatInterval.mid, RatInterval.width] at h ⊢
    exact h
  have hcond : |equilibriumCapstone.root - xTrue| ≤ ((1 : NNReal) : ℝ) * |2 - cTrue| := by
    have h := abs_sub_le_abs_add_sub_add Real.exp_monotone equilibriumCapstone.root xTrue
    rw [capstone_root_eq, hx] at h
    simpa using h
  have h := abs_sub_le_numerical_add_data hnum hcond hdata
  simpa using h
