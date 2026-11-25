/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.DeBruijnNewman
public import MathlibExt.NumberTheory.LSeries.RiemannXi
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Asymptotics

/-!
# The de Bruijn–Newman deformation at time zero and the Riemann ξ function

At time `0` the de Bruijn–Newman deformation `H 0` is the Riemann ξ function on the critical line,
rescaled: `8 H 0 z = ξ(1/2 + i z / 2)`. A real `z` corresponds to a point of the line `Re s = 1/2`.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.DeBruijnNewmanXiWanted

open Complex MathlibExt.NumberTheory.DeBruijnNewman RiemannXi
open Real MeasureTheory Set Filter Asymptotics HurwitzZeta
open scoped Topology

-- Gaussian moments of the positive-index part of the theta series.
private noncomputable def rate (n : ℕ) : ℝ := π * (n + 1 : ℝ) ^ 2

private noncomputable def momentTerm (j n : ℕ) (t : ℝ) : ℝ :=
  rate n ^ j * Real.exp (-(rate n) * t)

private noncomputable def moment (j : ℕ) (t : ℝ) : ℝ := ∑' n, momentTerm j n t

private lemma rate_ge_one (n : ℕ) : 1 ≤ rate n := by
  unfold rate
  have hn : 1 ≤ (n + 1 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n]
  nlinarith [mul_le_mul_of_nonneg_left hn Real.pi_pos.le, Real.pi_gt_three]

private lemma term_nonneg (j n : ℕ) (t : ℝ) : 0 ≤ momentTerm j n t := by
  unfold momentTerm rate
  positivity

private lemma summable_term (j : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable (fun n ↦ momentTerm j n t) := by
  have h := (summable_nat_add_iff 1).mpr
    (Real.summable_pow_mul_exp_neg_nat_mul (2 * j) (mul_pos Real.pi_pos ht))
  refine Summable.of_nonneg_of_le (fun n ↦ term_nonneg j n t) (f := fun n : ℕ ↦
    π ^ j * (((n + 1 : ℕ) : ℝ) ^ (2 * j) * Real.exp (-(π * t) * (n + 1 : ℕ)))) ?_
    (h.mul_left (π ^ j))
  intro n
  push_cast
  simp only [momentTerm, rate, mul_pow, pow_mul, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hn : (n + 1 : ℝ) ≤ (n + 1 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n]
  nlinarith [mul_le_mul_of_nonneg_left hn (mul_pos Real.pi_pos ht).le]

private lemma moment_deriv (j : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (moment j) (-moment (j + 1) t) t := by
  have hhalf : 0 < t / 2 := by positivity
  have hlt : t / 2 < t := by linarith
  have hd (n : ℕ) (v : ℝ) :
      HasDerivAt (momentTerm j n) (-momentTerm (j + 1) n v) v := by
    convert! (((hasDerivAt_id v).const_mul (-(rate n))).exp.const_mul (rate n ^ j)) using 1
    simp [momentTerm, pow_succ, mul_comm, mul_assoc, mul_left_comm]
  have hb (n : ℕ) (v : ℝ) (hv : v ∈ Ioi (t / 2)) :
      ‖-momentTerm (j + 1) n v‖ ≤ momentTerm (j + 1) n (t / 2) := by
    rw [norm_neg, Real.norm_of_nonneg (term_nonneg ..)]
    unfold momentTerm
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith [rate_ge_one n]) _)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hv.le (by linarith [rate_ge_one n]))
  unfold moment
  simpa only [tsum_neg] using hasDerivAt_tsum_of_isPreconnected
    (summable_term (j + 1) hhalf) isOpen_Ioi isPreconnected_Ioi (fun n v _ ↦ hd n v)
    hb hlt (summable_term j ht) hlt

private lemma moment_bound (j : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    moment j t ≤ moment j (1 / 2) * Real.exp (-t / 2) := by
  unfold moment
  rw [← tsum_mul_right]
  refine (summable_term j (by linarith : 0 < t)).tsum_le_tsum (fun n ↦ ?_)
    ((summable_term j (show 0 < 1 / 2 by norm_num)).mul_right _)
  simp only [momentTerm, mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith [rate_ge_one n]) _)
  apply Real.exp_le_exp.mpr
  nlinarith [rate_ge_one n, mul_nonneg (sub_nonneg.mpr (rate_ge_one n)) (sub_nonneg.mpr ht)]

-- The Laplace integrals of the moments after the substitution t = exp(4u).
private noncomputable def weighted (j : ℕ) (b : ℂ) (u : ℝ) : ℂ :=
  (moment j (Real.exp (4 * u)) : ℂ) * Complex.exp (b * u)

private noncomputable def laplace (j : ℕ) (b : ℂ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), weighted j b u

private lemma weighted_deriv (j : ℕ) (b : ℂ) (u : ℝ) :
    HasDerivAt (weighted j b)
      (b * weighted j b u - 4 * weighted (j + 1) (b + 4) u) u := by
  have hm := ((moment_deriv j (Real.exp_pos (4 * u))).comp u
    (((hasDerivAt_id u).const_mul 4).exp)).ofReal_comp
  have heb := ((Complex.hasDerivAt_exp (b * u)).comp (u : ℂ)
    ((hasDerivAt_id (u : ℂ)).const_mul b)).comp_ofReal
  convert! hm.mul heb using 1
  simp [weighted, add_mul, Complex.exp_add, mul_comm (4 : ℂ)]
  ring_nf

private lemma weighted_decay (j : ℕ) (b : ℂ) :
    weighted j b =O[atTop] fun u : ℝ ↦ Real.exp (-u) := by
  refine isBigO_iff.mpr ⟨moment j (1 / 2), ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ), eventually_ge_atTop (b.re + 1)] with u hu hb
  have ht : 1 ≤ Real.exp (4 * u) := Real.one_le_exp (by positivity)
  have hm : 0 ≤ moment j (Real.exp (4 * u)) := tsum_nonneg (fun n ↦ term_nonneg j n _)
  rw [weighted, norm_mul, Complex.norm_real, Real.norm_of_nonneg hm, Complex.norm_exp,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Real.norm_of_nonneg (Real.exp_nonneg _)]
  calc
    _ ≤ (moment j (1 / 2) * Real.exp (-Real.exp (4 * u) / 2)) * Real.exp (b.re * u) :=
      mul_le_mul_of_nonneg_right (moment_bound j ht) (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [mul_assoc, ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ (tsum_nonneg (fun n ↦ term_nonneg j n _))
      apply Real.exp_le_exp.mpr
      nlinarith [Real.quadratic_le_exp_of_nonneg (show 0 ≤ 4 * u by positivity),
        mul_nonneg (sub_nonneg.mpr hb) hu, sq_nonneg u]

private lemma weighted_int (j : ℕ) (b : ℂ) : IntegrableOn (weighted j b) (Ioi 0) := by
  have hc : Continuous (weighted j b) :=
    continuous_iff_continuousAt.mpr fun u ↦ (weighted_deriv j b u).continuousAt
  exact ((hc.continuousOn.locallyIntegrableOn measurableSet_Ici).integrableOn_of_isBigO_atTop
    (weighted_decay j b) ⟨Ioi 0, Ioi_mem_atTop 0, integrableOn_exp_neg_Ioi 0⟩).mono_set
    Ioi_subset_Ici_self

private lemma laplace_step (j : ℕ) (b : ℂ) :
    4 * laplace (j + 1) (b + 4) = b * laplace j b + moment j 1 := by
  have htop := (weighted_decay j b).trans_tendsto Real.tendsto_exp_neg_atTop_nhds_zero
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0)
    (fun u _ ↦ weighted_deriv j b u)
    (((weighted_int j b).const_mul b).sub ((weighted_int (j + 1) (b + 4)).const_mul 4)) htop
  rw [integral_sub ((weighted_int j b).const_mul b)
    ((weighted_int (j + 1) (b + 4)).const_mul 4), integral_const_mul, integral_const_mul] at h
  change b * laplace j b - 4 * laplace (j + 1) (b + 4) = 0 - weighted j b 0 at h
  simp only [weighted, ofReal_zero, mul_zero, Real.exp_zero, Complex.exp_zero, mul_one] at h
  linear_combination -h

private lemma theta_eq {t : ℝ} (ht : 0 < t) :
    evenKernel 0 t = 1 + 2 * moment 0 t := by
  have h := (hasSum_nat_cosKernel₀ 0 ht).tsum_eq
  simp only [mul_zero, zero_mul, Real.cos_zero, mul_one, neg_mul, QuotientAddGroup.mk_zero,
    ← evenKernel_eq_cosKernel_of_zero] at h
  have hm : (∑' n : ℕ, 2 * Real.exp (-π * (n + 1 : ℝ) ^ 2 * t)) = 2 * moment 0 t := by
    simp [moment, momentTerm, rate, tsum_mul_left, neg_mul]
  simp only [neg_mul] at hm
  linarith

private lemma theta_reflect (v : ℝ) :
    evenKernel 0 (Real.exp (-v)) = Real.exp (v / 2) * evenKernel 0 (Real.exp v) := by
  rw [evenKernel_functional_equation, ← evenKernel_eq_cosKernel_of_zero,
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  simp only [← Real.exp_neg, neg_neg, neg_mul, div_eq_mul_inv, one_mul]

-- Differentiate the theta transformation at its fixed point to evaluate the boundary term.
private lemma boundary : 4 * moment 1 1 - moment 0 1 = 1 / 2 := by
  let f (v : ℝ) := 1 + 2 * moment 0 (Real.exp v)
  have hd : HasDerivAt f (-2 * moment 1 1) 0 := by
    have h := (((moment_deriv 0 (Real.exp_pos 0)).comp 0
      (Real.hasDerivAt_exp 0)).const_mul 2).const_add 1
    simpa [f, Function.comp_def] using h
  have heq : (fun v ↦ f (-v)) = fun v ↦ Real.exp (v / 2) * f v := by
    funext v
    simpa only [theta_eq (Real.exp_pos _), f] using theta_reflect v
  have hd' : HasDerivAt f (-2 * moment 1 1) (-id (0 : ℝ)) := by simpa using hd
  have hl := hd'.comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).neg)
  have hr := (((hasDerivAt_id (0 : ℝ)).div_const 2).exp).mul hd
  change HasDerivAt (fun v ↦ f (-v)) _ _ at hl
  rw [heq] at hl
  have h := hl.unique hr
  simp [f] at h
  linarith

-- Fold the entire Mellin integral at t = 1, using the theta transformation on (0,1).
private noncomputable def logKernel (s : ℂ) (v : ℝ) : ℂ :=
  Complex.exp (v * (s / 2)) * (hurwitzEvenFEPair 0).f_modif (Real.exp v)

private lemma modif_pos {v : ℝ} (hv : 0 < v) :
    (hurwitzEvenFEPair 0).f_modif (Real.exp v) = 2 * (moment 0 (Real.exp v) : ℂ) := by
  have ht := Real.one_lt_exp_iff.mpr hv
  simp [WeakFEPair.f_modif, indicator_of_mem (mem_Ioi.mpr ht),
    indicator_of_notMem (notMem_Ioo_of_ge ht.le : Real.exp v ∉ Ioo 0 1), hurwitzEvenFEPair,
    theta_eq (Real.exp_pos _)]

private lemma modif_neg {v : ℝ} (hv : 0 < v) :
    (hurwitzEvenFEPair 0).f_modif (Real.exp (-v)) =
      (Real.exp (v / 2) : ℂ) * (2 * moment 0 (Real.exp v)) := by
  have ht : Real.exp (-v) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hv)
  rw [WeakFEPair.f_modif, Pi.add_apply, indicator_of_mem (mem_Ioo.mpr ⟨Real.exp_pos _, ht⟩),
    indicator_of_notMem (notMem_Ioi.mpr ht.le), zero_add]
  simp only [hurwitzEvenFEPair, Function.comp_apply, one_mul, smul_eq_mul, mul_one]
  rw [theta_reflect, theta_eq (Real.exp_pos v), Real.rpow_def_of_pos (Real.exp_pos _),
    Real.log_exp, show -v * -(1 / 2) = v / 2 by ring]
  push_cast
  ring

private lemma mellin_integrand (s : ℂ) (v : ℝ) :
    Real.exp v • ((Real.exp v : ℂ) ^ (s / 2 - 1) •
      (hurwitzEvenFEPair 0).f_modif (Real.exp v)) = logKernel s v := by
  rw [real_smul, smul_eq_mul, Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)), ← Complex.ofReal_log (Real.exp_pos _).le,
    Real.log_exp, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add, logKernel]
  congr 2
  ring

private lemma integral_half_scale (f : ℝ → ℂ) :
    (∫ u in Ioi (0 : ℝ), f u) = 4 * ∫ u in Ioi (0 : ℝ), f (4 * u) := by
  simpa [real_smul, smul_eq_mul] using
    (integral_comp_mul_left_Ioi' f 0 (by norm_num : (0 : ℝ) < 4)).symm

private lemma completed_eq (s : ℂ) :
    completedRiemannZeta₀ s = 4 * (laplace 0 (2 * s) + laplace 0 (2 - 2 * s)) := by
  have hc := ((hurwitzEvenFEPair 0).isStrongFEPair_toStrongFEPair.hasMellin (s / 2)).1
  change MellinConvergent (hurwitzEvenFEPair 0).f_modif (s / 2) at hc
  have hi : Integrable (logKernel s) := by
    simpa only [mellin_integrand] using (integrable_comp_exp _).mpr hc
  have he : completedRiemannZeta₀ s = (∫ v, logKernel s v) / 2 := by
    change (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s / 2 - 1) • (hurwitzEvenFEPair 0).f_modif t) / 2 = _
    rw [← integral_comp_exp]
    simp only [mellin_integrand]
  have hp : (∫ v in Ioi (0 : ℝ), logKernel s v) = 4 * (2 * laplace 0 (2 * s)) := by
    rw [integral_half_scale (logKernel s)]
    congr 1
    rw [laplace, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu ↦ ?_
    rw [logKernel, modif_pos (mul_pos (by norm_num) hu), weighted]
    push_cast
    rw [show 4 * (u : ℂ) * (s / 2) = 2 * s * u by ring]
    ring
  have hn : (∫ v in Ioi (0 : ℝ), logKernel s (-v)) = 4 * (2 * laplace 0 (2 - 2 * s)) := by
    rw [integral_half_scale (fun v ↦ logKernel s (-v))]
    congr 1
    rw [laplace, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu ↦ ?_
    rw [logKernel, modif_neg (mul_pos (by norm_num) hu), weighted]
    push_cast
    rw [← mul_assoc, ← Complex.exp_add, show -(4 * (u : ℂ)) * (s / 2) + 4 * u / 2 =
      (2 - 2 * s) * u by ring]
    ring
  have hr := integral_comp_neg_Ioi 0 (logKernel s)
  rw [neg_zero] at hr
  rw [he, ← integral_add_compl (measurableSet_Ioi (a := 0)) hi, compl_Ioi, ← hr, hp, hn]
  ring

private lemma phi_eq (u : ℝ) :
    phi u = 2 * Real.exp (9 * u) * moment 2 (Real.exp (4 * u)) -
      3 * Real.exp (5 * u) * moment 1 (Real.exp (4 * u)) := by
  unfold phi moment
  rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_sub]
  · apply tsum_congr
    intro n
    simp only [phiTerm, momentTerm, rate, neg_mul]
    ring
  · exact (summable_term 2 (Real.exp_pos _)).mul_left _
  · exact (summable_term 1 (Real.exp_pos _)).mul_left _

private noncomputable def phiExp (a : ℂ) (u : ℝ) : ℂ :=
  phi u * Complex.exp (a * u)

private lemma phiExp_eq (a : ℂ) : phiExp a = fun u ↦
    2 * weighted 2 (1 + a + 4 + 4) u - 3 * weighted 1 (1 + a + 4) u := by
  funext u
  rw [phiExp, phi_eq, weighted, weighted]
  push_cast
  rw [show (1 + a + 4 + 4) * (u : ℂ) = 9 * u + a * u by ring,
    show (1 + a + 4) * (u : ℂ) = 5 * u + a * u by ring, Complex.exp_add, Complex.exp_add]
  ring

private lemma phiExp_int (a : ℂ) : IntegrableOn (phiExp a) (Ioi 0) := by
  rw [phiExp_eq]
  exact ((weighted_int ..).const_mul 2).sub ((weighted_int ..).const_mul 3)

-- Two integrations by parts convert the kernel transform to the zeroth moment.
private lemma phiExp_transform (a : ℂ) :
    8 * (∫ u in Ioi (0 : ℝ), phiExp a u) =
    (a ^ 2 - 1) * laplace 0 (1 + a) + (a - 1) * (moment 0 1 : ℂ) + 4 * moment 1 1 := by
  rw [phiExp_eq, integral_sub ((weighted_int ..).const_mul 2) ((weighted_int ..).const_mul 3),
    integral_const_mul, integral_const_mul]
  change 8 * (2 * laplace 2 _ - 3 * laplace 1 _) = _
  linear_combination 4 * laplace_step 1 (1 + a + 4) + (a - 1) * laplace_step 0 (1 + a)

/-- **Fourier integral for the Riemann ξ function.** For every complex number `z`,
`8 H₀(z) = ξ(1/2 + i z / 2)`, where `H₀(z) = ∫₀^∞ Φ(u) cos(z u) du` is the de Bruijn–Newman
deformation at time `0`, `Φ` is Newman's kernel, and `ξ` is the Riemann ξ function:
`ξ(s) = s (s - 1) / 2 · Λ(s)` for `s ≠ 0, 1` and `ξ(0) = ξ(1) = 1/2`, where `Λ` is the completed
zeta function, the meromorphic function `π^(-s/2) Γ(s/2) ζ(s)` continued across its removable
singularities at `-2, -4, …`, whose only poles are simple poles at `0` and `1`.

Source: B. Rodgers and T. Tao, *The de Bruijn–Newman constant is non-negative*, Forum Math. Pi 8
(2020), e6, arXiv:1801.05914v3, §1: equation (1) defines `H₀(z) = ξ(1/2 + i z / 2) / 8` with `ξ`
as in (2), and the next sentence gives the Fourier representation `H₀(z) = ∫₀^∞ Φ(u) cos(z u) du`
with `Φ` as in (3), as a classical fact (citing E. C. Titchmarsh, *The theory of the Riemann
zeta-function*, 2nd ed., p. 255). -/
theorem eight_mul_H_zero_eq_riemannXi (z : ℂ) :
    8 * H 0 z = riemannXi (1 / 2 + I * z / 2) := by
  let a := I * z
  have hcos : H 0 z = ((∫ u in Ioi (0 : ℝ), phiExp a u) +
      ∫ u in Ioi (0 : ℝ), phiExp (-a) u) / 2 := by
    rw [H, ← integral_add (phiExp_int a) (phiExp_int (-a)), ← integral_div]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
    simp only [zero_mul, Real.exp_zero, one_mul, Complex.cos, phiExp, a]
    rw [show z * (u : ℂ) * I = I * z * u by ring,
      show -(z * (u : ℂ)) * I = -(I * z) * u by ring]
    ring
  have hb : 4 * (moment 1 1 : ℂ) - moment 0 1 = 1 / 2 := by
    simpa only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using congrArg Complex.ofReal boundary
  rw [hcos, riemannXi, completed_eq]
  change _ = (1 / 2 + a / 2) * (1 / 2 + a / 2 - 1) / 2 *
    (4 * (laplace 0 (2 * (1 / 2 + a / 2)) + laplace 0 (2 - 2 * (1 / 2 + a / 2)))) + 1 / 2
  rw [show 2 * (1 / 2 + a / 2) = 1 + a by ring,
    show 2 - (1 + a) = 1 + -a by ring]
  linear_combination (phiExp_transform a + phiExp_transform (-a)) / 2 + hb

end MathlibExt.NumberTheory.DeBruijnNewmanXiWanted
