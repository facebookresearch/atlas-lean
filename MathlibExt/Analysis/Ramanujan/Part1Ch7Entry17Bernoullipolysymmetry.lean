/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.MeasureTheory.Function.Floor

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
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Meromorphic.Complex
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 7

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry17Bernoullipolysymmetry

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open DirichletBeta

noncomputable section

def chapter7DirichletBetaTerm (s : ℂ) (k : ℕ) : ℂ :=
  (-1 : ℂ) ^ k / Complex.cpow (2 * k + 1 : ℕ) s

def chapter7DirichletBetaPartialSum (s : ℂ) (N : ℕ) : ℂ :=
  ∑ k ∈ range N, chapter7DirichletBetaTerm s k

def chapter7Entry17Left (r : ℂ) : ℂ :=
  chapter7Phi r ⟨-1 / 4, by
      change (-1 : ℝ) < -1 / 4 ∧ (-1 / 4 : ℝ) < 0
      norm_num⟩ -
    chapter7Phi r ⟨-3 / 4, by
      change (-1 : ℝ) < -3 / 4 ∧ (-3 / 4 : ℝ) < 0
      norm_num⟩

def chapter7Entry17Right (r : ℂ) : ℂ :=
  2 * Complex.cos (Real.pi * r / 2) * chapter7EulerStar (r + 1) /
    Complex.cpow 4 (r + 1)

/-- The class of `3 / 4` is the negation of the class of `1 / 4`. -/
private theorem class34_eq_neg_class14 :
    (((3 / 4 : ℝ)) : UnitAddCircle) = -(((1 / 4 : ℝ)) : UnitAddCircle) := by
  have h : (3 / 4 : ℝ) = 1 - 1 / 4 := by norm_num
  rw [h, AddCircle.coe_sub, AddCircle.coe_period (1 : ℝ), zero_sub]

/-- The left side equals twice the odd Hurwitz zeta at `1 / 4`. -/
private theorem entry17Left_eq (r : ℂ) :
    chapter7Entry17Left r =
      2 * HurwitzZeta.hurwitzZetaOdd ((1 / 4 : ℝ) : UnitAddCircle) (-r) := by
  unfold chapter7Entry17Left chapter7Phi
  change riemannZeta (-r) -
        HurwitzZeta.hurwitzZeta (((-1 / 4 : ℝ) + 1 : ℝ) : UnitAddCircle) (-r) -
        (riemannZeta (-r) -
          HurwitzZeta.hurwitzZeta (((-3 / 4 : ℝ) + 1 : ℝ) : UnitAddCircle) (-r)) =
      2 * HurwitzZeta.hurwitzZetaOdd ((1 / 4 : ℝ) : UnitAddCircle) (-r)
  rw [show ((-1 / 4 : ℝ) + 1) = (3 / 4 : ℝ) by norm_num,
    show ((-3 / 4 : ℝ) + 1) = (1 / 4 : ℝ) by norm_num, class34_eq_neg_class14]
  simp only [HurwitzZeta.hurwitzZeta]
  rw [HurwitzZeta.hurwitzZetaEven_neg, HurwitzZeta.hurwitzZetaOdd_neg]
  ring

/-- Key lemma: the sine zeta at `1 / 4` is the Dirichlet beta function. -/
private theorem sinZeta_quarter_eq_beta :
    ∀ s : ℂ, HurwitzZeta.sinZeta ((1 / 4 : ℝ) : UnitAddCircle) s =
      chapter7DirichletBeta s := by
  have hNe : NeZero 4 := ⟨by decide⟩
  have key : ∀ s : ℂ, 1 < s.re →
      HurwitzZeta.sinZeta ((1 / 4 : ℝ) : UnitAddCircle) s =
        chapter7DirichletBeta s := by
    intro s hs
    have hbeta : chapter7DirichletBeta s =
        LSeries (fun x => chapter7BetaCharacter (↑x : ZMod 4)) s :=
      ZMod.LFunction_eq_LSeries _ hs
    have hsumm : LSeriesSummable (fun x => chapter7BetaCharacter (↑x : ZMod 4)) s :=
      ZMod.LSeriesSummable_of_one_lt_re _ hs
    have hHasBeta : HasSum
        (LSeries.term (fun x => chapter7BetaCharacter (↑x : ZMod 4)) s)
        (chapter7DirichletBeta s) := by
      rw [hbeta]
      exact hsumm.LSeriesHasSum
    have hHasSin : HasSum
        (fun n : ℕ => ((Real.sin (2 * Real.pi * (1 / 4 : ℝ) * (n : ℝ)) : ℝ) : ℂ) /
          ((n : ℂ) ^ s))
        (HurwitzZeta.sinZeta ((1 / 4 : ℝ) : UnitAddCircle) s) :=
      HurwitzZeta.hasSum_nat_sinZeta (1 / 4) hs
    have hterm : ∀ n : ℕ, LSeries.term (fun x => chapter7BetaCharacter (↑x : ZMod 4)) s n =
        ((Real.sin (2 * Real.pi * (1 / 4 : ℝ) * (n : ℝ)) : ℝ) : ℂ) / ((n : ℂ) ^ s) := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · rw [LSeries.term_zero]
        simp
      · rw [LSeries.term_of_ne_zero hn]
        show chapter7BetaCharacter (↑n : ZMod 4) / (↑n : ℂ) ^ s =
          ((Real.sin (2 * Real.pi * (1 / 4 : ℝ) * (n : ℝ)) : ℝ) : ℂ) / (↑n : ℂ) ^ s
        congr 1
        have hmod : (n : ZMod 4) = (((n % 4 : ℕ)) : ZMod 4) :=
          (ZMod.natCast_mod n 4).symm
        rw [hmod]
        have hdecomp : (n : ℝ) = ((n % 4 : ℕ) : ℝ) + 4 * ((n / 4 : ℕ) : ℝ) := by
          have h := Nat.mod_add_div n 4
          have h2 : ((n % 4 + 4 * (n / 4) : ℕ) : ℝ) = ((n : ℕ) : ℝ) := by
            exact_mod_cast h
          push_cast at h2
          linarith
        have harg : 2 * Real.pi * (1 / 4 : ℝ) * (n : ℝ) =
            Real.pi * ((n % 4 : ℕ) : ℝ) / 2 + ((n / 4 : ℕ) : ℝ) * (2 * Real.pi) := by
          rw [hdecomp]
          ring
        rw [harg, Real.sin_add_nat_mul_two_pi]
        have hcases : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
          have h4lt : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
          omega
        rcases hcases with h0 | h1 | h2 | h3
        · rw [h0]
          simp
        · rw [h1]
          simp
        · rw [h2]
          simp
        · rw [h3]
          have e3 : Real.pi * ((3 : ℕ) : ℝ) / 2 = Real.pi / 2 + Real.pi := by
            push_cast
            ring
          rw [e3, Real.sin_add_pi, Real.sin_pi_div_two]
          simp [betaChar3]
    have hfun_eq : LSeries.term (fun x => chapter7BetaCharacter (↑x : ZMod 4)) s =
        (fun n : ℕ => ((Real.sin (2 * Real.pi * (1 / 4 : ℝ) * (n : ℝ)) : ℝ) : ℂ) /
          ((n : ℂ) ^ s)) :=
      funext hterm
    rw [hfun_eq] at hHasBeta
    exact HasSum.unique hHasSin hHasBeta
  have hA : AnalyticOnNhd ℂ (HurwitzZeta.sinZeta ((1 / 4 : ℝ) : UnitAddCircle)) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (HurwitzZeta.differentiableAt_sinZeta _)
  have hB : AnalyticOnNhd ℂ chapter7DirichletBeta Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr betaDirichletEntire
  have hev : HurwitzZeta.sinZeta ((1 / 4 : ℝ) : UnitAddCircle) =ᶠ[nhds 2]
      chapter7DirichletBeta := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := Complex.isOpen_re_gt 1
    have h2 : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by norm_num
    filter_upwards [hopen.mem_nhds h2] with s hs
    exact key s hs
  have hfun : HurwitzZeta.sinZeta ((1 / 4 : ℝ) : UnitAddCircle) = chapter7DirichletBeta :=
    AnalyticOnNhd.eq_of_eventuallyEq hA hB hev
  exact congrFun hfun

/-- The Euler star function is meromorphic everywhere. -/
private theorem eulerStar_mero : MeromorphicOn chapter7EulerStar Set.univ := by
  have hpi : ((Real.pi / 2 : ℝ) : ℂ) ≠ 0 := by
    have h : (0 : ℝ) < Real.pi / 2 := half_pos Real.pi_pos
    exact_mod_cast ne_of_gt h
  have hcpow : Differentiable ℂ (fun s : ℂ => Complex.cpow ((Real.pi / 2 : ℝ) : ℂ) s) :=
    differentiable_id.const_cpow (Or.inl hpi)
  have hBeta : MeromorphicOn chapter7DirichletBeta Set.univ :=
    AnalyticOnNhd.meromorphicOn
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr betaDirichletEntire)
  have h2 : MeromorphicOn (fun _ : ℂ => (2 : ℂ)) Set.univ := MeromorphicOn.const 2
  have hG : MeromorphicOn Complex.Gamma Set.univ := MeromorphicOn.Gamma
  have hmul : MeromorphicOn (fun s : ℂ => 2 * Complex.Gamma s * chapter7DirichletBeta s)
      Set.univ :=
    (h2.mul hG).mul hBeta
  have hdiv := hmul.div (AnalyticOnNhd.meromorphicOn
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hcpow))
  have hfun : chapter7EulerStar =
      (fun s : ℂ => 2 * Complex.Gamma s * chapter7DirichletBeta s /
        Complex.cpow ((Real.pi / 2 : ℝ) : ℂ) s) := rfl
  rw [hfun]
  exact hdiv

/-- The left side is meromorphic everywhere (it is entire). -/
private theorem entry17Left_mero : MeromorphicOn chapter7Entry17Left Set.univ := by
  have hfun : chapter7Entry17Left =
      (fun r : ℂ => 2 * HurwitzZeta.hurwitzZetaOdd ((1 / 4 : ℝ) : UnitAddCircle) (-r)) :=
    funext entry17Left_eq
  rw [hfun]
  have hO : Differentiable ℂ
      (fun r : ℂ => HurwitzZeta.hurwitzZetaOdd ((1 / 4 : ℝ) : UnitAddCircle) (-r)) :=
    (HurwitzZeta.differentiable_hurwitzZetaOdd _).comp (differentiable_id.neg)
  exact AnalyticOnNhd.meromorphicOn
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr ((differentiable_const 2).mul hO))

/-- The right side is meromorphic everywhere. -/
private theorem entry17Right_mero : MeromorphicOn chapter7Entry17Right Set.univ := by
  have hcos : Differentiable ℂ (fun r : ℂ => Complex.cos (↑Real.pi * r / 2)) :=
    Complex.differentiable_cos.comp
      (((differentiable_const (↑Real.pi : ℂ)).mul differentiable_id).div_const 2)
  have hcosm : MeromorphicOn (fun r : ℂ => Complex.cos (↑Real.pi * r / 2)) Set.univ :=
    AnalyticOnNhd.meromorphicOn
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hcos)
  have hEcomp : MeromorphicOn (fun r : ℂ => chapter7EulerStar (r + 1)) Set.univ := by
    intro x _
    have h1 : MeromorphicAt chapter7EulerStar (x + 1) :=
      eulerStar_mero (x + 1) (Set.mem_univ _)
    have h2 : AnalyticAt ℂ (fun r : ℂ => r + 1) x :=
      (differentiable_id.add_const 1).analyticAt x
    exact h1.comp_analyticAt (g := fun r : ℂ => r + 1) h2
  have h4 : (4 : ℂ) ≠ 0 := by norm_num
  have hcpow : Differentiable ℂ (fun r : ℂ => Complex.cpow 4 (r + 1)) :=
    (differentiable_id.add_const 1).const_cpow (Or.inl h4)
  have hcpowm : MeromorphicOn (fun r : ℂ => Complex.cpow 4 (r + 1)) Set.univ :=
    AnalyticOnNhd.meromorphicOn
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hcpow)
  have h2 : MeromorphicOn (fun _ : ℂ => (2 : ℂ)) Set.univ := MeromorphicOn.const 2
  have hfun : chapter7Entry17Right =
      (fun r : ℂ => 2 * Complex.cos (↑Real.pi * r / 2) * chapter7EulerStar (r + 1) /
        Complex.cpow 4 (r + 1)) := rfl
  rw [hfun]
  exact ((h2.mul hcosm).mul hEcomp).div hcpowm

/-- Pointwise equality off the nonpositive integers shifted by one. -/
private theorem entry17_eq_off (r : ℂ) (hs : ∀ n : ℕ, r + 1 ≠ -(n : ℂ)) :
    chapter7Entry17Left r = chapter7Entry17Right r := by
  set s := r + 1 with hs_def
  have hLeft : chapter7Entry17Left r =
      2 * HurwitzZeta.hurwitzZetaOdd ((1 / 4 : ℝ) : UnitAddCircle) (1 - s) := by
    have hr : -r = 1 - s := by rw [hs_def]; ring
    rw [entry17Left_eq r, hr]
  have hFE := HurwitzZeta.hurwitzZetaOdd_one_sub ((1 / 4 : ℝ) : UnitAddCircle)
    (s := s) (fun n => hs n)
  rw [hLeft, hFE, sinZeta_quarter_eq_beta s]
  have hsin : Complex.sin (↑Real.pi * s / 2) = Complex.cos (↑Real.pi * r / 2) := by
    have harg : ↑Real.pi * s / 2 = ↑Real.pi * r / 2 + ↑Real.pi / 2 := by
      rw [hs_def]; ring
    rw [harg, Complex.sin_add_pi_div_two]
  rw [hsin]
  have hbase : ((2 : ℂ) * ↑Real.pi) = ((Real.pi / 2 : ℝ) : ℂ) * 4 := by
    push_cast
    ring
  have hsplit : ((2 : ℂ) * ↑Real.pi) ^ s =
      ((Real.pi / 2 : ℝ) : ℂ) ^ s * (4 : ℂ) ^ s := by
    rw [hbase]
    exact Complex.mul_cpow_ofReal_nonneg (div_nonneg (le_of_lt Real.pi_pos)
      (by norm_num)) (by norm_num) s
  have hpi : ((Real.pi / 2 : ℝ) : ℂ) ≠ 0 := by
    have h : (0 : ℝ) < Real.pi / 2 := half_pos Real.pi_pos
    exact_mod_cast ne_of_gt h
  have hP : ((Real.pi / 2 : ℝ) : ℂ) ^ s ≠ 0 := by
    intro h
    rw [Complex.cpow_eq_zero_iff] at h
    exact hpi h.1
  have hF : (4 : ℂ) ^ s ≠ 0 := by
    intro h
    rw [Complex.cpow_eq_zero_iff] at h
    exact (by norm_num : (4 : ℂ) ≠ 0) h.1
  have hA : ((2 : ℂ) * ↑Real.pi) ^ (-s) =
      (((Real.pi / 2 : ℝ) : ℂ) ^ s * (4 : ℂ) ^ s)⁻¹ := by
    rw [← hsplit, Complex.cpow_neg]
  rw [hA]
  have hRight : chapter7Entry17Right r =
      2 * Complex.cos (↑Real.pi * r / 2) * chapter7EulerStar (r + 1) /
        (4 : ℂ) ^ (r + 1) := rfl
  have hEuler : ∀ t : ℂ, chapter7EulerStar t =
      2 * Complex.Gamma t * chapter7DirichletBeta t / ((Real.pi / 2 : ℝ) : ℂ) ^ t :=
    fun t => rfl
  rw [hRight, hEuler, ← hs_def]
  field_simp

/-- Eventual equality on a codiscrete set. -/
private theorem entry17_eventual :
    chapter7Entry17Left =ᶠ[codiscrete ℂ] chapter7Entry17Right := by
  have hg : Differentiable ℂ (fun r : ℂ => (Complex.Gamma (r + 1))⁻¹) :=
    Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const 1)
  have hA : AnalyticOnNhd ℂ (fun r : ℂ => (Complex.Gamma (r + 1))⁻¹) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hg
  have hg0 : (fun r : ℂ => (Complex.Gamma (r + 1))⁻¹) 0 ≠ 0 := by
    simp [Complex.Gamma_one]
  have hmem : (fun r : ℂ => (Complex.Gamma (r + 1))⁻¹) ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℂ :=
    AnalyticOnNhd.preimage_zero_mem_codiscrete hA hg0
  apply Filter.mem_of_superset hmem
  intro r hr
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hr
  have hG : Complex.Gamma (r + 1) ≠ 0 := by
    intro h
    apply hr
    rw [h]
    exact inv_zero
  refine entry17_eq_off r (fun n hn => hG ?_)
  rw [Complex.Gamma_eq_zero_iff]
  exact ⟨n, hn⟩

/-- The Dirichlet beta coefficients. -/
private def betaCoeff : ℕ → ℂ := fun n => chapter7BetaCharacter (n : ZMod 4)

private theorem betaCoeff_zero : betaCoeff 0 = 0 := by
  simp [betaCoeff, betaChar0]

private theorem betaCoeff_sum_char : ∀ N : ℕ, ∑ n ∈ Finset.Icc 0 N, betaCoeff n =
    if N % 4 = 1 ∨ N % 4 = 2 then 1 else 0 := by
  intro N
  induction N with
  | zero => simp [betaCoeff_zero]
  | succ N ih =>
    have hsum : ∑ n ∈ Finset.Icc 0 (N + 1), betaCoeff n =
        (∑ n ∈ Finset.Icc 0 N, betaCoeff n) + betaCoeff (N + 1) :=
      Finset.sum_Icc_succ_top (by omega) _
    have hmod : (N + 1) % 4 = 0 ∨ (N + 1) % 4 = 1 ∨ (N + 1) % 4 = 2 ∨
        (N + 1) % 4 = 3 := by omega
    have hcast : (((N + 1 : ℕ)) : ZMod 4) = ((((N + 1) % 4 : ℕ)) : ZMod 4) :=
      (ZMod.natCast_mod (N + 1) 4).symm
    have hval : betaCoeff (N + 1) =
        if (N + 1) % 4 = 1 then 1 else if (N + 1) % 4 = 3 then -1 else 0 := by
      simp only [betaCoeff]
      rw [hcast]
      rcases hmod with h0 | h1 | h2 | h3
      · rw [h0]; simp [betaChar0]
      · rw [h1]; simp [betaChar1]
      · rw [h2]; simp [betaChar2]
      · rw [h3]; simp [betaChar3]
    rw [hsum, hval, ih]
    rcases hmod with h0 | h1 | h2 | h3
    · have g : N % 4 = 3 := by omega
      rw [h0, g]; norm_num
    · have g : N % 4 = 0 := by omega
      rw [h1, g]; norm_num
    · have g : N % 4 = 1 := by omega
      rw [h2, g]; norm_num
    · have g : N % 4 = 2 := by omega
      rw [h3, g]; norm_num

private theorem betaCoeff_sum_bound (N : ℕ) : ‖∑ n ∈ Finset.Icc 0 N, betaCoeff n‖ ≤ 1 := by
  rw [betaCoeff_sum_char]
  split <;> simp

/-- Norm of a complex power of a nonnegative real cast. -/
private theorem norm_ofReal_cpow_aux (t : ℝ) (w : ℂ) (ht : 1 ≤ t) :
    ‖(((t:ℝ)):ℂ)^w‖ = (t:ℝ)^(w.re) := by
  have htpos : (0:ℝ) < t := lt_of_lt_of_le one_pos ht
  have ht0 : (((t:ℝ)):ℂ) ≠ 0 := by exact_mod_cast ne_of_gt htpos
  have hexp : (((t:ℝ)):ℂ) = Complex.exp (((Real.log t : ℝ)):ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log htpos]
  have him : ((((Real.log t : ℝ)):ℂ)).im = 0 := Complex.ofReal_im _
  have h1 : -Real.pi < ((((Real.log t : ℝ)):ℂ)).im := by
    rw [him]; linarith [Real.pi_pos]
  have h2 : ((((Real.log t : ℝ)):ℂ)).im ≤ Real.pi := by
    rw [him]; exact le_of_lt Real.pi_pos
  rw [hexp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp h1 h2, Complex.norm_exp]
  have hre : (((((Real.log t : ℝ)):ℂ)) * w).re = Real.log t * w.re := by
    simp [Complex.mul_re]
  rw [hre, ← Real.rpow_def_of_pos htpos]

/-- Abel summation for the beta coefficients: raw integral form of the limit. -/
private theorem betaIcc_tendsto_raw (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 0 N, ((((n : ℝ)):ℂ)^(-s)) * betaCoeff n)
      atTop (𝓝 (0 - ∫ t : ℝ in Set.Ioi 1,
        deriv (fun t : ℝ => (((t:ℝ)):ℂ)^(-s)) t *
          ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, betaCoeff k)) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have hsm : -s ≠ 0 := neg_ne_zero.mpr hs0
  have hderiv : ∀ t ∈ Set.Ici (1:ℝ),
      DifferentiableAt ℝ (fun t : ℝ => (((t:ℝ)):ℂ)^(-s)) t := by
    intro t ht
    rw [Set.mem_Ici] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos ht)
    exact (hasDerivAt_ofReal_cpow_const ht0 hsm).differentiableAt
  have hder : ∀ t : ℝ, 1 ≤ t →
      deriv (fun t : ℝ => (((t:ℝ)):ℂ)^(-s)) t = -s * ((((t:ℝ)):ℂ)^(-s-1)) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos ht)
    exact (hasDerivAt_ofReal_cpow_const ht0 hsm).deriv
  have hcont : ContinuousOn (fun t : ℝ => -s * ((((t:ℝ)):ℂ)^(-s-1))) (Set.Ici 1) := by
    apply ContinuousOn.mul continuousOn_const
    intro t ht
    rw [Set.mem_Ici] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos ht)
    have h1s : -s - 1 ≠ 0 := by
      intro h
      have hre : (-s - 1).re = 0 := by rw [h]; rfl
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re] at hre
      linarith
    exact ((hasDerivAt_ofReal_cpow_const ht0 h1s).differentiableAt).continuousAt.continuousWithinAt
  have hloc : MeasureTheory.LocallyIntegrableOn
      (deriv (fun t : ℝ => (((t:ℝ)):ℂ)^(-s))) (Set.Ici 1) MeasureTheory.volume := by
    apply MeasureTheory.LocallyIntegrableOn.congr _
      (hcont.locallyIntegrableOn measurableSet_Ici)
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
    rw [Set.mem_Ici] at ht
    exact ((hasDerivAt_ofReal_cpow_const
      (ne_of_gt (lt_of_lt_of_le one_pos ht)) hsm).deriv).symm
  have hlim : Tendsto
      (fun n : ℕ => ((((n:ℝ)):ℂ)^(-s)) * ∑ k ∈ Finset.Icc 0 n, betaCoeff k)
      atTop (nhds 0) := by
    have hbound : ∀ n : ℕ,
        ‖((((n:ℝ)):ℂ)^(-s)) * ∑ k ∈ Finset.Icc 0 n, betaCoeff k‖ ≤
          (n:ℝ)^(-s.re) := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · rw [Finset.Icc_self, Finset.sum_singleton, betaCoeff_zero, mul_zero, norm_zero]
        exact Real.rpow_nonneg (Nat.cast_nonneg 0) _
      · have h1 : ‖((((n:ℝ)):ℂ)^(-s))‖ = (n:ℝ)^(-s.re) := by
          rw [Complex.ofReal_natCast,
            Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
            Complex.neg_re]
        rw [norm_mul, h1]
        calc (n:ℝ)^(-s.re) * ‖∑ k ∈ Finset.Icc 0 n, betaCoeff k‖
            ≤ (n:ℝ)^(-s.re) * 1 :=
              mul_le_mul_of_nonneg_left (betaCoeff_sum_bound n)
                (Real.rpow_nonneg (Nat.cast_nonneg n) _)
          _ = (n:ℝ)^(-s.re) := mul_one _
    have htend : Tendsto (fun n : ℕ => (n:ℝ)^(-s.re)) atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hs).comp tendsto_natCast_atTop_atTop
    exact squeeze_zero_norm hbound htend
  have hbig : (fun t : ℝ => deriv (fun u : ℝ => (((u:ℝ)):ℂ)^(-s)) t *
        ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, betaCoeff k) =O[atTop]
      (fun t : ℝ => (t:ℝ)^(-s.re-1)) := by
    apply Asymptotics.IsBigO.of_bound ‖s‖
    filter_upwards [Filter.eventually_ge_atTop 1] with t ht
    have ht1 : (1:ℝ) ≤ t := ht
    rw [hder t ht1]
    have hn1 : ‖((((t:ℝ)):ℂ)^(-s-1))‖ = (t:ℝ)^(-s.re-1) := by
      have e : (-s - 1).re = -s.re - 1 := by
        simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
      rw [norm_ofReal_cpow_aux t (-s-1) ht1, e]
    rw [norm_mul, norm_mul, hn1, norm_neg, mul_assoc]
    have hA1 : (t:ℝ)^(-s.re-1) * ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, betaCoeff k‖ ≤
        (t:ℝ)^(-s.re-1) * 1 :=
      mul_le_mul_of_nonneg_left (betaCoeff_sum_bound _)
        (Real.rpow_nonneg (le_trans zero_le_one ht1) _)
    calc ‖s‖ * ((t:ℝ)^(-s.re-1) * ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, betaCoeff k‖)
        ≤ ‖s‖ * ((t:ℝ)^(-s.re-1) * 1) :=
          mul_le_mul_of_nonneg_left hA1 (norm_nonneg _)
      _ = ‖s‖ * ‖(t:ℝ)^(-s.re-1)‖ := by
          rw [mul_one, Real.norm_eq_abs,
            abs_of_nonneg (Real.rpow_nonneg (le_trans zero_le_one ht1) _)]
  have hint : MeasureTheory.IntegrableAtFilter (fun t : ℝ => (t:ℝ)^(-s.re-1))
      atTop MeasureTheory.volume := by
    rw [integrableAtFilter_rpow_atTop_iff]
    linarith
  exact tendsto_sum_mul_atTop_nhds_one_sub_integral₀ betaCoeff betaCoeff_zero hderiv
    hloc hlim hbig hint

private theorem betaCoeff_odd (k : ℕ) : betaCoeff (2 * k + 1) = (-1 : ℂ) ^ k := by
  have hmod : (2 * k + 1) % 4 = 1 ∨ (2 * k + 1) % 4 = 3 := by omega
  have hcast : (((2 * k + 1 : ℕ)) : ZMod 4) = ((((2 * k + 1) % 4 : ℕ)) : ZMod 4) :=
    (ZMod.natCast_mod (2 * k + 1) 4).symm
  simp only [betaCoeff]
  rw [hcast]
  rcases hmod with h1 | h3
  · rw [h1]
    simp only [Nat.cast_one, betaChar1]
    have hk : Even k := Nat.even_iff.mpr (by omega)
    rw [hk.neg_one_pow]
  · rw [h3]
    simp only [Nat.cast_ofNat, betaChar3]
    have hk : Odd k := Nat.odd_iff.mpr (by omega)
    rw [hk.neg_one_pow]

private theorem betaCoeff_even (k : ℕ) : betaCoeff (2 * k) = 0 := by
  have hmod : (2 * k) % 4 = 0 ∨ (2 * k) % 4 = 2 := by omega
  have hcast : (((2 * k : ℕ)) : ZMod 4) = ((((2 * k) % 4 : ℕ)) : ZMod 4) :=
    (ZMod.natCast_mod (2 * k) 4).symm
  simp only [betaCoeff]
  rw [hcast]
  rcases hmod with h0 | h2
  · rw [h0]; simp only [Nat.cast_zero, betaChar0]
  · rw [h2]; simp only [Nat.cast_ofNat, betaChar2]

private theorem betaTerm_eq (s : ℂ) (k : ℕ) : chapter7DirichletBetaTerm s k =
    (-1 : ℂ) ^ k * ((((2 * k + 1 : ℕ)) : ℂ) ^ s)⁻¹ := by
  simp only [chapter7DirichletBetaTerm, div_eq_mul_inv]
  congr 1

private theorem betaPartialSum_eq (s : ℂ) (N : ℕ) :
    chapter7DirichletBetaPartialSum s N =
      ∑ n ∈ Finset.Icc 0 (2 * N), ((((n : ℝ)):ℂ)^(-s)) * betaCoeff n := by
  induction N with
  | zero =>
    simp [chapter7DirichletBetaPartialSum, chapter7DirichletBetaTerm, betaCoeff_zero]
  | succ N ih =>
    have hsplit : Finset.Icc 0 (2 * (N + 1)) =
        Finset.Icc 0 (2 * N) ∪ {2 * N + 1, 2 * (N + 1)} := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton]
      omega
    have hdis : Disjoint (Finset.Icc 0 (2 * N)) {2 * N + 1, 2 * (N + 1)} := by
      rw [Finset.disjoint_left]
      intro a ha hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      simp only [Finset.mem_Icc] at ha
      omega
    have hodd : ((((2 * N + 1 : ℕ)):ℝ):ℂ)^(-s) * betaCoeff (2 * N + 1) =
        chapter7DirichletBetaTerm s N := by
      rw [betaCoeff_odd, betaTerm_eq s N, Complex.ofReal_natCast, Complex.cpow_neg]
      ring
    have heven : ((((2 * (N + 1) : ℕ)):ℝ):ℂ)^(-s) * betaCoeff (2 * (N + 1)) = 0 := by
      rw [betaCoeff_even]
      exact mul_zero _
    have hrec : chapter7DirichletBetaPartialSum s (N + 1) =
        chapter7DirichletBetaPartialSum s N + chapter7DirichletBetaTerm s N := by
      simp only [chapter7DirichletBetaPartialSum, Finset.sum_range_succ]
    rw [hrec, ih, hsplit, Finset.sum_union hdis,
      Finset.sum_pair (by omega : 2 * N + 1 ≠ 2 * (N + 1))]
    change (∑ n ∈ Finset.Icc 0 (2 * N), ((((n : ℝ)):ℂ)^(-s)) * betaCoeff n) +
        chapter7DirichletBetaTerm s N =
      (∑ n ∈ Finset.Icc 0 (2 * N), ((((n : ℝ)):ℂ)^(-s)) * betaCoeff n) +
        ((((((2 * N + 1 : ℕ)):ℝ):ℂ)^(-s)) * betaCoeff (2 * N + 1) +
        (((((2 * (N + 1) : ℕ)):ℝ):ℂ)^(-s)) * betaCoeff (2 * (N + 1)))
    rw [hodd, heven, add_zero]

/-- Convergence of the Dirichlet beta partial sums for `1 < s.re`.
This is the `Re s > 1` case of the second conjunct, proved via the
`L`-series `HasSum`. -/
private theorem beta_tendsto_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    Tendsto (chapter7DirichletBetaPartialSum s) atTop
      (𝓝 (chapter7DirichletBeta s)) := by
  have hNe : NeZero 4 := ⟨by decide⟩
  have hbeta : chapter7DirichletBeta s =
      LSeries (fun x => chapter7BetaCharacter (↑x : ZMod 4)) s :=
    ZMod.LFunction_eq_LSeries _ hs
  have hsumm : LSeriesSummable (fun x => chapter7BetaCharacter (↑x : ZMod 4)) s :=
    ZMod.LSeriesSummable_of_one_lt_re _ hs
  have hHas : HasSum
      (LSeries.term (fun x => chapter7BetaCharacter (↑x : ZMod 4)) s)
      (chapter7DirichletBeta s) := by
    rw [hbeta]
    exact hsumm.LSeriesHasSum
  have hrange : Tendsto
      (fun N => ∑ i ∈ Finset.range N,
        LSeries.term (fun x => chapter7BetaCharacter (↑x : ZMod 4)) s i)
      atTop (𝓝 (chapter7DirichletBeta s)) :=
    hHas.tendsto_sum_nat
  have hterm : ∀ n : ℕ, ((((n : ℝ)) : ℂ) ^ (-s)) * betaCoeff n =
      LSeries.term (fun x => chapter7BetaCharacter (↑x : ZMod 4)) s n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [betaCoeff_zero, mul_zero]
      exact (LSeries.term_zero _ _).symm
    · rw [LSeries.term_of_ne_zero hn]
      show ((((n : ℝ)) : ℂ) ^ (-s)) * betaCoeff n =
        chapter7BetaCharacter (↑n : ZMod 4) / (↑n : ℂ) ^ s
      rw [show betaCoeff n = chapter7BetaCharacter (↑n : ZMod 4) from rfl,
        Complex.ofReal_natCast, Complex.cpow_neg, div_eq_mul_inv, mul_comm]
  have hIcc : Tendsto
      (fun M : ℕ => ∑ n ∈ Finset.Icc 0 M, ((((n : ℝ)) : ℂ) ^ (-s)) * betaCoeff n)
      atTop (𝓝 (chapter7DirichletBeta s)) := by
    have heq : (fun M : ℕ => ∑ n ∈ Finset.Icc 0 M,
          ((((n : ℝ)) : ℂ) ^ (-s)) * betaCoeff n) =
        (fun N => ∑ i ∈ Finset.range N,
          LSeries.term (fun x => chapter7BetaCharacter (↑x : ZMod 4)) s i) ∘
          (fun M : ℕ => M + 1) := by
      funext M
      change (∑ n ∈ Finset.Icc 0 M, ((((n : ℝ)) : ℂ) ^ (-s)) * betaCoeff n) =
        ∑ i ∈ Finset.range (M + 1),
          LSeries.term (fun x => chapter7BetaCharacter (↑x : ZMod 4)) s i
      rw [← Finset.sum_congr rfl (fun n _ => hterm n)]
      congr 1
      ext n
      simp only [Finset.mem_Icc, Finset.mem_range]
      omega
    rw [heq]
    apply hrange.comp
    rw [Filter.tendsto_atTop]
    intro b
    rw [Filter.eventually_atTop]
    exact ⟨b, fun M hM => by omega⟩
  have hcomp : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    Filter.Tendsto.const_mul_atTop' (by norm_num) tendsto_id
  have hlim := hIcc.comp hcomp
  have hfun : ((fun M : ℕ =>
        ∑ n ∈ Finset.Icc 0 M, ((((n : ℝ)) : ℂ) ^ (-s)) * betaCoeff n) ∘
      (fun N : ℕ => 2 * N)) =
      chapter7DirichletBetaPartialSum s :=
    funext (fun N => (betaPartialSum_eq s N).symm)
  rwa [hfun] at hlim

/-- Step function of beta-coefficient partial sums, for the Mellin argument. -/
private def betaStepFunc : ℝ → ℂ :=
  Set.indicator (Set.Ioi (1 : ℝ)) (fun t => ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, betaCoeff k)

private theorem betaStepFunc_bound (t : ℝ) : ‖betaStepFunc t‖ ≤ 1 := by
  unfold betaStepFunc
  by_cases ht : t ∈ Set.Ioi (1 : ℝ)
  · rw [Set.indicator_of_mem ht]
    exact betaCoeff_sum_bound _
  · rw [Set.indicator_of_notMem ht]
    simp

private theorem betaStepFunc_measurable : Measurable betaStepFunc := by
  unfold betaStepFunc
  apply Measurable.indicator _ measurableSet_Ioi
  change Measurable ((fun j : ℕ => ∑ k ∈ Finset.Icc 0 j, betaCoeff k) ∘ Nat.floor)
  exact (measurable_of_countable _).comp Nat.measurable_floor

private theorem betaStepFunc_locallyIntegrable :
    MeasureTheory.LocallyIntegrableOn betaStepFunc (Set.Ioi 0) MeasureTheory.volume := by
  intro x hx
  refine ⟨Set.Ioo 0 (x + 1), mem_nhdsWithin_of_mem_nhds ?_, ?_⟩
  · apply isOpen_Ioo.mem_nhds
    rw [Set.mem_Ioo]
    exact ⟨Set.mem_Ioi.mp hx, by linarith⟩
  · have hfin : MeasureTheory.volume (Set.Ioo 0 (x + 1)) < ⊤ := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_lt_top
    have hae : MeasureTheory.AEStronglyMeasurable betaStepFunc
        (MeasureTheory.volume.restrict (Set.Ioo 0 (x + 1))) :=
      betaStepFunc_measurable.aestronglyMeasurable.restrict
    have hb : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.Ioo 0 (x + 1)),
        ‖betaStepFunc t‖ ≤ 1 :=
      Filter.Eventually.of_forall (fun t => betaStepFunc_bound t)
    exact MeasureTheory.IntegrableOn.of_bound hfin hae 1 hb

private theorem betaStepFunc_top :
    betaStepFunc =O[atTop] (fun x : ℝ => x ^ (-(0 : ℝ))) := by
  rw [show (-(0 : ℝ)) = 0 from neg_zero]
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards with t
  rw [Real.rpow_zero]
  simpa using betaStepFunc_bound t

private theorem betaStepFunc_zero (b : ℝ) :
    betaStepFunc =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-b)) := by
  apply Asymptotics.IsBigO.of_bound 0
  have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Set.Iio (1 : ℝ) := Iio_mem_nhds (by norm_num)
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Iio (1 : ℝ) :=
    h1.filter_mono nhdsWithin_le_nhds
  filter_upwards [h2] with t ht
  have h0 : betaStepFunc t = 0 := by
    unfold betaStepFunc
    rw [Set.mem_Iio] at ht
    have hnt : t ∉ Set.Ioi (1 : ℝ) := by
      rw [Set.mem_Ioi]
      linarith
    exact Set.indicator_of_notMem hnt _
  simp [h0]

/-- The Mellin-side function, holomorphic on `Re s > 0`. -/
private def betaMellinFunc : ℂ → ℂ := fun s => s * mellin betaStepFunc (-s)

private theorem betaMellin_differentiableOn :
    DifferentiableOn ℂ betaMellinFunc {s : ℂ | 0 < s.re} := by
  intro s hs
  have hs0 : 0 < s.re := hs
  have hmel : DifferentiableAt ℂ (mellin betaStepFunc) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow betaStepFunc_locallyIntegrable
      betaStepFunc_top (by simp only [Complex.neg_re]; linarith)
      (betaStepFunc_zero (-s.re - 1)) (by simp only [Complex.neg_re]; linarith)
  have hcomp : DifferentiableAt ℂ (fun s : ℂ => mellin betaStepFunc (-s)) s :=
    hmel.comp s differentiableAt_id.neg
  have hFs : DifferentiableAt ℂ (fun s : ℂ => s * mellin betaStepFunc (-s)) s :=
    differentiableAt_id.mul hcomp
  change DifferentiableWithinAt ℂ betaMellinFunc {s : ℂ | 0 < s.re} s
  unfold betaMellinFunc
  exact hFs.differentiableWithinAt

private theorem betaMellin_analytic :
    AnalyticOnNhd ℂ betaMellinFunc {s : ℂ | 0 < s.re} :=
  betaMellin_differentiableOn.analyticOnNhd (Complex.isOpen_re_gt 0)

/-- The Abel integral limit equals the Mellin-side function. -/
private theorem betaAbel_eq_mellin (s : ℂ) (hs : 0 < s.re) :
    (0 - ∫ t : ℝ in Set.Ioi 1,
        deriv (fun y : ℝ => ((((y : ℝ)) : ℂ) ^ (-s))) t *
          ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, betaCoeff k) =
      betaMellinFunc s := by
  have hs0 : -s ≠ 0 := by
    intro h
    have hss : s = 0 := by simpa using h
    rw [hss] at hs
    simp at hs
  have hderiv : ∀ t ∈ Set.Ioi (1 : ℝ),
      deriv (fun y : ℝ => ((((y : ℝ)) : ℂ) ^ (-s))) t =
        -s * ((((t : ℝ)) : ℂ) ^ (-s - 1)) := by
    intro t ht
    have ht0 : (t : ℝ) ≠ 0 := by
      rw [Set.mem_Ioi] at ht
      linarith
    exact (hasDerivAt_ofReal_cpow_const ht0 hs0).deriv
  have hDeq : (∫ t : ℝ in Set.Ioi 1,
        deriv (fun y : ℝ => ((((y : ℝ)) : ℂ) ^ (-s))) t *
          ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, betaCoeff k) =
      (-s) * (∫ t : ℝ in Set.Ioi 1, ((((t : ℝ)) : ℂ) ^ (-s - 1)) *
        (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, betaCoeff k)) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change deriv (fun y : ℝ => ((((y : ℝ)) : ℂ) ^ (-s))) t *
          ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, betaCoeff k =
        -s * (((((t : ℝ)) : ℂ) ^ (-s - 1)) *
          ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, betaCoeff k)
    rw [hderiv t ht]
    ring
  have e2 : (fun t : ℝ => ((((t : ℝ)) : ℂ) ^ ((-s) - 1)) • betaStepFunc t) =
      (fun t : ℝ => Set.indicator (Set.Ioi 1)
        (fun u : ℝ => ((((u : ℝ)) : ℂ) ^ ((-s) - 1)) •
          (∑ k ∈ Finset.Icc 0 ⌊u⌋₊, betaCoeff k)) t) := by
    funext t
    show ((((t : ℝ)) : ℂ) ^ ((-s) - 1)) • betaStepFunc t =
      Set.indicator (Set.Ioi 1)
        (fun u : ℝ => ((((u : ℝ)) : ℂ) ^ ((-s) - 1)) •
          (∑ k ∈ Finset.Icc 0 ⌊u⌋₊, betaCoeff k)) t
    unfold betaStepFunc
    by_cases ht : t ∈ Set.Ioi (1 : ℝ)
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, smul_zero]
  have hMell : betaMellinFunc s = s *
      (∫ t : ℝ in Set.Ioi 1, ((((t : ℝ)) : ℂ) ^ (-s - 1)) *
        (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, betaCoeff k)) := by
    have e1 : betaMellinFunc s = s * mellin betaStepFunc (-s) := rfl
    rw [e1]
    congr 1
    have e3 : mellin betaStepFunc (-s) =
        ∫ t : ℝ in Set.Ioi (0 : ℝ), ((((t : ℝ)) : ℂ) ^ ((-s) - 1)) • betaStepFunc t := rfl
    rw [e3, e2, MeasureTheory.setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_self_of_subset_right
        (Set.Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change ((((t : ℝ)) : ℂ) ^ ((-s) - 1)) •
          (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, betaCoeff k) =
        ((((t : ℝ)) : ℂ) ^ (-s - 1)) *
          (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, betaCoeff k)
    rw [smul_eq_mul]
  rw [hDeq, hMell]
  ring

/-- Abel summation for the beta coefficients: the `Icc` partial sums converge
to an integral limit for `0 < s.re`. -/
private theorem betaIcc_abel_limit (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun M : ℕ => ∑ n ∈ Finset.Icc 0 M, ((((n : ℝ)) : ℂ) ^ (-s)) * betaCoeff n)
      atTop (𝓝 (0 - ∫ t : ℝ in Set.Ioi 1,
        deriv (fun y : ℝ => ((((y : ℝ)) : ℂ) ^ (-s))) t *
          ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, betaCoeff k)) := by
  refine tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (c := betaCoeff)
    (f := fun y : ℝ => ((((y : ℝ)) : ℂ) ^ (-s)))
    (g := fun t : ℝ => ‖s‖ * t ^ (-s.re - 1)) betaCoeff_zero ?_ ?_ ?_ ?_ ?_
  · intro t ht
    have ht0 : (t : ℝ) ≠ 0 := by
      rw [Set.mem_Ici] at ht
      linarith
    have hs0 : -s ≠ 0 := by
      intro h
      have hss : s = 0 := by simpa using h
      rw [hss] at hs
      simp at hs
    exact (hasDerivAt_ofReal_cpow_const ht0 hs0).differentiableAt
  · have hs0B : -s ≠ 0 := by
      intro h
      have hss : s = 0 := by simpa using h
      rw [hss] at hs
      simp at hs
    have hderiv_eq : ∀ t ∈ Set.Ici (1 : ℝ),
        deriv (fun y : ℝ => ((((y : ℝ)) : ℂ) ^ (-s))) t =
          -s * ((((t : ℝ)) : ℂ) ^ (-s - 1)) := by
      intro t ht
      have ht0 : (t : ℝ) ≠ 0 := by
        rw [Set.mem_Ici] at ht
        linarith
      exact (hasDerivAt_ofReal_cpow_const ht0 hs0B).deriv
    have hdiff2 : ∀ t ∈ Set.Ici (1 : ℝ),
        DifferentiableAt ℝ (fun y : ℝ => ((((y : ℝ)) : ℂ) ^ (-s - 1))) t := by
      intro t ht
      have ht0 : (t : ℝ) ≠ 0 := by
        rw [Set.mem_Ici] at ht
        linarith
      have hs1 : -s - 1 ≠ 0 := by
        intro h
        have h2 := congrArg Complex.re h
        simp only [Complex.sub_re, Complex.neg_re, Complex.one_re,
          Complex.zero_re] at h2
        linarith
      exact (hasDerivAt_ofReal_cpow_const ht0 hs1).differentiableAt
    have hdiffOn : DifferentiableOn ℝ
        (fun y : ℝ => ((((y : ℝ)) : ℂ) ^ (-s - 1))) (Set.Ici 1) :=
      fun t ht => (hdiff2 t ht).differentiableWithinAt
    have hcont : ContinuousOn
        (fun t : ℝ => -s * ((((t : ℝ)) : ℂ) ^ (-s - 1))) (Set.Ici 1) :=
      continuousOn_const.mul hdiffOn.continuousOn
    have hloc : MeasureTheory.LocallyIntegrableOn
        (fun t : ℝ => -s * ((((t : ℝ)) : ℂ) ^ (-s - 1)))
        (Set.Ici 1) MeasureTheory.volume :=
      hcont.locallyIntegrableOn measurableSet_Ici
    have hae : (fun t : ℝ => -s * ((((t : ℝ)) : ℂ) ^ (-s - 1))) =ᵐ[
        MeasureTheory.volume.restrict (Set.Ici 1)]
        (fun t => deriv (fun y : ℝ => ((((y : ℝ)) : ℂ) ^ (-s))) t) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
      exact (hderiv_eq t ht).symm
    exact MeasureTheory.LocallyIntegrableOn.congr hae hloc
  · have hbound : ∀ n : ℕ,
        ‖((((n : ℝ)) : ℂ) ^ (-s)) * ∑ k ∈ Finset.Icc 0 n, betaCoeff k‖ ≤
          (n : ℝ) ^ (-s.re) := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · have hsum : ∑ k ∈ Finset.Icc 0 0, betaCoeff k = 0 := by
          simp [betaCoeff_zero]
        rw [hsum, mul_zero, norm_zero]
        exact Real.rpow_nonneg (Nat.cast_nonneg _) _
      · have hpos : 0 < n := Nat.pos_of_ne_zero hn
        calc ‖((((n : ℝ)) : ℂ) ^ (-s)) * ∑ k ∈ Finset.Icc 0 n, betaCoeff k‖
              = ‖((((n : ℝ)) : ℂ) ^ (-s))‖ * ‖∑ k ∈ Finset.Icc 0 n, betaCoeff k‖ :=
            norm_mul _ _
          _ ≤ ‖((((n : ℝ)) : ℂ) ^ (-s))‖ * 1 :=
            mul_le_mul_of_nonneg_left (betaCoeff_sum_bound n) (norm_nonneg _)
          _ = (n : ℝ) ^ (-s.re) := by
            rw [mul_one, Complex.ofReal_natCast]
            have h := Complex.norm_natCast_cpow_of_pos hpos (-s)
            simpa using h
    have hlim0 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-s.re)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hs).comp tendsto_natCast_atTop_atTop
    exact squeeze_zero_norm hbound hlim0
  · apply Asymptotics.IsBigO.of_bound 1
    have hs0 : -s ≠ 0 := by
      intro h
      have hss : s = 0 := by simpa using h
      rw [hss] at hs
      simp at hs
    have key : ∀ t : ℝ, 1 ≤ t →
        ‖deriv (fun y : ℝ => ((((y : ℝ)) : ℂ) ^ (-s))) t *
            ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, betaCoeff k‖ ≤
          1 * ‖‖s‖ * t ^ (-s.re - 1)‖ := by
      intro t ht
      have ht0 : (0 : ℝ) < t := by linarith
      have hderiv : deriv (fun y : ℝ => ((((y : ℝ)) : ℂ) ^ (-s))) t =
          -s * ((((t : ℝ)) : ℂ) ^ (-s - 1)) := by
        have ht0' : (t : ℝ) ≠ 0 := ne_of_gt ht0
        exact (hasDerivAt_ofReal_cpow_const ht0' hs0).deriv
      have hnorm_g : ‖‖s‖ * t ^ (-s.re - 1)‖ = ‖s‖ * t ^ (-s.re - 1) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [hnorm_g, one_mul, hderiv, norm_mul, norm_mul, norm_neg,
        Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      have hre : (-s - 1).re = -s.re - 1 := by simp
      rw [hre]
      have hA := betaCoeff_sum_bound ⌊t⌋₊
      calc ‖s‖ * t ^ (-s.re - 1) * ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, betaCoeff k‖
          ≤ ‖s‖ * t ^ (-s.re - 1) * 1 :=
            mul_le_mul_of_nonneg_left hA (by positivity)
        _ = ‖s‖ * t ^ (-s.re - 1) := mul_one _
    rw [Filter.eventually_atTop]
    exact ⟨1, fun b hb => key b hb⟩
  · have he : -s.re - 1 < -1 := by linarith
    obtain ⟨u, hu, huint⟩ := integrableAtFilter_rpow_atTop_iff.mpr he
    refine ⟨u, hu, ?_⟩
    exact MeasureTheory.Integrable.const_mul huint ‖s‖

/-- The Mellin-side function agrees with `β` for `1 < s.re`. -/
private theorem betaMellin_eq_beta_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    betaMellinFunc s = chapter7DirichletBeta s := by
  have hs0 : 0 < s.re := by linarith
  have habel := betaIcc_abel_limit s hs0
  rw [betaAbel_eq_mellin s hs0] at habel
  have hbeta := beta_tendsto_of_one_lt_re s hs
  have hcomp : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    Filter.Tendsto.const_mul_atTop' (by norm_num) tendsto_id
  have hsub := habel.comp hcomp
  have hfun : ((fun M : ℕ => ∑ n ∈ Finset.Icc 0 M, ((((n : ℝ)) : ℂ) ^ (-s)) * betaCoeff n) ∘
      (fun N : ℕ => 2 * N)) =
      chapter7DirichletBetaPartialSum s :=
    funext (fun N => (betaPartialSum_eq s N).symm)
  rw [hfun] at hsub
  exact tendsto_nhds_unique hsub hbeta

/-- The Mellin-side function equals `β` on all of `Re s > 0`. -/
private theorem betaMellin_eq_beta (s : ℂ) (hs : 0 < s.re) :
    betaMellinFunc s = chapter7DirichletBeta s := by
  have hB : AnalyticOnNhd ℂ chapter7DirichletBeta {s : ℂ | 0 < s.re} :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr betaDirichletEntire).mono
      (Set.subset_univ _)
  have hpre : IsPreconnected {s : ℂ | 0 < s.re} :=
    (convex_halfSpace_re_gt 0).isPreconnected
  have hev : betaMellinFunc =ᶠ[nhds 2] chapter7DirichletBeta := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := Complex.isOpen_re_gt 1
    have h2 : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by norm_num
    filter_upwards [hopen.mem_nhds h2] with z hz
    exact betaMellin_eq_beta_of_one_lt_re z hz
  have hEq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    betaMellin_analytic hB hpre (show (2 : ℂ) ∈ {s : ℂ | 0 < s.re} by norm_num) hev
  exact hEq hs

/-- Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 7.

Proves `Wanted` entry `ramanujan_part1_ch7_entry17_bernoullipolysymmetry`.
-/
theorem ramanujan_part1_ch7_entry17_bernoullipolysymmetry :
    Differentiable ℂ chapter7DirichletBeta ∧
      (∀ s : ℂ, 0 < s.re →
        Tendsto (chapter7DirichletBetaPartialSum s) atTop
          (𝓝 (chapter7DirichletBeta s))) ∧
      MeromorphicOn chapter7EulerStar Set.univ ∧
      MeromorphicOn chapter7Entry17Left Set.univ ∧
      MeromorphicOn chapter7Entry17Right Set.univ ∧
      chapter7Entry17Left =ᶠ[codiscrete ℂ] chapter7Entry17Right := by
  refine ⟨betaDirichletEntire, ?_, eulerStar_mero, entry17Left_mero, entry17Right_mero,
    entry17_eventual⟩
  intro s hs
  have habel := betaIcc_abel_limit s hs
  rw [betaAbel_eq_mellin s hs] at habel
  rw [betaMellin_eq_beta s hs] at habel
  have hcomp : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    Filter.Tendsto.const_mul_atTop' (by norm_num) tendsto_id
  have hlim := habel.comp hcomp
  have hfun : ((fun M : ℕ => ∑ n ∈ Finset.Icc 0 M, ((((n : ℝ)) : ℂ) ^ (-s)) * betaCoeff n) ∘
      (fun N : ℕ => 2 * N)) =
      chapter7DirichletBetaPartialSum s :=
    funext (fun N => (betaPartialSum_eq s N).symm)
  rwa [hfun] at hlim

end
end Entry17Bernoullipolysymmetry
end MathlibExt.Analysis.Ramanujan.Part1Ch7
end
