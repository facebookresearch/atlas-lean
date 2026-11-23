/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

section
/-!
# Koebe one-quarter theorem
-/

namespace MathlibExt.Analysis.Complex.KoebeQuarterWanted

open MeasureTheory

private theorem exists_log_of_ne_zero_on_ball
    (c : ℂ) (R : ℝ) (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g (Metric.ball c R))
    (hne : ∀ z ∈ Metric.ball c R, g z ≠ 0)
    (a : ℂ) (ha : Complex.exp a = g c)
    (hmem : c ∈ Metric.ball c R) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L (Metric.ball c R) ∧ L c = a ∧
      ∀ z ∈ Metric.ball c R, Complex.exp (L z) = g z := by
  have hopen : IsOpen (Metric.ball c R) := Metric.isOpen_ball
  have hR : 0 < R := by
    rw [Metric.mem_ball, dist_self] at hmem
    exact hmem
  have hg' : DifferentiableOn ℂ (deriv g) (Metric.ball c R) :=
    hg.deriv hopen
  have hlog : DifferentiableOn ℂ (fun z => deriv g z / g z) (Metric.ball c R) :=
    hg'.div hg hne
  have hexact : Complex.IsExactOn (fun z => deriv g z / g z) (Metric.ball c R) :=
    hlog.isExactOn_ball
  obtain ⟨L, hLc, hL⟩ := hexact.with_val_at c a
  refine ⟨L, ?_, hLc, ?_⟩
  · exact (fun z hz => (hL z hz).differentiableAt.differentiableWithinAt)
  · have hE : ∀ z ∈ Metric.ball c R, Complex.exp (-L z) * g z = 1 := by
      have hEderiv : ∀ z ∈ Metric.ball c R,
          HasDerivAt (fun w => Complex.exp (-L w) * g w) 0 z := by
        intro z hz
        have h1 : HasDerivAt L (deriv g z / g z) z := hL z hz
        have hexp : HasDerivAt (fun w => Complex.exp (-L w))
            (-Complex.exp (-L z) * (deriv g z / g z)) z := by
          have hneg : HasDerivAt (fun w => -L w) (-(deriv g z / g z)) z :=
            h1.neg
          have := hneg.cexp
          simpa [mul_comm] using this
        have hg1 : HasDerivAt g (deriv g z) z :=
          hg.hasDerivAt (hopen.mem_nhds hz)
        have hmul := hexp.mul hg1
        have hgz : g z ≠ 0 := hne z hz
        have hzero : -Complex.exp (-L z) * (deriv g z / g z) * g z +
            Complex.exp (-L z) * deriv g z = 0 := by
          field_simp
          ring
        have hfun : ((fun w => Complex.exp (-L w)) * g) = (fun w => Complex.exp (-L w) * g w) := rfl
        rw [hfun] at hmul
        rw [hzero] at hmul
        exact hmul
      have hEdiff : DifferentiableOn ℂ (fun w => Complex.exp (-L w) * g w) (Metric.ball c R) :=
        fun z hz => (hEderiv z hz).differentiableAt.differentiableWithinAt
      have hEqOn : Set.EqOn (deriv (fun w => Complex.exp (-L w) * g w)) 0 (Metric.ball c R) := by
        intro w hw
        have h := (hEderiv w hw).deriv
        simpa using h
      have hconst : ∀ x ∈ Metric.ball c R, ∀ y ∈ Metric.ball c R,
          (fun w => Complex.exp (-L w) * g w) x = (fun w => Complex.exp (-L w) * g w) y := by
        intro x hx y hy
        exact hopen.is_const_of_deriv_eq_zero
          (convex_ball c R |>.isPreconnected) hEdiff hEqOn hx hy
      have hEc : Complex.exp (-L c) * g c = 1 := by
        rw [← ha]
        rw [← Complex.exp_add]
        simp [hLc]
      intro z hz
      have hcc := hconst z hz c hmem
      simpa [hEc] using hcc
    intro z hz
    have h1 := hE z hz
    have hexp0 : Complex.exp (-L z) ≠ 0 := Complex.exp_ne_zero _
    have h2 : Complex.exp (-L z) * g z = Complex.exp (-L z) * Complex.exp (L z) := by
      rw [h1]
      rw [← Complex.exp_add]
      simp
    have h3 : g z = Complex.exp (L z) := (mul_left_cancel₀ hexp0 h2)
    exact h3.symm

private theorem exists_sqrt_of_univalent
    (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (hinj : Set.InjOn f (Metric.ball (0 : ℂ) 1))
    (h0 : f 0 = 0)
    (hderiv : deriv f 0 = 1) :
    ∃ s : ℂ → ℂ, DifferentiableOn ℂ s (Metric.ball (0 : ℂ) 1) ∧ s 0 = 1 ∧
      (∀ w ∈ Metric.ball (0 : ℂ) 1, s w ≠ 0) ∧
      ∀ w ∈ Metric.ball (0 : ℂ) 1, w * s w ^ 2 = f w := by
  have hmem0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  have hnhds : Metric.ball (0 : ℂ) 1 ∈ nhds (0 : ℂ) :=
    Metric.ball_mem_nhds 0 (by norm_num)
  have hphi : DifferentiableOn ℂ (dslope f 0) (Metric.ball (0 : ℂ) 1) :=
    (Complex.differentiableOn_dslope hnhds).mpr hf
  have hphi0 : dslope f 0 0 = 1 := by rw [dslope_same, hderiv]
  have hmul_eq : ∀ w : ℂ, w * dslope f 0 w = f w := by
    intro w
    have h := sub_smul_dslope f 0 w
    simpa [h0, smul_eq_mul] using h
  have hphine : ∀ w ∈ Metric.ball (0 : ℂ) 1, dslope f 0 w ≠ 0 := by
    intro w hw hcon
    by_cases hw0 : w = 0
    · rw [hw0, hphi0] at hcon; exact one_ne_zero hcon
    · have h2 := hmul_eq w
      rw [hcon, mul_zero] at h2
      have hfw : f w = f 0 := by rw [← h2, h0]
      have heq := hinj hw hmem0 hfw
      exact hw0 heq
  obtain ⟨L, hLdiff, hL0, hLexp⟩ :=
    exists_log_of_ne_zero_on_ball 0 1 (dslope f 0) hphi hphine 0
      (by rw [hphi0, Complex.exp_zero]) hmem0
  refine ⟨fun w => Complex.exp (L w / 2), ?_, ?_, ?_, ?_⟩
  · exact (hLdiff.div_const 2).cexp
  · simp [hL0]
  · intro w _
    exact Complex.exp_ne_zero _
  · intro w hw
    have hsq : (Complex.exp (L w / 2)) ^ 2 = dslope f 0 w := by
      have h1 : Complex.exp (L w / 2) ^ 2 =
          Complex.exp (L w / 2 + L w / 2) := by
        rw [sq, ← Complex.exp_add]
      rw [h1]
      have h2 : L w / 2 + L w / 2 = L w := by ring
      rw [h2, hLexp w hw]
    rw [hsq]
    exact hmul_eq w

private theorem koebe_inv_sqrt_expansion
    (s : ℂ → ℂ)
    (hs : DifferentiableOn ℂ s (Metric.ball (0 : ℂ) 1))
    (hs0 : s 0 = 1)
    (hsne : ∀ w ∈ Metric.ball (0 : ℂ) 1, s w ≠ 0) :
    let k := dslope (fun w => (s w)⁻¹) 0
    DifferentiableOn ℂ k (Metric.ball (0 : ℂ) 1) ∧
    (∀ w : ℂ, (s w)⁻¹ = 1 + w * k w) ∧
    k 0 = -deriv s 0 := by
  have hmem0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  have hnhds : Metric.ball (0 : ℂ) 1 ∈ nhds (0 : ℂ) :=
    Metric.ball_mem_nhds 0 (by norm_num)
  have hinv : DifferentiableOn ℂ (fun w => (s w)⁻¹) (Metric.ball (0 : ℂ) 1) :=
    hs.inv hsne
  have hk : DifferentiableOn ℂ (dslope (fun w => (s w)⁻¹) 0) (Metric.ball (0 : ℂ) 1) :=
    (Complex.differentiableOn_dslope hnhds).mpr hinv
  refine ⟨hk, ?_, ?_⟩
  · intro w
    have h := sub_smul_dslope (fun w => (s w)⁻¹) 0 w
    have h0inv : ((s (0 : ℂ))⁻¹) = 1 := by rw [hs0, inv_one]
    have h2 : w * dslope (fun w => (s w)⁻¹) 0 w = (s w)⁻¹ - 1 := by
      simpa [h0inv, smul_eq_mul, sub_zero] using h
    linear_combination -h2
  · have hds : dslope (fun w => (s w)⁻¹) 0 0
      = deriv (fun w => (s w)⁻¹) 0 := dslope_same _ _
    rw [hds]
    have hs0at : HasDerivAt s (deriv s 0) 0 :=
      hs.hasDerivAt (Metric.isOpen_ball.mem_nhds hmem0)
    have hinv_at := hs0at.inv (by rw [hs0]; exact one_ne_zero)
    have hder : deriv (fun w => (s w)⁻¹) 0 = -deriv s 0 / s 0 ^ 2 :=
      hinv_at.deriv
    rw [hder, hs0]
    simp

private theorem deriv_sqrt_eq_iteratedDeriv_two
    (f s : ℂ → ℂ)
    (hs : DifferentiableOn ℂ s (Metric.ball (0 : ℂ) 1))
    (hs0 : s 0 = 1)
    (heq : ∀ w ∈ Metric.ball (0 : ℂ) 1, w * s w ^ 2 = f w) :
    deriv s 0 = iteratedDeriv 2 f 0 / 4 := by
  have hopen : IsOpen (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball
  have hmem0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  have hnhds : Metric.ball (0 : ℂ) 1 ∈ nhds (0 : ℂ) :=
    Metric.ball_mem_nhds 0 (by norm_num)
  have hev : (fun w => w * s w ^ 2) =ᶠ[nhds (0 : ℂ)] f :=
    Filter.eventually_of_mem hnhds (fun w hw => heq w hw)
  have hiter : iteratedDeriv 2 (fun w => w * s w ^ 2) 0 = iteratedDeriv 2 f 0 :=
    Filter.EventuallyEq.iteratedDeriv_eq 2 hev
  have hs' : DifferentiableOn ℂ (deriv s) (Metric.ball (0 : ℂ) 1) :=
    hs.deriv hopen
  have hsq_at : ∀ w : ℂ, HasDerivAt s (deriv s w) w →
      HasDerivAt (fun w => s w ^ 2) (2 * s w * deriv s w) w := by
    intro w hsw
    have h := hsw.mul hsw
    have hfun : (s * s) = (fun w => s w ^ 2) := by ext x; simp [sq, Pi.mul_apply]
    have hder : deriv s w * s w + s w * deriv s w = 2 * s w * deriv s w := by ring
    rw [hfun, hder] at h
    exact h
  have hderiv1 : ∀ w ∈ Metric.ball (0 : ℂ) 1,
      HasDerivAt (fun w => w * s w ^ 2)
        (s w ^ 2 + w * (2 * s w * deriv s w)) w := by
    intro w hw
    have hsw : HasDerivAt s (deriv s w) w :=
      hs.hasDerivAt (hopen.mem_nhds hw)
    have hsq := hsq_at w hsw
    have hid : HasDerivAt (fun w : ℂ => w) 1 w := hasDerivAt_id w
    have hmul := hid.mul hsq
    have hfun : ((fun w : ℂ => w) * (fun w => s w ^ 2)) = (fun w => w * s w ^ 2) := rfl
    have hder : (1 : ℂ) * s w ^ 2 + w * (2 * s w * deriv s w) =
        s w ^ 2 + w * (2 * s w * deriv s w) := by ring
    rw [hfun, hder] at hmul
    exact hmul
  have h1 : deriv (fun w => w * s w ^ 2) =ᶠ[nhds (0 : ℂ)]
      (fun w => s w ^ 2 + w * (2 * s w * deriv s w)) := by
    apply Filter.eventually_of_mem hnhds
    intro w hw
    exact (hderiv1 w hw).deriv
  have h2 : deriv (deriv (fun w => w * s w ^ 2)) 0 =
      deriv (fun w => s w ^ 2 + w * (2 * s w * deriv s w)) 0 :=
    Filter.EventuallyEq.deriv_eq h1
  have hsw0 : HasDerivAt s (deriv s 0) 0 :=
    hs.hasDerivAt (hopen.mem_nhds hmem0)
  have hsp0 : HasDerivAt (deriv s) (deriv (deriv s) 0) 0 :=
    hs'.hasDerivAt (hopen.mem_nhds hmem0)
  have hsq0 : HasDerivAt (fun w => s w ^ 2) (2 * s 0 * deriv s 0) 0 :=
    hsq_at 0 hsw0
  have hinner : HasDerivAt (fun w : ℂ => 2 * s w * deriv s w)
      (2 * (deriv s 0 * deriv s 0 + s 0 * deriv (deriv s) 0)) 0 := by
    have e1 : HasDerivAt (fun w => s w * deriv s w)
        (deriv s 0 * deriv s 0 + s 0 * deriv (deriv s) 0) 0 :=
      hsw0.mul hsp0 |>.congr_of_eventuallyEq (by filter_upwards with x; simp [Pi.mul_apply])
    have e2 := e1.const_mul (2 : ℂ)
    have hfun12 : (fun w : ℂ => 2 * s w * deriv s w) =ᶠ[nhds (0 : ℂ)]
        (fun y => 2 * (s y * deriv s y)) := by
      filter_upwards with x; ring
    exact e2.congr_of_eventuallyEq hfun12
  have hprod0 : HasDerivAt (fun w : ℂ => w * (2 * s w * deriv s w))
      (2 * s 0 * deriv s 0) 0 := by
    have hmul := (hasDerivAt_id (0 : ℂ)).mul hinner
    have hder_eq : (1 : ℂ) * (2 * s 0 * deriv s 0) +
        id 0 * (2 * (deriv s 0 * deriv s 0 + s 0 * deriv (deriv s) 0)) =
        2 * s 0 * deriv s 0 := by
      simp only [id_eq]
      ring
    rw [hder_eq] at hmul
    have hfun12 : (fun w : ℂ => w * (2 * s w * deriv s w)) =ᶠ[nhds (0 : ℂ)]
        ((id : ℂ → ℂ) * (fun w : ℂ => 2 * s w * deriv s w)) := by
      filter_upwards with x; simp [Pi.mul_apply, id_eq]
    exact hmul.congr_of_eventuallyEq hfun12
  have hsum0 : HasDerivAt (fun w => s w ^ 2 + w * (2 * s w * deriv s w))
      (4 * deriv s 0) 0 := by
    have h := hsq0.add hprod0
    have hder_eq : 2 * s 0 * deriv s 0 + 2 * s 0 * deriv s 0 = 4 * deriv s 0 := by
      rw [hs0]; ring
    rw [hder_eq] at h
    have hfun12 : (fun w => s w ^ 2 + w * (2 * s w * deriv s w)) =ᶠ[nhds (0 : ℂ)]
        ((fun w => s w ^ 2) + (fun w : ℂ => w * (2 * s w * deriv s w))) := by
      filter_upwards with x; simp [Pi.add_apply]
    exact h.congr_of_eventuallyEq hfun12
  have hval : deriv (fun w => s w ^ 2 + w * (2 * s w * deriv s w)) 0 =
      4 * deriv s 0 := hsum0.deriv
  have hiter2 : iteratedDeriv 2 (fun w => w * s w ^ 2) 0 = 4 * deriv s 0 := by
    have e1 : iteratedDeriv 2 (fun w => w * s w ^ 2) =
        deriv (deriv (fun w => w * s w ^ 2)) := by
      have : (2 : ℕ) = 1 + 1 := rfl
      rw [this, iteratedDeriv_succ, iteratedDeriv_one]
    rw [e1, h2, hval]
  rw [hiter] at hiter2
  rw [hiter2]
  ring

private theorem koebe_G_injOn
    (f s k G : ℂ → ℂ)
    (hsne : ∀ w ∈ Metric.ball (0 : ℂ) 1, s w ≠ 0)
    (heq : ∀ w ∈ Metric.ball (0 : ℂ) 1, w * s w ^ 2 = f w)
    (hkinv : ∀ w : ℂ, (s w)⁻¹ = 1 + w * k w)
    (hG : ∀ z : ℂ, G z = z⁻¹ + z * k (z ^ 2))
    (hinj : Set.InjOn f (Metric.ball (0 : ℂ) 1)) :
    (∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → z ^ 2 ∈ Metric.ball (0 : ℂ) 1) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → G z = (z * s (z ^ 2))⁻¹) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → G z ≠ 0) ∧
    Set.InjOn G (Metric.ball (0 : ℂ) 1 \ {0}) := by
  have hsq_mem : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → z ^ 2 ∈ Metric.ball (0 : ℂ) 1 := by
    intro z hz _
    have h1 : ‖z‖ < 1 := by
      have h := Metric.mem_ball.mp hz
      rwa [dist_zero_right] at h
    rw [Metric.mem_ball, dist_zero_right, norm_pow]
    have hnn : 0 ≤ ‖z‖ := norm_nonneg _
    nlinarith [sq_nonneg ‖z‖, sq_nonneg (‖z‖ - 1)]
  have hGinv : ∀ z : ℂ, z ≠ 0 → G z = (z * s (z ^ 2))⁻¹ := by
    intro z hzne
    have h1 := hkinv (z ^ 2)
    rw [hG z, mul_inv, h1]
    field_simp
  refine ⟨hsq_mem, fun z hz hzne => hGinv z hzne, ?_, ?_⟩
  · intro z hz hzne
    rw [hGinv z hzne]
    have hmem2 : z ^ 2 ∈ Metric.ball (0 : ℂ) 1 := hsq_mem z hz hzne
    have hs2 : s (z ^ 2) ≠ 0 := hsne _ hmem2
    exact inv_ne_zero (mul_ne_zero hzne hs2)
  · intro z1 hz1 z2 hz2 heq12
    have hz1m : z1 ∈ Metric.ball (0 : ℂ) 1 := hz1.1
    have hz2m : z2 ∈ Metric.ball (0 : ℂ) 1 := hz2.1
    have hn1 : z1 ≠ 0 := fun h => hz1.2 (Set.mem_singleton_iff.mpr h)
    have hn2 : z2 ≠ 0 := fun h => hz2.2 (Set.mem_singleton_iff.mpr h)
    have hm1 : z1 ^ 2 ∈ Metric.ball (0 : ℂ) 1 := hsq_mem z1 hz1m hn1
    have hm2 : z2 ^ 2 ∈ Metric.ball (0 : ℂ) 1 := hsq_mem z2 hz2m hn2
    have hG1 : G z1 = (z1 * s (z1 ^ 2))⁻¹ := hGinv z1 hn1
    have hG2 : G z2 = (z2 * s (z2 ^ 2))⁻¹ := hGinv z2 hn2
    have h12 : z1 * s (z1 ^ 2) = z2 * s (z2 ^ 2) := by
      rw [hG1, hG2] at heq12
      exact inv_inj.mp heq12
    have hsq12 : f (z1 ^ 2) = f (z2 ^ 2) := by
      have e1 := heq _ hm1
      have e2 := heq _ hm2
      have q1 : (z1 * s (z1 ^ 2)) ^ 2 = f (z1 ^ 2) := by
        rw [mul_pow]; exact e1
      have q2 : (z2 * s (z2 ^ 2)) ^ 2 = f (z2 ^ 2) := by
        rw [mul_pow]; exact e2
      rw [← q1, ← q2, h12]
    have hsq_eq := hinj hm1 hm2 hsq12
    have hor := sq_eq_sq_iff_eq_or_eq_neg.mp hsq_eq
    rcases hor with h | h
    · exact h
    · exfalso
      have hsq2 : z1 ^ 2 = z2 ^ 2 := by rw [h]; ring
      have hs12 : s (z1 ^ 2) = s (z2 ^ 2) := by rw [hsq2]
      have hz2 : z2 = -z1 := by linear_combination h
      have hsq3 : (-z1) ^ 2 = z1 ^ 2 := by ring
      have hcontra : z1 * s (z1 ^ 2) = -(z1 * s (z1 ^ 2)) := by
        rw [hz2] at h12
        rw [hsq3] at h12
        linear_combination h12
      have h2z : (2 : ℂ) * (z1 * s (z1 ^ 2)) = 0 := by linear_combination hcontra
      have hs1 : s (z1 ^ 2) ≠ 0 := hsne _ hm1
      have hzz : z1 = 0 := by
        rcases mul_eq_zero.mp h2z with h2 | hz
        · norm_num at h2
        · rcases mul_eq_zero.mp hz with hzz | hss
          · exact hzz
          · exact absurd hss hs1
      exact hn1 hzz

private theorem koebe_G_hasDerivAt
    (k G : ℂ → ℂ)
    (hk : DifferentiableOn ℂ k (Metric.ball (0 : ℂ) 1))
    (hG : ∀ z : ℂ, G z = z⁻¹ + z * k (z ^ 2)) :
    let u := fun z : ℂ => z * k (z ^ 2)
    let m := deriv u
    let c := k 0
    DifferentiableOn ℂ u (Metric.ball (0 : ℂ) 1) ∧
    DifferentiableOn ℂ m (Metric.ball (0 : ℂ) 1) ∧
    m 0 = c ∧
    ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 →
      HasDerivAt G (-(z ^ 2)⁻¹ + m z) z := by
  have hopen : IsOpen (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball
  have hmem0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  have hmaps : Set.MapsTo (fun z : ℂ => z ^ 2) (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have h1 : ‖z‖ < 1 := by
      have h := Metric.mem_ball.mp hz
      rwa [dist_zero_right] at h
    rw [Metric.mem_ball, dist_zero_right, norm_pow]
    have hnn : 0 ≤ ‖z‖ := norm_nonneg _
    nlinarith [sq_nonneg ‖z‖, sq_nonneg (‖z‖ - 1)]
  have hsq_diff : DifferentiableOn ℂ (fun z : ℂ => z ^ 2) (Metric.ball (0 : ℂ) 1) :=
    DifferentiableOn.pow differentiableOn_id 2
  have hcomp : DifferentiableOn ℂ (fun z : ℂ => k (z ^ 2)) (Metric.ball (0 : ℂ) 1) :=
    hk.comp hsq_diff hmaps
  have hu : DifferentiableOn ℂ (fun z : ℂ => z * k (z ^ 2)) (Metric.ball (0 : ℂ) 1) :=
    differentiableOn_id.mul hcomp
  refine ⟨hu, hu.deriv hopen, ?_, ?_⟩
  · show deriv (fun z : ℂ => z * k (z ^ 2)) 0 = k 0
    have hsq0 : HasDerivAt (fun z : ℂ => z ^ 2) ((2 : ℂ) * 0 ^ (2 - 1)) 0 :=
      hasDerivAt_pow 2 0
    have hk0 : HasDerivAt k (deriv k ((0 : ℂ) ^ 2)) ((0 : ℂ) ^ 2) := by
      have hmem : ((0 : ℂ) ^ 2) ∈ Metric.ball (0 : ℂ) 1 := by simp [hmem0]
      exact hk.hasDerivAt (hopen.mem_nhds hmem)
    have hcomp0 :
        HasDerivAt (fun z : ℂ => k (z ^ 2))
          (deriv k ((0 : ℂ) ^ 2) * ((2 : ℂ) * 0 ^ (2 - 1))) 0 :=
      (HasDerivAt.comp (0 : ℂ) (h := fun z : ℂ => z ^ 2) hk0
        hsq0).congr_of_eventuallyEq (by
        filter_upwards with x
        simp)
    have hu0 := (hasDerivAt_id (0 : ℂ)).mul hcomp0
    have hder_eq : (1 : ℂ) * k ((0 : ℂ) ^ 2) +
        id 0 * (deriv k ((0 : ℂ) ^ 2) * ((2 : ℂ) * 0 ^ (2 - 1))) = k 0 := by
      simp [id_eq]
    rw [hder_eq] at hu0
    have hfun : ((fun w : ℂ => w) * (fun z : ℂ => k (z ^ 2))) =ᶠ[nhds (0 : ℂ)]
        (fun z : ℂ => z * k (z ^ 2)) := by
      filter_upwards with x; simp [Pi.mul_apply]
    have hu0' := hu0.congr_of_eventuallyEq hfun
    exact hu0'.deriv
  · intro z hz hzne
    have hu_at : HasDerivAt (fun w : ℂ => w * k (w ^ 2)) (deriv (fun w : ℂ => w * k (w ^ 2)) z) z :=
      hu.hasDerivAt (hopen.mem_nhds hz)
    have hinv : HasDerivAt (fun y : ℂ => y⁻¹) (-(z ^ 2)⁻¹) z :=
      hasDerivAt_inv hzne
    have hadd := hinv.add hu_at
    have hfun : (fun w : ℂ => w⁻¹ + w * k (w ^ 2)) =ᶠ[nhds z]
        (((fun y : ℂ => y⁻¹) + (fun w : ℂ => w * k (w ^ 2)))) := by
      filter_upwards with x; simp [Pi.add_apply]
    have hadd' := hadd.congr_of_eventuallyEq hfun
    have hGeq : G = (fun w : ℂ => w⁻¹ + w * k (w ^ 2)) := by
      ext w; rw [hG w]
    rw [hGeq]
    exact hadd'

private theorem vol_image_eq_lintegral_norm_deriv_sq
    (S : Set ℂ) (F : ℂ → ℂ) (F' : ℂ → ℂ)
    (hS : MeasurableSet S)
    (hderiv : ∀ z ∈ S, HasDerivAt F (F' z) z)
    (hinj : Set.InjOn F S) :
    volume (F '' S) = ∫⁻ z in S, ENNReal.ofReal (‖F' z‖ ^ 2) := by
  have key : ∀ z ∈ S, HasFDerivWithinAt F
      ((ContinuousLinearMap.toSpanSingleton ℂ (F' z)).restrictScalars ℝ) S z := by
    intro z hz
    have h1 : HasFDerivAt F (ContinuousLinearMap.toSpanSingleton ℂ (F' z)) z :=
      (hderiv z hz).hasFDerivAt
    have h2 : HasFDerivAt F
        ((ContinuousLinearMap.toSpanSingleton ℂ (F' z)).restrictScalars ℝ) z :=
      HasFDerivAt.restrictScalars ℝ h1
    exact h2.hasFDerivWithinAt
  have hvol := MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image
    (E := ℂ) (s := S) (f := F)
    (f' := fun z => (ContinuousLinearMap.toSpanSingleton ℂ (F' z)).restrictScalars ℝ)
    (μ := volume) hS key hinj
  rw [← hvol]
  apply setLIntegral_congr_fun hS
  intro z hz
  have hdet : ((ContinuousLinearMap.toSpanSingleton ℂ (F' z)).restrictScalars ℝ).det
      = ‖F' z‖ ^ 2 := by
    have e1 : ((ContinuousLinearMap.toSpanSingleton ℂ (F' z)).restrictScalars ℝ).det
        = LinearMap.det
          (((ContinuousLinearMap.toSpanSingleton ℂ (F' z)).restrictScalars ℝ) : ℂ →ₗ[ℝ] ℂ) := rfl
    rw [e1, ContinuousLinearMap.coe_restrictScalars]
    have e2 : ((ContinuousLinearMap.toSpanSingleton ℂ (F' z) : ℂ →L[ℂ] ℂ) : ℂ →ₗ[ℂ] ℂ)
        = LinearMap.toSpanSingleton ℂ ℂ (F' z) := rfl
    rw [e2, LinearMap.det_restrictScalars]
    have e3 : LinearMap.det (LinearMap.toSpanSingleton ℂ ℂ (F' z)) = F' z := by
      have hsm : LinearMap.toSpanSingleton ℂ ℂ (F' z) = (F' z) • LinearMap.id := by
        ext
        simp [LinearMap.toSpanSingleton]
      rw [hsm, LinearMap.det_smul, LinearMap.det_id]
      simp [Module.finrank_self]
    rw [e3]
    rw [Algebra.norm_complex_eq]
    simp [Complex.normSq_eq_norm_sq]
  simp only
  rw [hdet, abs_of_nonneg (by positivity)]

private theorem koebe_pointwise_lower
    (m : ℂ → ℂ) (c : ℂ) (t : ℝ) (u : ℂ)
    (ht0 : 0 < t) (hU : ‖u‖ = t) :
    t⁻¹ ^ 4 + ‖c‖ ^ 2
      + 2 * (((starRingEnd ℂ) c * (m u - c)).re)
      - 2 * t⁻¹ ^ 4 * (((u ^ 2 * m u)).re)
      ≤ ‖-(((u ^ 2))⁻¹) + m u‖ ^ 2 := by
  have htne : t ≠ 0 := ne_of_gt ht0
  have ht4 : (t ^ 4 : ℝ) ≠ 0 := pow_ne_zero 4 htne
  have hu0 : u ≠ 0 := by
    intro h
    apply htne
    rw [← hU, h, norm_zero]
  have hconj : ∀ a b : ℂ,
      (a * (starRingEnd ℂ) b).re = ((starRingEnd ℂ) a * b).re := by
    intro a b
    conv_lhs => rw [← Complex.conj_re]
    simp [map_mul]
  have h3 : (starRingEnd ℂ) (u ^ 2)
      = ((t ^ 4 : ℝ) : ℂ) * ((u ^ 2)⁻¹) := by
    have h := Complex.mul_conj' (u ^ 2)
    rw [norm_pow, hU, ← Complex.ofReal_pow] at h
    have eX : ((t ^ 2) ^ 2 : ℝ) = t ^ 4 := by ring
    rw [eX] at h
    have hu2 : (u ^ 2 : ℂ) ≠ 0 := pow_ne_zero 2 hu0
    have hcc : (starRingEnd ℂ) (u ^ 2)
        = ((u ^ 2)⁻¹) * ((u ^ 2) * (starRingEnd ℂ) (u ^ 2)) := by
      rw [← mul_assoc, inv_mul_cancel₀ hu2, one_mul]
    rw [hcc, h]
    ring
  have h4 : ((u ^ 2)⁻¹) * (starRingEnd ℂ) (m u)
      = ((((t ^ 4)⁻¹ : ℝ)) : ℂ) * (starRingEnd ℂ) (u ^ 2 * m u) := by
    have h5 : ((((t ^ 4)⁻¹ : ℝ)) : ℂ) * ((t ^ 4 : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ ht4, Complex.ofReal_one]
    calc ((u ^ 2)⁻¹) * (starRingEnd ℂ) (m u)
        = 1 * (((u ^ 2)⁻¹) * (starRingEnd ℂ) (m u)) := by ring
      _ = (((((t ^ 4)⁻¹ : ℝ)) : ℂ) * ((t ^ 4 : ℝ) : ℂ)) *
          (((u ^ 2)⁻¹) * (starRingEnd ℂ) (m u)) := by rw [h5]
      _ = _ := by rw [map_mul, h3]; ring
  have h4' : (-(((u ^ 2))⁻¹)) * (starRingEnd ℂ) (m u)
      = -(((((t ^ 4)⁻¹ : ℝ)) : ℂ) * (starRingEnd ℂ) (u ^ 2 * m u)) := by
    rw [neg_mul, h4]
  have h7 : ∀ (s : ℝ) (z : ℂ), (((s : ℝ) : ℂ) * z).re = s * z.re := by
    intro s z
    simp [Complex.mul_re]
  have hcross : ((-(((u ^ 2))⁻¹)) * (starRingEnd ℂ) (m u)).re
      = -(t⁻¹ ^ 4) * (((u ^ 2 * m u)).re) := by
    have eS : ((((t ^ 4)⁻¹ : ℝ))) = t⁻¹ ^ 4 := by rw [inv_pow]
    rw [h4', Complex.neg_re, h7, Complex.conj_re, eS, neg_mul]
  have hA2 : ‖(((u ^ 2))⁻¹)‖ ^ 2 = t⁻¹ ^ 4 := by
    rw [norm_inv, norm_pow, hU]
    simp only [inv_pow]
    have eX : ((t ^ 2) ^ 2 : ℝ) = t ^ 4 := by ring
    rw [eX]
  have hAsq : Complex.normSq (-(((u ^ 2))⁻¹)) = t⁻¹ ^ 4 := by
    rw [Complex.normSq_neg, Complex.normSq_eq_norm_sq]
    exact hA2
  have hcsq : Complex.normSq c = ‖c‖ ^ 2 := Complex.normSq_eq_norm_sq c
  have hcross2 : (-(((u ^ 2))⁻¹) *
      (starRingEnd ℂ) (c + (m u - c))).re
      = -(t⁻¹ ^ 4) * (((u ^ 2 * m u)).re) := by
    have hce : c + (m u - c) = m u := add_sub_cancel c (m u)
    rw [hce]
    exact hcross
  have hconj_e : (c * (starRingEnd ℂ) (m u - c)).re
      = (((starRingEnd ℂ) c * (m u - c))).re :=
    hconj c _
  have hns : Complex.normSq (-(((u ^ 2))⁻¹) + m u)
      = t⁻¹ ^ 4 + (‖c‖ ^ 2 + 2 * ((((starRingEnd ℂ) c * (m u - c))).re) +
        (Complex.normSq (m u - c) +
          2 * (-(t⁻¹ ^ 4) * (((u ^ 2 * m u)).re)))) := by
    have e1 : (-(((u ^ 2))⁻¹) + m u)
        = (-(((u ^ 2))⁻¹)) + (c + (m u - c)) := by
      rw [add_sub_cancel]
    rw [e1, Complex.normSq_add, Complex.normSq_add, hAsq, hcsq, hcross2,
      hconj_e]
    ring
  have hle : t⁻¹ ^ 4 + ‖c‖ ^ 2
      + 2 * (((starRingEnd ℂ) c * (m u - c)).re)
      - 2 * t⁻¹ ^ 4 * (((u ^ 2 * m u)).re)
      ≤ Complex.normSq (-(((u ^ 2))⁻¹) + m u) := by
    rw [hns]
    have hnn : 0 ≤ Complex.normSq (m u - c) := Complex.normSq_nonneg _
    linarith
  rwa [Complex.normSq_eq_norm_sq] at hle

private theorem koebe_circle_integral_lower
    (m : ℂ → ℂ) (c : ℂ) (t : ℝ)
    (hm : DifferentiableOn ℂ m (Metric.ball (0 : ℂ) 1))
    (hm0 : m 0 = c)
    (ht0 : 0 < t) (ht1 : t < 1) :
    2 * Real.pi * (t⁻¹ ^ 4 + ‖c‖ ^ 2) ≤
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        ‖-(((circleMap 0 t θ) ^ 2)⁻¹) + m (circleMap 0 t θ)‖ ^ 2 := by
  have htne : t ≠ 0 := ne_of_gt ht0
  have hnorm : ∀ θ : ℝ, ‖circleMap 0 t θ‖ = t := by
    intro θ
    rw [norm_circleMap_zero, abs_of_pos ht0]
  have hmem : ∀ θ : ℝ, circleMap 0 t θ ∈ Metric.ball (0 : ℂ) 1 := by
    intro θ
    rw [Metric.mem_ball, dist_zero_right, hnorm θ]
    exact ht1
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2π : (2 * Real.pi) ≠ 0 := ne_of_gt hpos
  have hmw_cont : ContinuousOn (fun θ : ℝ => m (circleMap 0 t θ))
      (Set.uIcc 0 (2 * Real.pi)) := by
    have hmaps : Set.MapsTo (circleMap 0 t) (Set.uIcc 0 (2 * Real.pi))
        (Metric.ball (0 : ℂ) 1) :=
      fun θ _ => hmem θ
    have h := (hm.continuousOn).comp (continuous_circleMap 0 t).continuousOn
      hmaps
    exact h.congr (fun θ _ => rfl)
  have hsqc : ContinuousOn (fun θ : ℝ => (circleMap 0 t θ) ^ 2)
      (Set.uIcc 0 (2 * Real.pi)) :=
    ((continuous_circleMap 0 t).continuousOn.mul
      (continuous_circleMap 0 t).continuousOn).congr
      (fun θ _ => pow_two _)
  have hconst_c : ContinuousOn (fun _ : ℝ => c) (Set.uIcc 0 (2 * Real.pi)) :=
    continuous_const.continuousOn
  have hsubc : ContinuousOn (fun θ : ℝ => m (circleMap 0 t θ) - c)
      (Set.uIcc 0 (2 * Real.pi)) :=
    (hmw_cont.sub hconst_c).congr (fun θ _ => rfl)
  have hRe1c : ContinuousOn
      (fun θ : ℝ => ((starRingEnd ℂ) c * (m (circleMap 0 t θ) - c)).re)
      (Set.uIcc 0 (2 * Real.pi)) := by
    have h := (Complex.continuous_re.continuousOn).comp
      (hsubc.const_mul ((starRingEnd ℂ) c)) (Set.mapsTo_univ _ _)
    exact h.congr (fun θ _ => rfl)
  have hF2c : ContinuousOn
      (fun θ : ℝ => (circleMap 0 t θ) ^ 2 * m (circleMap 0 t θ))
      (Set.uIcc 0 (2 * Real.pi)) :=
    (hsqc.mul hmw_cont).congr (fun θ _ => rfl)
  have hRe2c : ContinuousOn
      (fun θ : ℝ => (((circleMap 0 t θ) ^ 2 * m (circleMap 0 t θ))).re)
      (Set.uIcc 0 (2 * Real.pi)) := by
    have h := (Complex.continuous_re.continuousOn).comp hF2c
      (Set.mapsTo_univ _ _)
    exact h.congr (fun θ _ => rfl)
  have hAc : ContinuousOn (fun θ : ℝ => -(((circleMap 0 t θ) ^ 2))⁻¹)
      (Set.uIcc 0 (2 * Real.pi)) := by
    have hne : ∀ θ ∈ Set.uIcc 0 (2 * Real.pi),
        ((circleMap 0 t θ) ^ 2) ≠ 0 := by
      intro θ _
      have h0' : circleMap 0 t θ ≠ 0 := by
        intro hcon
        apply htne
        rw [← hnorm θ, hcon, norm_zero]
      exact pow_ne_zero 2 h0'
    have h := hsqc.inv₀ hne
    have h2 := h.neg
    exact h2.congr (fun θ _ => rfl)
  have hsumc : ContinuousOn
      (fun θ : ℝ => -(((circleMap 0 t θ) ^ 2))⁻¹ + m (circleMap 0 t θ))
      (Set.uIcc 0 (2 * Real.pi)) :=
    (hAc.add hmw_cont).congr (fun θ _ => rfl)
  have hFc : ContinuousOn
      (fun θ : ℝ => ‖-(((circleMap 0 t θ) ^ 2))⁻¹ + m (circleMap 0 t θ)‖ ^ 2)
      (Set.uIcc 0 (2 * Real.pi)) := by
    have h := (hsumc.norm).mul (hsumc.norm)
    exact h.congr (fun θ _ => pow_two _)
  have hint_F : IntervalIntegrable
      (fun θ : ℝ => ‖-(((circleMap 0 t θ) ^ 2))⁻¹ + m (circleMap 0 t θ)‖ ^ 2)
      volume 0 (2 * Real.pi) := hFc.intervalIntegrable
  have hint_m : IntervalIntegrable (fun θ : ℝ => m (circleMap 0 t θ))
      volume 0 (2 * Real.pi) := hmw_cont.intervalIntegrable
  have hint_c : IntervalIntegrable (fun _ : ℝ => c) volume 0 (2 * Real.pi) :=
    hconst_c.intervalIntegrable
  have hint_Re1 : IntervalIntegrable
      (fun θ : ℝ => ((starRingEnd ℂ) c * (m (circleMap 0 t θ) - c)).re)
      volume 0 (2 * Real.pi) := hRe1c.intervalIntegrable
  have hint_Re2 : IntervalIntegrable
      (fun θ : ℝ => (((circleMap 0 t θ) ^ 2 * m (circleMap 0 t θ))).re)
      volume 0 (2 * Real.pi) := hRe2c.intervalIntegrable
  have hint_F2 : IntervalIntegrable
      (fun θ : ℝ => (circleMap 0 t θ) ^ 2 * m (circleMap 0 t θ))
      volume 0 (2 * Real.pi) := hF2c.intervalIntegrable
  have hint_sub : IntervalIntegrable
      (fun θ : ℝ => (starRingEnd ℂ) c * (m (circleMap 0 t θ) - c))
      volume 0 (2 * Real.pi) :=
    (hsubc.const_mul _).intervalIntegrable
  have hsub : closure (Metric.ball (0 : ℂ) |t|) ⊆ Metric.ball (0 : ℂ) 1 := by
    have h1 : closure (Metric.ball (0 : ℂ) |t|)
        ⊆ Metric.closedBall (0 : ℂ) |t| :=
      closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall
    have h2 : Metric.closedBall (0 : ℂ) |t| ⊆ Metric.ball (0 : ℂ) 1 := by
      intro z hz
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      rw [Metric.mem_ball, dist_zero_right]
      rw [abs_of_pos ht0] at hz
      linarith
    exact h1.trans h2
  have hdiff_m : DiffContOnCl ℂ m (Metric.ball (0 : ℂ) |t|) :=
    (hm.mono hsub).diffContOnCl
  have hF2 : DifferentiableOn ℂ (fun z => z ^ 2 * m z)
      (Metric.ball (0 : ℂ) 1) :=
    ((DifferentiableOn.pow differentiableOn_id 2).mono
      (Set.subset_univ _)).mul hm
  have hdiff_F2 : DiffContOnCl ℂ (fun z => z ^ 2 * m z)
      (Metric.ball (0 : ℂ) |t|) :=
    (hF2.mono hsub).diffContOnCl
  have hmean_m : (∫ θ in (0 : ℝ)..(2 * Real.pi), m (circleMap 0 t θ))
      = (2 * Real.pi) • c := by
    have h0 := DiffContOnCl.circleAverage hdiff_m
    rw [Real.circleAverage_def, hm0] at h0
    have h := congrArg ((2 * Real.pi) • ·) h0
    rwa [smul_inv_smul₀ h2π] at h
  have hmean_F2 : (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (circleMap 0 t θ) ^ 2 * m (circleMap 0 t θ)) = 0 := by
    have h0 := DiffContOnCl.circleAverage hdiff_F2
    rw [Real.circleAverage_def] at h0
    have hF200 : (0 : ℂ) ^ 2 * m 0 = 0 := by simp
    rw [hF200] at h0
    have h := congrArg ((2 * Real.pi) • ·) h0
    rwa [smul_inv_smul₀ h2π, smul_zero] at h
  have hRe1 : (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (((starRingEnd ℂ) c * (m (circleMap 0 t θ) - c)).re)) = 0 := by
    simp only [← Complex.reCLM_apply]
    rw [ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hint_sub,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub hint_m hint_c, hmean_m,
      intervalIntegral.integral_const]
    simp
  have hRe2 : (∫ θ in (0 : ℝ)..(2 * Real.pi),
      ((((circleMap 0 t θ) ^ 2 * m (circleMap 0 t θ))).re)) = 0 := by
    simp only [← Complex.reCLM_apply]
    rw [ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hint_F2,
      hmean_F2, map_zero]
  have hint_2Re1 : IntervalIntegrable
      (fun θ : ℝ => 2 * (((starRingEnd ℂ) c * (m (circleMap 0 t θ) - c)).re))
      volume 0 (2 * Real.pi) :=
    (hRe1c.const_mul 2).intervalIntegrable
  have hint_K : IntervalIntegrable (fun _ : ℝ => t⁻¹ ^ 4 + ‖c‖ ^ 2)
      volume 0 (2 * Real.pi) :=
    continuous_const.continuousOn.intervalIntegrable
  have hint_L1 : IntervalIntegrable
      (fun θ : ℝ => t⁻¹ ^ 4 + ‖c‖ ^ 2 +
        2 * (((starRingEnd ℂ) c * (m (circleMap 0 t θ) - c)).re))
      volume 0 (2 * Real.pi) :=
    hint_K.add hint_2Re1
  have hint_2tRe2 : IntervalIntegrable
      (fun θ : ℝ => 2 * t⁻¹ ^ 4 *
        ((((circleMap 0 t θ) ^ 2 * m (circleMap 0 t θ))).re))
      volume 0 (2 * Real.pi) :=
    (hRe2c.const_mul (2 * t⁻¹ ^ 4)).intervalIntegrable
  have hint_L : IntervalIntegrable
      (fun θ : ℝ => t⁻¹ ^ 4 + ‖c‖ ^ 2 +
        2 * (((starRingEnd ℂ) c * (m (circleMap 0 t θ) - c)).re) -
        2 * t⁻¹ ^ 4 * ((((circleMap 0 t θ) ^ 2 * m (circleMap 0 t θ))).re))
      volume 0 (2 * Real.pi) :=
    hint_L1.sub hint_2tRe2
  have hLval : (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (t⁻¹ ^ 4 + ‖c‖ ^ 2 +
        2 * (((starRingEnd ℂ) c * (m (circleMap 0 t θ) - c)).re) -
        2 * t⁻¹ ^ 4 * ((((circleMap 0 t θ) ^ 2 * m (circleMap 0 t θ))).re)))
      = 2 * Real.pi * (t⁻¹ ^ 4 + ‖c‖ ^ 2) := by
    rw [intervalIntegral.integral_sub hint_L1 hint_2tRe2,
      intervalIntegral.integral_add hint_K hint_2Re1,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      hRe1, hRe2, intervalIntegral.integral_const]
    simp [smul_eq_mul]
  have hmono := intervalIntegral.integral_mono_on (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    hint_L hint_F (fun x _ => koebe_pointwise_lower m c t (circleMap 0 t x) ht0
      (hnorm x))
  rw [hLval] at hmono
  exact hmono

private def koebeAnnulus (ρ r : ℝ) : Set ℂ := {z : ℂ | ρ < ‖z‖ ∧ ‖z‖ < r}

private theorem koebe_lintegral_annulus_polar
    (g : ℂ → ENNReal) (ρ r : ℝ)
    (hg : Measurable g)
    (hρ0 : 0 ≤ ρ) :
    ∫⁻ z in koebeAnnulus ρ r, g z =
      ∫⁻ t in Set.Ioo ρ r,
        ENNReal.ofReal t * ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
          g (circleMap 0 t θ) := by
  have hopen : IsOpen (koebeAnnulus ρ r) := by
    change IsOpen {z : ℂ | ρ < ‖z‖ ∧ ‖z‖ < r}
    exact (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hAmeas : MeasurableSet (koebeAnnulus ρ r) := hopen.measurableSet
  have hsymm_cont : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
    have e : (fun p : ℝ × ℝ => Complex.polarCoord.symm p)
        = (fun p : ℝ × ℝ => ((p.1 : ℝ) : ℂ) *
          (((Real.cos p.2 : ℝ) : ℂ) +
            ((Real.sin p.2 : ℝ) : ℂ) * Complex.I)) := by
      funext p
      exact Complex.polarCoord_symm_apply p
    rw [e]
    fun_prop
  have hAE : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal p.1 •
        (koebeAnnulus ρ r).indicator g (Complex.polarCoord.symm p))
      ((volume.prod volume).restrict
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi)) :=
    (((ENNReal.measurable_ofReal.comp measurable_fst).smul
      ((hg.indicator hAmeas).comp hsymm_cont.measurable))).aemeasurable
  have hmem_iff : ∀ t' : ℝ, ∀ θ : ℝ, 0 < t' →
      (Complex.polarCoord.symm (t', θ) ∈ koebeAnnulus ρ r ↔
        t' ∈ Set.Ioo ρ r) := by
    intro t' θ ht'
    have h1 : ‖Complex.polarCoord.symm (t', θ)‖ = t' := by
      rw [Complex.norm_polarCoord_symm]
      change |t'| = t'
      exact abs_of_pos ht'
    unfold koebeAnnulus
    rw [Set.mem_ofPred_eq, h1]
    rfl
  have hsymm_circ : ∀ t' : ℝ, ∀ θ : ℝ,
      Complex.polarCoord.symm (t', θ) = circleMap 0 t' θ := by
    intro t' θ
    rw [Complex.polarCoord_symm_apply, circleMap_zero, Complex.exp_mul_I,
      Complex.ofReal_cos, Complex.ofReal_sin]
  have hsub2 : Set.Ioo ρ r ⊆ Set.Ioi (0 : ℝ) := by
    intro t ht
    change (0 : ℝ) < t
    exact lt_of_le_of_lt hρ0 ht.1
  have hinner : ∀ t' : ℝ, t' ∈ Set.Ioi (0 : ℝ) →
      (∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal t' *
          (koebeAnnulus ρ r).indicator g (Complex.polarCoord.symm (t', θ)))
      = (Set.Ioo ρ r).indicator
        (fun t => ENNReal.ofReal t *
          ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, g (circleMap 0 t θ)) t' := by
    intro t' ht'
    have ht'pos : 0 < t' := ht'
    have hgc : Measurable (fun θ : ℝ => g (circleMap 0 t' θ)) :=
      hg.comp (continuous_circleMap 0 t').measurable
    by_cases htr : t' ∈ Set.Ioo ρ r
    · have heq : Set.EqOn
          (fun θ => ENNReal.ofReal t' *
            (koebeAnnulus ρ r).indicator g (Complex.polarCoord.symm (t', θ)))
          (fun θ => ENNReal.ofReal t' * g (circleMap 0 t' θ))
          (Set.Ioo (-Real.pi) Real.pi) := by
        intro θ _
        have hmemA : Complex.polarCoord.symm (t', θ) ∈ koebeAnnulus ρ r :=
          (hmem_iff t' θ ht'pos).mpr htr
        change ENNReal.ofReal t' *
            (koebeAnnulus ρ r).indicator g
              (Complex.polarCoord.symm (t', θ)) =
            ENNReal.ofReal t' * g (circleMap 0 t' θ)
        rw [Set.indicator_of_mem hmemA, hsymm_circ]
      rw [Set.indicator_of_mem htr,
        setLIntegral_congr_fun measurableSet_Ioo heq,
        lintegral_const_mul _ hgc]
    · have heq0 : Set.EqOn
          (fun θ => ENNReal.ofReal t' *
            (koebeAnnulus ρ r).indicator g (Complex.polarCoord.symm (t', θ)))
          (fun _ => 0) (Set.Ioo (-Real.pi) Real.pi) := by
        intro θ _
        have hmemA : Complex.polarCoord.symm (t', θ) ∉ koebeAnnulus ρ r := by
          intro hc
          exact htr ((hmem_iff t' θ ht'pos).mp hc)
        change ENNReal.ofReal t' *
            (koebeAnnulus ρ r).indicator g
              (Complex.polarCoord.symm (t', θ)) = 0
        rw [Set.indicator_of_notMem hmemA, mul_zero]
      rw [Set.indicator_of_notMem htr,
        setLIntegral_congr_fun measurableSet_Ioo heq0]
      exact lintegral_zero
  have houter : Set.EqOn
      (fun t' : ℝ => ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal t' *
          (koebeAnnulus ρ r).indicator g (Complex.polarCoord.symm (t', θ)))
      (fun t' : ℝ => (Set.Ioo ρ r).indicator
        (fun t => ENNReal.ofReal t *
          ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, g (circleMap 0 t θ)) t')
      (Set.Ioi (0 : ℝ)) :=
    fun t' ht' => hinner t' ht'
  rw [← lintegral_indicator hAmeas, ← Complex.lintegral_comp_polarCoord_symm]
  rw [polarCoord_target, Measure.volume_eq_prod]
  rw [setLIntegral_prod _ hAE]
  simp only [smul_eq_mul]
  rw [setLIntegral_congr_fun measurableSet_Ioi houter,
    ← lintegral_indicator measurableSet_Ioi,
    ← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr_ae
  filter_upwards with t
  by_cases htI : t ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem htI]
  · rw [Set.indicator_of_notMem htI]
    have htr : t ∉ Set.Ioo ρ r := fun hc => htI (hsub2 hc)
    rw [Set.indicator_of_notMem htr]

private theorem koebe_lintegral_Ioo_eq
    (F : ℝ → ℝ) (hcont : ContinuousOn F (Set.uIcc (-Real.pi) Real.pi))
    (hper : Function.Periodic F (2 * Real.pi))
    (hnn : ∀ θ : ℝ, 0 ≤ F θ) :
    (∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, ENNReal.ofReal (F θ))
      = ENNReal.ofReal (∫ θ in (0 : ℝ)..(2 * Real.pi), F θ) := by
  have hle : (-Real.pi) ≤ Real.pi := by linarith [Real.pi_pos]
  have hint : IntervalIntegrable F volume (-Real.pi) Real.pi :=
    hcont.intervalIntegrable
  have hIoo : IntegrableOn F (Set.Ioo (-Real.pi) Real.pi) volume :=
    IntegrableOn.congr_set_ae
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp hint)
      Ioo_ae_eq_Ioc
  have hnn' : 0 ≤ᵐ[volume.restrict (Set.Ioo (-Real.pi) Real.pi)] F :=
    Filter.Eventually.of_forall hnn
  have e1 : ENNReal.ofReal (∫ θ in Set.Ioo (-Real.pi) Real.pi, F θ)
      = ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, ENNReal.ofReal (F θ) :=
    ofReal_integral_eq_lintegral_ofReal hIoo hnn'
  rw [← e1]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hle]
  have h := hper.intervalIntegral_add_eq (-Real.pi) 0
  rwa [show (-Real.pi) + 2 * Real.pi = Real.pi by ring,
    show (0 : ℝ) + 2 * Real.pi = 2 * Real.pi by ring] at h

private theorem koebe_area_lower
    (G m : ℂ → ℂ) (c : ℂ) (ρ r : ℝ)
    (hρ0 : 0 < ρ) (hρr : ρ < r) (hr1 : r < 1)
    (hG' : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 →
      HasDerivAt G (-(((z ^ 2))⁻¹) + m z) z)
    (hGinj : Set.InjOn G (Metric.ball (0 : ℂ) 1 \ {0}))
    (hm : DifferentiableOn ℂ m (Metric.ball (0 : ℂ) 1))
    (hm0 : m 0 = c)
    (hmeas : Measurable
      (fun z : ℂ => ENNReal.ofReal (‖-(((z ^ 2))⁻¹) + m z‖ ^ 2))) :
    ENNReal.ofReal
        (Real.pi * (ρ⁻¹ ^ 2 - r⁻¹ ^ 2) + Real.pi * ‖c‖ ^ 2 * (r ^ 2 - ρ ^ 2))
      ≤ volume (G '' koebeAnnulus ρ r) := by
  have hρr' : ρ ≤ r := le_of_lt hρr
  have hAsub : koebeAnnulus ρ r ⊆ Metric.ball (0 : ℂ) 1 \ {0} := by
    intro z hz
    obtain ⟨h1, h2⟩ := hz
    have hball : z ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    have hne : z ∉ ({0} : Set ℂ) := by
      rw [Set.mem_singleton_iff]
      intro hcon
      rw [hcon, norm_zero] at h1
      linarith
    exact ⟨hball, hne⟩
  have hAmeas : MeasurableSet (koebeAnnulus ρ r) := by
    have hopen : IsOpen (koebeAnnulus ρ r) := by
      change IsOpen {z : ℂ | ρ < ‖z‖ ∧ ‖z‖ < r}
      exact (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)
    exact hopen.measurableSet
  have hG'A : ∀ z ∈ koebeAnnulus ρ r,
      HasDerivAt G (-(((z ^ 2))⁻¹) + m z) z := by
    intro z hz
    obtain ⟨hb, hn⟩ := hAsub hz
    have hne : z ≠ 0 := fun h => hn (Set.mem_singleton_iff.mpr h)
    exact hG' z hb hne
  have hGinjA : Set.InjOn G (koebeAnnulus ρ r) := hGinj.mono hAsub
  have hvol := vol_image_eq_lintegral_norm_deriv_sq (koebeAnnulus ρ r) G
    (fun z => -(((z ^ 2))⁻¹) + m z) hAmeas hG'A hGinjA
  have hpolar := koebe_lintegral_annulus_polar
    (fun z => ENNReal.ofReal (‖-(((z ^ 2))⁻¹) + m z‖ ^ 2)) ρ r hmeas
    (le_of_lt hρ0)
  have hinner_lb : ∀ t ∈ Set.Ioo ρ r,
      ENNReal.ofReal (2 * Real.pi * (t⁻¹ ^ 4 + ‖c‖ ^ 2))
      ≤ ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal
          (‖-((((circleMap 0 t θ) ^ 2))⁻¹) + m (circleMap 0 t θ)‖ ^ 2) := by
    intro t ht
    have ht0 : 0 < t := lt_trans hρ0 ht.1
    have ht1 : t < 1 := lt_trans ht.2 hr1
    have htne : t ≠ 0 := ne_of_gt ht0
    have hnorm_t : ∀ θ : ℝ, ‖circleMap 0 t θ‖ = t := by
      intro θ
      rw [norm_circleMap_zero, abs_of_pos ht0]
    have hmw_cont : ContinuousOn (fun θ : ℝ => m (circleMap 0 t θ))
        (Set.uIcc (-Real.pi) Real.pi) := by
      have hmaps : Set.MapsTo (circleMap 0 t) (Set.uIcc (-Real.pi) Real.pi)
          (Metric.ball (0 : ℂ) 1) := by
        intro θ _
        rw [Metric.mem_ball, dist_zero_right, hnorm_t θ]
        exact ht1
      have h := (hm.continuousOn).comp
        (continuous_circleMap 0 t).continuousOn hmaps
      exact h.congr (fun θ _ => rfl)
    have hsqc : ContinuousOn (fun θ : ℝ => (circleMap 0 t θ) ^ 2)
        (Set.uIcc (-Real.pi) Real.pi) :=
      ((continuous_circleMap 0 t).continuousOn.mul
        (continuous_circleMap 0 t).continuousOn).congr
        (fun θ _ => pow_two _)
    have hAc : ContinuousOn (fun θ : ℝ => -(((circleMap 0 t θ) ^ 2))⁻¹)
        (Set.uIcc (-Real.pi) Real.pi) := by
      have hne : ∀ θ ∈ Set.uIcc (-Real.pi) Real.pi,
          ((circleMap 0 t θ) ^ 2) ≠ 0 := by
        intro θ _
        have h0' : circleMap 0 t θ ≠ 0 := by
          intro hcon
          apply htne
          rw [← hnorm_t θ, hcon, norm_zero]
        exact pow_ne_zero 2 h0'
      have h := hsqc.inv₀ hne
      have h2 := h.neg
      exact h2.congr (fun θ _ => rfl)
    have hcont : ContinuousOn
        (fun θ => ‖-((((circleMap 0 t θ) ^ 2))⁻¹) + m (circleMap 0 t θ)‖ ^ 2)
        (Set.uIcc (-Real.pi) Real.pi) := by
      have hsumc : ContinuousOn
          (fun θ : ℝ => -(((circleMap 0 t θ) ^ 2))⁻¹ + m (circleMap 0 t θ))
          (Set.uIcc (-Real.pi) Real.pi) :=
        (hAc.add hmw_cont).congr (fun θ _ => rfl)
      have h := (hsumc.norm).mul (hsumc.norm)
      exact h.congr (fun θ _ => pow_two _)
    have hper : Function.Periodic
        (fun θ => ‖-((((circleMap 0 t θ) ^ 2))⁻¹) + m (circleMap 0 t θ)‖ ^ 2)
        (2 * Real.pi) := by
      intro θ
      simp only []
      rw [periodic_circleMap 0 t θ]
    rw [koebe_lintegral_Ioo_eq _ hcont hper (fun θ => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal
      (koebe_circle_integral_lower m c t hm hm0 ht0 ht1)
  have hmono : (∫⁻ t in Set.Ioo ρ r,
      ENNReal.ofReal t * ENNReal.ofReal (2 * Real.pi * (t⁻¹ ^ 4 + ‖c‖ ^ 2)))
      ≤ ∫⁻ t in Set.Ioo ρ r,
        ENNReal.ofReal t * ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal
            (‖-((((circleMap 0 t θ) ^ 2))⁻¹) + m (circleMap 0 t θ)‖ ^ 2) := by
    rw [← lintegral_indicator measurableSet_Ioo,
      ← lintegral_indicator measurableSet_Ioo]
    apply lintegral_mono
    intro t
    by_cases ht : t ∈ Set.Ioo ρ r
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      exact mul_le_mul_of_nonneg_left (hinner_lb t ht) (by positivity)
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
  have hradial : (∫⁻ t in Set.Ioo ρ r,
      ENNReal.ofReal t * ENNReal.ofReal (2 * Real.pi * (t⁻¹ ^ 4 + ‖c‖ ^ 2)))
      = ENNReal.ofReal
        (Real.pi * (ρ⁻¹ ^ 2 - r⁻¹ ^ 2) +
          Real.pi * ‖c‖ ^ 2 * (r ^ 2 - ρ ^ 2)) := by
    have e_rw : ∀ t ∈ Set.Ioo ρ r, ENNReal.ofReal t *
        ENNReal.ofReal (2 * Real.pi * (t⁻¹ ^ 4 + ‖c‖ ^ 2))
        = ENNReal.ofReal (t * (2 * Real.pi * (t⁻¹ ^ 4 + ‖c‖ ^ 2))) := by
      intro t ht
      rw [← ENNReal.ofReal_mul (le_of_lt (lt_trans hρ0 ht.1))]
    rw [setLIntegral_congr_fun measurableSet_Ioo e_rw]
    have hFcont : ContinuousOn
        (fun t : ℝ => t * (2 * Real.pi * (t⁻¹ ^ 4 + ‖c‖ ^ 2)))
        (Set.uIcc ρ r) := by
      have hne : ∀ t ∈ Set.uIcc ρ r, t ≠ 0 := by
        intro t ht
        rw [Set.uIcc_of_le hρr'] at ht
        rw [Set.mem_Icc] at ht
        exact ne_of_gt (lt_of_lt_of_le hρ0 ht.1)
      have hbase : ContinuousOn (fun t : ℝ => t) (Set.uIcc ρ r) :=
        continuous_id.continuousOn
      have hinv : ContinuousOn (fun t : ℝ => t⁻¹) (Set.uIcc ρ r) :=
        (hbase.inv₀ hne).congr (fun t _ => rfl)
      have hpow : ContinuousOn (fun t : ℝ => (t⁻¹) ^ 4) (Set.uIcc ρ r) :=
        (hinv.pow 4).congr (fun t _ => rfl)
      have hinner : ContinuousOn
          (fun t : ℝ => 2 * Real.pi * ((t⁻¹) ^ 4 + ‖c‖ ^ 2))
          (Set.uIcc ρ r) :=
        (hpow.add_const _).const_mul _
      exact hbase.mul hinner
    have hInt : IntervalIntegrable
        (fun t : ℝ => t * (2 * Real.pi * (t⁻¹ ^ 4 + ‖c‖ ^ 2)))
        volume ρ r := hFcont.intervalIntegrable
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo ρ r)]
        (fun t : ℝ => t * (2 * Real.pi * (t⁻¹ ^ 4 + ‖c‖ ^ 2))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have ht0' : 0 ≤ t := le_of_lt (lt_trans hρ0 ht.1)
      have h1 : (0 : ℝ) ≤ 2 * Real.pi * (t⁻¹ ^ 4 + ‖c‖ ^ 2) := by positivity
      exact mul_nonneg ht0' h1
    have hB : (∫ t in Set.Ioo ρ r, t * (2 * Real.pi * (t⁻¹ ^ 4 + ‖c‖ ^ 2)))
        = Real.pi * (ρ⁻¹ ^ 2 - r⁻¹ ^ 2) +
          Real.pi * ‖c‖ ^ 2 * (r ^ 2 - ρ ^ 2) := by
      rw [← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le hρr']
      have hΦ : ∀ t ∈ Set.uIcc ρ r,
          HasDerivAt (fun t : ℝ => -Real.pi * (t⁻¹) ^ 2 + Real.pi * ‖c‖ ^ 2 * t ^ 2)
            (t * (2 * Real.pi * (t⁻¹ ^ 4 + ‖c‖ ^ 2))) t := by
        intro t ht
        have htpos : 0 < t := by
          rw [Set.uIcc_of_le hρr'] at ht
          rw [Set.mem_Icc] at ht
          exact lt_of_lt_of_le hρ0 ht.1
        have htne : t ≠ 0 := ne_of_gt htpos
        have hinv : HasDerivAt (fun x : ℝ => x⁻¹) (-1 / t ^ 2) t :=
          (hasDerivAt_id t).inv (by simpa using htne)
        have hsq : HasDerivAt (fun x : ℝ => (x⁻¹) ^ 2)
            (2 * t⁻¹ * (-1 / t ^ 2)) t := by
          have h := hinv.mul hinv
          have hv : (-1 / t ^ 2) * (fun x : ℝ => x⁻¹) t +
              (fun x : ℝ => x⁻¹) t * (-1 / t ^ 2)
              = 2 * t⁻¹ * (-1 / t ^ 2) := by
            simp only []
            ring
          rw [hv] at h
          exact h.congr_of_eventuallyEq (by
            filter_upwards with y
            exact (pow_two _))
        have h1 : HasDerivAt (fun x : ℝ => -Real.pi * (x⁻¹) ^ 2)
            (-Real.pi * (2 * t⁻¹ * (-1 / t ^ 2))) t :=
          hsq.const_mul (-Real.pi)
        have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
          simpa using hasDerivAt_pow 2 t
        have h3 : HasDerivAt (fun x : ℝ => Real.pi * ‖c‖ ^ 2 * x ^ 2)
            (Real.pi * ‖c‖ ^ 2 * (2 * t)) t :=
          h2.const_mul (Real.pi * ‖c‖ ^ 2)
        have hΦraw : HasDerivAt
            (fun t : ℝ => -Real.pi * (t⁻¹) ^ 2 + Real.pi * ‖c‖ ^ 2 * t ^ 2)
            (-Real.pi * (2 * t⁻¹ * (-1 / t ^ 2)) +
              Real.pi * ‖c‖ ^ 2 * (2 * t)) t :=
          h1.add h3
        have hval : -Real.pi * (2 * t⁻¹ * (-1 / t ^ 2)) +
            Real.pi * ‖c‖ ^ 2 * (2 * t)
            = t * (2 * Real.pi * (t⁻¹ ^ 4 + ‖c‖ ^ 2)) := by
          field_simp
        rw [hval] at hΦraw
        exact hΦraw
      have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hΦ hInt
      rw [heq]
      have hrne : r ≠ 0 := ne_of_gt (lt_trans hρ0 hρr)
      have hρne : ρ ≠ 0 := ne_of_gt hρ0
      field_simp
      ring
    have hIntR : Integrable
        (fun t : ℝ => t * (2 * Real.pi * (t⁻¹ ^ 4 + ‖c‖ ^ 2)))
        (volume.restrict (Set.Ioo ρ r)) :=
      IntegrableOn.congr_set_ae
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hρr').mp hInt)
        Ioo_ae_eq_Ioc
    rw [← ofReal_integral_eq_lintegral_ofReal hIntR hnn, hB]
  rw [hvol, hpolar, ← hradial]
  exact hmono

/-- Reduction of the Koebe quarter theorem to Bieberbach's second-coefficient bound. -/
private theorem koebe_of_bieberbach
    (hB : ∀ g : ℂ → ℂ, DifferentiableOn ℂ g (Metric.ball (0 : ℂ) 1) →
      Set.InjOn g (Metric.ball (0 : ℂ) 1) → g 0 = 0 → deriv g 0 = 1 →
      ‖iteratedDeriv 2 g 0‖ ≤ 4)
    (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (hinj : Set.InjOn f (Metric.ball (0 : ℂ) 1))
    (h0 : f 0 = 0)
    (hderiv : deriv f 0 = 1) :
    Metric.ball (0 : ℂ) (1 / 4 : ℝ) ⊆ f '' Metric.ball (0 : ℂ) 1 := by
  have hopen : IsOpen (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball
  have hmem0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  have hnhds : Metric.ball (0 : ℂ) 1 ∈ nhds (0 : ℂ) :=
    Metric.ball_mem_nhds 0 (by norm_num)
  intro w hw
  have hwball : ‖w‖ < 1 / 4 := by
    have h := Metric.mem_ball.mp hw
    rwa [dist_zero_right] at h
  by_contra hcon
  have hne : ∀ z ∈ Metric.ball (0 : ℂ) 1, f z ≠ w := by
    intro z hz hzw
    exact hcon ⟨z, hz, hzw⟩
  have hw0 : w ≠ 0 := by
    intro hww
    apply hcon
    refine ⟨0, hmem0, ?_⟩
    rw [h0]
    exact hww.symm
  have hfat : ∀ z ∈ Metric.ball (0 : ℂ) 1, HasDerivAt f (deriv f z) z :=
    fun z hz => hf.hasDerivAt (hopen.mem_nhds hz)
  have h1 : HasDerivAt f 1 0 := by
    have h := hfat 0 hmem0
    rwa [hderiv] at h
  have hu0 : HasDerivAt (fun y => w * f y) w 0 := by
    have h := h1.const_mul w
    rwa [mul_one] at h
  have hv0 : HasDerivAt (fun y => w - f y) (-1) 0 := by
    have h := (hasDerivAt_const (0 : ℂ) w).sub h1
    rw [show (0 : ℂ) - 1 = -1 from zero_sub 1] at h
    exact h.congr_of_eventuallyEq (by filter_upwards with y; rfl)
  have hv00 : (fun y => w - f y) 0 ≠ 0 := by
    have he : (fun y => w - f y) (0 : ℂ) = w := by simp [h0]
    rw [he]
    exact hw0
  have hdiv := hu0.div hv0 hv00
  have hgderiv : deriv (fun z => w * f z / (w - f z)) 0 = 1 := by
    have hlam : HasDerivAt (fun z => w * f z / (w - f z))
        ((w * ((fun y => w - f y) 0) - (fun z => w * f z) 0 * -1) /
          ((fun y => w - f y) 0) ^ 2) 0 :=
      hdiv.congr_of_eventuallyEq (by filter_upwards with y; rfl)
    have e := hlam.deriv
    rw [show ((fun y => w - f y) (0 : ℂ)) = w from by simp [h0],
      show ((fun z => w * f z) (0 : ℂ)) = 0 from by simp [h0]] at e
    rw [zero_mul, sub_zero, pow_two, div_self (mul_ne_zero hw0 hw0)] at e
    exact e
  have hu_at : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      HasDerivAt (fun y => w * f y) (w * deriv f z) z :=
    fun z hz => HasDerivAt.const_mul w (hfat z hz)
  have hv_at : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      HasDerivAt (fun y => w - f y) (-deriv f z) z := by
    intro z hz
    have h := (hasDerivAt_const z w).sub (hfat z hz)
    rw [show (0 : ℂ) - deriv f z = -deriv f z from zero_sub _] at h
    exact h.congr_of_eventuallyEq (by filter_upwards with y; rfl)
  have hvv : ∀ z ∈ Metric.ball (0 : ℂ) 1, (fun y => w - f y) z ≠ 0 := by
    intro z hz
    have he : (fun y => w - f y) z = w - f z := rfl
    rw [he]
    exact sub_ne_zero.mpr (fun h => hne z hz h.symm)
  have hg_at : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      HasDerivAt (fun z => w * f z / (w - f z))
        ((w * deriv f z * ((fun y => w - f y) z) -
          (fun z => w * f z) z * (-deriv f z)) /
          ((fun y => w - f y) z) ^ 2) z := by
    intro z hz
    exact ((hu_at z hz).div (hv_at z hz)
      (hvv z hz)).congr_of_eventuallyEq (by filter_upwards with y; rfl)
  have hderiv_eq : deriv (fun z => w * f z / (w - f z)) =ᶠ[nhds (0 : ℂ)]
      (fun z => (w * deriv f z * (w - f z) - w * f z * (-deriv f z)) /
        ((w - f z) * (w - f z))) := by
    filter_upwards [hnhds] with z hz
    have e := (hg_at z hz).deriv
    rw [pow_two] at e
    exact e
  have hdf : DifferentiableOn ℂ (deriv f) (Metric.ball (0 : ℂ) 1) :=
    hf.deriv hopen
  have hdd : HasDerivAt (deriv f) (deriv (deriv f) 0) 0 :=
    hdf.hasDerivAt (hopen.mem_nhds hmem0)
  have i2f_eq : iteratedDeriv 2 f 0 = deriv (deriv f) 0 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hA : HasDerivAt (fun z => w * deriv f z) (w * deriv (deriv f) 0) 0 :=
    HasDerivAt.const_mul w hdd
  have hE : HasDerivAt (fun z => -deriv f z) (-deriv (deriv f) 0) 0 := by
    have h := hdd.neg
    exact h.congr_of_eventuallyEq (by filter_upwards with y; rfl)
  have hC : HasDerivAt (fun z => w * f z) (w * 1) 0 := h1.const_mul w
  have hN : HasDerivAt
      (fun z => w * deriv f z * (w - f z) - w * f z * (-deriv f z))
      (((w * deriv (deriv f) 0) * (fun y => w - f y) 0 +
        (fun z => w * deriv f z) 0 * -1) -
        ((w * 1) * (fun z => -deriv f z) 0 +
          (fun z => w * f z) 0 * (-deriv (deriv f) 0))) 0 := by
    have hAV := hA.mul hv0
    have hCE := hC.mul hE
    have h := hAV.sub hCE
    exact h.congr_of_eventuallyEq (by filter_upwards with y; rfl)
  have hDraw : HasDerivAt (fun z => (w - f z) * (w - f z))
      ((-1) * (fun y => w - f y) 0 + (fun y => w - f y) 0 * (-1)) 0 := by
    have h := hv0.mul hv0
    exact h.congr_of_eventuallyEq (by filter_upwards with y; rfl)
  have hD0 : (fun z => (w - f z) * (w - f z)) 0 ≠ 0 := by
    have he : (fun z => (w - f z) * (w - f z)) (0 : ℂ) = w * w := by
      simp [h0]
    rw [he]
    exact mul_ne_zero hw0 hw0
  have hi2 : iteratedDeriv 2 (fun z => w * f z / (w - f z)) 0 =
      iteratedDeriv 2 f 0 + 2 / w := by
    have e1 : iteratedDeriv 2 (fun z => w * f z / (w - f z)) 0 =
        deriv (deriv (fun z => w * f z / (w - f z))) 0 := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    have e2 : deriv (deriv (fun z => w * f z / (w - f z))) 0 =
        deriv (fun z => (w * deriv f z * (w - f z) - w * f z * (-deriv f z)) /
          ((w - f z) * (w - f z))) 0 :=
      Filter.EventuallyEq.deriv_eq hderiv_eq
    have hQ := hN.div hDraw hD0
    have e4 : deriv (fun z => (w * deriv f z * (w - f z) -
        w * f z * (-deriv f z)) / ((w - f z) * (w - f z))) 0 =
        deriv ((fun z => w * deriv f z * (w - f z) - w * f z * (-deriv f z)) /
          (fun z => (w - f z) * (w - f z))) 0 := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards with y
      rfl
    have e5 := hQ.deriv
    rw [← e4] at e5
    simp only [] at e5
    rw [h0, hderiv, ← i2f_eq] at e5
    rw [e1, e2, e5]
    field_simp
    ring
  have hg_diffble : DifferentiableOn ℂ (fun z => w * f z / (w - f z))
      (Metric.ball (0 : ℂ) 1) :=
    ((differentiableOn_const w).mul hf).div
      ((differentiableOn_const w).sub hf)
      (fun z hz => sub_ne_zero.mpr (fun h => hne z hz h.symm))
  have ginj : Set.InjOn (fun z => w * f z / (w - f z))
      (Metric.ball (0 : ℂ) 1) := by
    intro z1 hz1 z2 hz2 heq
    have ha : w - f z1 ≠ 0 :=
      sub_ne_zero.mpr (fun h => hne z1 hz1 h.symm)
    have hb : w - f z2 ≠ 0 :=
      sub_ne_zero.mpr (fun h => hne z2 hz2 h.symm)
    simp only [] at heq
    rw [div_eq_div_iff ha hb] at heq
    have hw2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw0
    have hab : f z1 = f z2 := by
      have h2 : w ^ 2 * (f z1 - f z2) = 0 := by linear_combination heq
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h hw2
      · exact sub_eq_zero.mp h
    exact hinj hz1 hz2 hab
  have hg0 : (fun z => w * f z / (w - f z)) 0 = 0 := by simp [h0]
  have hBf : ‖iteratedDeriv 2 f 0‖ ≤ 4 := hB f hf hinj h0 hderiv
  have hgB : ‖iteratedDeriv 2 (fun z => w * f z / (w - f z)) 0‖ ≤ 4 :=
    hB _ hg_diffble ginj hg0 hgderiv
  have h2w : ‖(2 : ℂ) / w‖ ≤ 8 := by
    have e : (2 : ℂ) / w =
        iteratedDeriv 2 (fun z => w * f z / (w - f z)) 0 -
          iteratedDeriv 2 f 0 := by
      rw [hi2]
      ring
    rw [e]
    calc ‖iteratedDeriv 2 (fun z => w * f z / (w - f z)) 0 -
          iteratedDeriv 2 f 0‖
        ≤ ‖iteratedDeriv 2 (fun z => w * f z / (w - f z)) 0‖ +
          ‖iteratedDeriv 2 f 0‖ := norm_sub_le _ _
      _ ≤ 4 + 4 := by gcongr
      _ = 8 := by norm_num
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have h2wn : ‖(2 : ℂ) / w‖ = 2 / ‖w‖ := by
    rw [norm_div]
    norm_num
  rw [h2wn] at h2w
  have hge : 1 / 4 ≤ ‖w‖ := by
    rw [div_le_iff₀ hwpos] at h2w
    linarith
  linarith

private theorem koebe_H_holo
    (s : ℂ → ℂ)
    (hs : DifferentiableOn ℂ s (Metric.ball (0 : ℂ) 1)) :
    DifferentiableOn ℂ (fun z : ℂ => z * s (z ^ 2)) (Metric.ball (0 : ℂ) 1) := by
  have hsq : DifferentiableOn ℂ (fun z : ℂ => z ^ 2) (Metric.ball (0 : ℂ) 1) :=
    DifferentiableOn.pow differentiableOn_id 2
  have hmaps : Set.MapsTo (fun z : ℂ => z ^ 2) (Metric.ball (0 : ℂ) 1)
      (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have h1 : ‖z‖ < 1 := by
      have h := Metric.mem_ball.mp hz
      rwa [dist_zero_right] at h
    rw [Metric.mem_ball, dist_zero_right, norm_pow]
    have hnn : 0 ≤ ‖z‖ := norm_nonneg _
    nlinarith [sq_nonneg ‖z‖, sq_nonneg (‖z‖ - 1)]
  exact differentiableOn_id.mul (hs.comp hsq hmaps)

private theorem koebe_H_zero_iff
    (s : ℂ → ℂ)
    (hsne : ∀ w ∈ Metric.ball (0 : ℂ) 1, s w ≠ 0)
    (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    (z * s (z ^ 2) = 0) ↔ z = 0 := by
  have hsq_mem : z ^ 2 ∈ Metric.ball (0 : ℂ) 1 := by
    have h1 : ‖z‖ < 1 := by
      have h := Metric.mem_ball.mp hz
      rwa [dist_zero_right] at h
    rw [Metric.mem_ball, dist_zero_right, norm_pow]
    have hnn : 0 ≤ ‖z‖ := norm_nonneg _
    nlinarith [sq_nonneg ‖z‖, sq_nonneg (‖z‖ - 1)]
  constructor
  · intro hcon
    rcases mul_eq_zero.mp hcon with h | h
    · exact h
    · exact absurd h (hsne _ hsq_mem)
  · intro h
    rw [h, zero_mul]

/-- The real-linear ellipse map `ζ ↦ ρ⁻¹ * (starRingEnd ℂ ζ) + c * ρ * ζ`. -/
private noncomputable def koebeEll (ρ : ℝ) (c : ℂ) : ℂ →ₗ[ℝ] ℂ :=
  (LinearMap.mulLeft ℝ ((ρ⁻¹ : ℝ) : ℂ)).comp
    Complex.conjAe.toLinearEquiv.toLinearMap +
    LinearMap.mulLeft ℝ (c * (ρ : ℂ))

private theorem koebeEll_apply (ρ : ℝ) (c ζ : ℂ) :
    koebeEll ρ c ζ = ((ρ⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ ζ) + c * (ρ : ℂ) * ζ := by
  have hconj : Complex.conjAe.toLinearEquiv.toLinearMap ζ = (starRingEnd ℂ ζ) := rfl
  simp only [koebeEll, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, hconj, mul_assoc]

private theorem koebeEll_norm_bounds (ρ : ℝ) (c ζ : ℂ) (hρ : 0 < ρ) :
    (ρ⁻¹ - ‖c‖ * ρ) * ‖ζ‖ ≤ ‖koebeEll ρ c ζ‖ ∧
      ‖koebeEll ρ c ζ‖ ≤ (ρ⁻¹ + ‖c‖ * ρ) * ‖ζ‖ := by
  rw [koebeEll_apply]
  have hA : ‖((ρ⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ ζ)‖ = ρ⁻¹ * ‖ζ‖ := by
    rw [norm_mul, Complex.norm_real, Complex.norm_conj, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hρ)]
  have hB : ‖c * (ρ : ℂ) * ζ‖ = ‖c‖ * ρ * ‖ζ‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hρ.le]
  constructor
  · have h := norm_sub_norm_le (((ρ⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ ζ))
      (-(c * (ρ : ℂ) * ζ))
    rw [norm_neg, sub_neg_eq_add] at h
    rw [hA, hB] at h
    have heq : (ρ⁻¹ - ‖c‖ * ρ) * ‖ζ‖ = ρ⁻¹ * ‖ζ‖ - ‖c‖ * ρ * ‖ζ‖ := by
      ring
    rw [heq]
    exact h
  · have h := norm_add_le (((ρ⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ ζ)) (c * (ρ : ℂ) * ζ)
    rw [hA, hB] at h
    have heq : (ρ⁻¹ + ‖c‖ * ρ) * ‖ζ‖ = ρ⁻¹ * ‖ζ‖ + ‖c‖ * ρ * ‖ζ‖ := by
      ring
    rw [heq]
    exact h

private theorem koebeEll_gap_pos (ρ : ℝ) (c : ℂ) (hρ : 0 < ρ)
    (h : ‖c‖ * ρ ^ 2 < 1) : 0 < ρ⁻¹ - ‖c‖ * ρ := by
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  have h1 : ‖c‖ * ρ < ρ⁻¹ := by
    have h3 : ‖c‖ * ρ = (‖c‖ * ρ ^ 2) * ρ⁻¹ := by
      field_simp
    rw [h3]
    have h4 : (‖c‖ * ρ ^ 2) * ρ⁻¹ < 1 * ρ⁻¹ :=
      mul_lt_mul_of_pos_right h (inv_pos.mpr hρ)
    rwa [one_mul] at h4
  linarith

private theorem koebeEll_injective (ρ : ℝ) (c : ℂ) (hρ : 0 < ρ)
    (h : ‖c‖ * ρ ^ 2 < 1) : Function.Injective (koebeEll ρ c) := by
  intro ζ₁ ζ₂ h12
  have hpos := koebeEll_gap_pos ρ c hρ h
  have hL : koebeEll ρ c (ζ₁ - ζ₂) = 0 := by
    rw [map_sub, h12, sub_self]
  have hnorm := (koebeEll_norm_bounds ρ c (ζ₁ - ζ₂) hρ).1
  rw [hL, norm_zero] at hnorm
  have h0 : ‖ζ₁ - ζ₂‖ = 0 := by
    rcases eq_or_lt_of_le (norm_nonneg (ζ₁ - ζ₂)) with hcon | hcon
    · exact hcon.symm
    · have hmul := mul_pos hpos hcon
      linarith
  have hsub : ζ₁ - ζ₂ = 0 := norm_eq_zero.mp h0
  exact sub_eq_zero.mp hsub

private theorem koebeEll_preimage (ρ : ℝ) (c : ℂ) (hρ : 0 < ρ)
    (h : ‖c‖ * ρ ^ 2 < 1) (t : ℝ) (e : ℂ)
    (he : ‖e‖ ≤ t * (ρ⁻¹ - ‖c‖ * ρ)) :
    ∃ η : ℂ, ‖η‖ ≤ t ∧ koebeEll ρ c η = e := by
  have hpos := koebeEll_gap_pos ρ c hρ h
  obtain ⟨η, hη⟩ := LinearMap.injective_iff_surjective.mp
    (koebeEll_injective ρ c hρ h) e
  refine ⟨η, ?_, hη⟩
  have h1 : (ρ⁻¹ - ‖c‖ * ρ) * ‖η‖ ≤ ‖e‖ := by
    rw [← hη]
    exact (koebeEll_norm_bounds ρ c η hρ).1
  have h2 : t * (ρ⁻¹ - ‖c‖ * ρ) = (ρ⁻¹ - ‖c‖ * ρ) * t := by ring
  rw [h2] at he
  have hle : (ρ⁻¹ - ‖c‖ * ρ) * ‖η‖ ≤ (ρ⁻¹ - ‖c‖ * ρ) * t :=
    le_trans h1 he
  exact le_of_mul_le_mul_left hle hpos

private theorem koebeEll_toMatrix (ρ : ℝ) (c : ℂ) :
    LinearMap.toMatrix Complex.basisOneI Complex.basisOneI (koebeEll ρ c) =
      !![ρ⁻¹ + c.re * ρ, -(c.im * ρ); c.im * ρ, c.re * ρ - ρ⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr,
      Complex.coe_basisOneI, koebeEll_apply, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

private theorem koebeEll_det (ρ : ℝ) (c : ℂ) :
    LinearMap.det (koebeEll ρ c) = ‖c‖ ^ 2 * ρ ^ 2 - ρ⁻¹ ^ 2 := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, koebeEll_toMatrix,
    Matrix.det_fin_two_of]
  have hsq : ‖c‖ ^ 2 = c.re * c.re + c.im * c.im := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  rw [hsq]
  ring

private theorem koebeEll_det_abs (ρ : ℝ) (c : ℂ) (hρ : 0 < ρ)
    (h : ‖c‖ * ρ ^ 2 < 1) :
    |LinearMap.det (koebeEll ρ c)| = ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2 := by
  have hnn0 : 0 ≤ ‖c‖ * ρ ^ 2 := by positivity
  have hsq1 : (‖c‖ * ρ ^ 2) ^ 2 < 1 := by
    have hlt := pow_lt_pow_left₀ h hnn0 two_ne_zero
    rwa [one_pow] at hlt
  have hnn : ‖c‖ ^ 2 * ρ ^ 2 ≤ ρ⁻¹ ^ 2 := by
    have hρne : ρ ≠ 0 := ne_of_gt hρ
    have h2 : ‖c‖ ^ 2 * ρ ^ 2 * ρ ^ 2 < 1 := by
      have heq : ‖c‖ ^ 2 * ρ ^ 2 * ρ ^ 2 = (‖c‖ * ρ ^ 2) ^ 2 := by ring
      rw [heq]
      exact hsq1
    have h3 : ‖c‖ ^ 2 * ρ ^ 2 = (‖c‖ ^ 2 * ρ ^ 2 * ρ ^ 2) * ρ⁻¹ ^ 2 := by
      field_simp
    rw [h3]
    have hpos : (0 : ℝ) < ρ⁻¹ ^ 2 := pow_pos (inv_pos.mpr hρ) 2
    have h4 : (‖c‖ ^ 2 * ρ ^ 2 * ρ ^ 2) * ρ⁻¹ ^ 2 < 1 * ρ⁻¹ ^ 2 :=
      mul_lt_mul_of_pos_right h2 hpos
    rw [one_mul] at h4
    exact le_of_lt h4
  rw [koebeEll_det, abs_of_nonpos (by linarith)]
  ring

private theorem koebeEll_volume (ρ : ℝ) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hρ : 0 < ρ) (h : ‖c‖ * ρ ^ 2 < 1) :
    volume (koebeEll ρ c '' Metric.closedBall 0 R) =
      ENNReal.ofReal (Real.pi * R ^ 2 * (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2)) := by
  have hdet := koebeEll_det_abs ρ c hρ h
  have hD : 0 ≤ ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2 := by
    rw [← hdet]
    exact abs_nonneg _
  have hpi : (NNReal.pi : ENNReal) = ENNReal.ofReal Real.pi := by
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  have hreal : Real.pi * R ^ 2 * (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2)
      = (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2) * (R ^ 2 * Real.pi) := by ring
  have hR2 : ENNReal.ofReal R ^ 2 = ENNReal.ofReal (R ^ 2) := by
    rw [ENNReal.ofReal_pow hR]
  rw [MeasureTheory.Measure.addHaar_image_linearMap volume _ _,
    Complex.volume_closedBall, hdet, hpi, hR2, hreal,
    ENNReal.ofReal_mul hD, ENNReal.ofReal_mul (sq_nonneg R)]

private theorem koebe_dslope_bound (k : ℂ → ℂ)
    (hk : DifferentiableOn ℂ k (Metric.ball 0 1)) :
    ∃ M : ℝ, 1 ≤ M ∧
      ∀ w ∈ Metric.closedBall (0 : ℂ) (1 / 4), ‖dslope k 0 w‖ ≤ M := by
  have hnhds : Metric.ball (0 : ℂ) 1 ∈ nhds (0 : ℂ) :=
    Metric.ball_mem_nhds 0 (by norm_num)
  have hk1 : DifferentiableOn ℂ (dslope k 0) (Metric.ball (0 : ℂ) 1) :=
    (Complex.differentiableOn_dslope hnhds).mpr hk
  have hsub : Metric.closedBall (0 : ℂ) (1 / 4 : ℝ) ⊆ Metric.ball (0 : ℂ) 1 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hcont : ContinuousOn (dslope k 0) (Metric.closedBall (0 : ℂ) (1 / 4)) :=
    (hk1.mono hsub).continuousOn
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_closedBall _ _) hcont
  exact ⟨max C 1, le_max_right _ _,
    fun w hw => le_trans (hC w hw) (le_max_left _ _)⟩

private theorem koebe_G_circle_mem (k G : ℂ → ℂ) (c : ℂ) (ρ M : ℝ) (ζ : ℂ)
    (hG : ∀ z : ℂ, G z = z⁻¹ + z * k (z ^ 2))
    (hc : c = k 0)
    (hM : 1 ≤ M)
    (hk1 : ∀ w ∈ Metric.closedBall (0 : ℂ) (1 / 4), ‖dslope k 0 w‖ ≤ M)
    (hρ0 : 0 < ρ) (hρ2 : ρ ≤ 1 / 2)
    (hρc : ‖c‖ * ρ ^ 2 ≤ 1 / 2)
    (hζ : ‖ζ‖ = 1) :
    G ((ρ : ℂ) * ζ) ∈
      koebeEll ρ c '' Metric.closedBall 0 (1 + 4 * M * ρ ^ 4) := by
  have hρne : ρ ≠ 0 := ne_of_gt hρ0
  have hζne : ζ ≠ 0 := by
    intro hcon
    rw [hcon, norm_zero] at hζ
    norm_num at hζ
  have hmul : ζ * starRingEnd ℂ ζ = 1 := by
    have hmc := Complex.mul_conj' ζ
    rw [hζ] at hmc
    simpa using hmc
  have hconj : ζ⁻¹ = starRingEnd ℂ ζ := by
    calc ζ⁻¹ = ζ⁻¹ * 1 := by rw [mul_one]
      _ = ζ⁻¹ * (ζ * starRingEnd ℂ ζ) := by rw [hmul]
      _ = starRingEnd ℂ ζ := by
        rw [← mul_assoc, inv_mul_cancel₀ hζne, one_mul]
  have hinv : (((ρ : ℝ) : ℂ) * ζ)⁻¹
      = ((ρ⁻¹ : ℝ) : ℂ) * starRingEnd ℂ ζ := by
    rw [mul_inv, hconj, ← Complex.ofReal_inv]
  have hkk : k ((((ρ : ℝ) : ℂ) * ζ) ^ 2)
      = c + (((ρ : ℝ) : ℂ) * ζ) ^ 2 * dslope k 0 ((((ρ : ℝ) : ℂ) * ζ) ^ 2) := by
    have hds := sub_smul_dslope k 0 ((((ρ : ℝ) : ℂ) * ζ) ^ 2)
    rw [smul_eq_mul, sub_zero, ← hc] at hds
    linear_combination -hds
  have hGexp : G (((ρ : ℝ) : ℂ) * ζ)
      = koebeEll ρ c ζ
        + (((ρ : ℝ) : ℂ) * ζ) ^ 3 * dslope k 0 ((((ρ : ℝ) : ℂ) * ζ) ^ 2) := by
    rw [hG, hinv, hkk, koebeEll_apply]
    ring
  have hn2 : ‖(((ρ : ℝ) : ℂ) * ζ) ^ 2‖ = ρ ^ 2 := by
    rw [norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hρ0.le, hζ]
    ring
  have hmem : (((ρ : ℝ) : ℂ) * ζ) ^ 2 ∈ Metric.closedBall (0 : ℂ) (1 / 4) := by
    rw [Metric.mem_closedBall, dist_zero_right, hn2]
    have hle := pow_le_pow_left₀ hρ0.le hρ2 2
    norm_num at hle ⊢
    exact hle
  have hn3 : ‖(((ρ : ℝ) : ℂ) * ζ) ^ 3‖ = ρ ^ 3 := by
    rw [norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hρ0.le, hζ]
    ring
  have herr : ‖(((ρ : ℝ) : ℂ) * ζ) ^ 3 * dslope k 0 ((((ρ : ℝ) : ℂ) * ζ) ^ 2)‖
      ≤ M * ρ ^ 3 := by
    rw [norm_mul, hn3, mul_comm M (ρ ^ 3)]
    exact mul_le_mul_of_nonneg_left (hk1 _ hmem) (pow_nonneg hρ0.le 3)
  have hlt : ‖c‖ * ρ ^ 2 < 1 := lt_of_le_of_lt hρc (by norm_num)
  have hpos := koebeEll_gap_pos ρ c hρ0 hlt
  have hd : ρ * (ρ⁻¹ - ‖c‖ * ρ) = 1 - ‖c‖ * ρ ^ 2 := by
    rw [mul_sub, mul_inv_cancel₀ hρne]
    ring
  have key : M * ρ ^ 3 / (ρ⁻¹ - ‖c‖ * ρ) ≤ 4 * M * ρ ^ 4 := by
    rw [div_le_iff₀ hpos]
    have hM0 : (0 : ℝ) ≤ M := le_trans (by norm_num) hM
    have hnn3 : (0 : ℝ) ≤ M * ρ ^ 3 :=
      mul_nonneg hM0 (pow_nonneg hρ0.le 3)
    have h4 : (1 : ℝ) ≤ 4 * (ρ * (ρ⁻¹ - ‖c‖ * ρ)) := by
      rw [hd]
      linarith
    have h5 : M * ρ ^ 3 * 1 ≤ M * ρ ^ 3 * (4 * (ρ * (ρ⁻¹ - ‖c‖ * ρ))) :=
      mul_le_mul_of_nonneg_left h4 hnn3
    have h6 : M * ρ ^ 3 * (4 * (ρ * (ρ⁻¹ - ‖c‖ * ρ)))
        = (4 * M * ρ ^ 4) * (ρ⁻¹ - ‖c‖ * ρ) := by ring
    rw [mul_one] at h5
    rw [h6] at h5
    exact h5
  obtain ⟨η, hηn, hηe⟩ := koebeEll_preimage ρ c hρ0 hlt
    (M * ρ ^ 3 / (ρ⁻¹ - ‖c‖ * ρ))
    ((((ρ : ℝ) : ℂ) * ζ) ^ 3 * dslope k 0 ((((ρ : ℝ) : ℂ) * ζ) ^ 2)) (by
    have hdne : ρ⁻¹ - ‖c‖ * ρ ≠ 0 := ne_of_gt hpos
    have heq : M * ρ ^ 3 / (ρ⁻¹ - ‖c‖ * ρ) * (ρ⁻¹ - ‖c‖ * ρ) = M * ρ ^ 3 :=
      div_mul_cancel₀ _ hdne
    rw [heq]
    exact herr)
  refine ⟨ζ + η, ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    have htri := norm_add_le ζ η
    linarith [htri, hζ, hηn, key]
  · rw [map_add, hηe, hGexp]

private theorem koebe_compl_subset_image (k G : ℂ → ℂ) (c : ℂ) (ρ M : ℝ)
    (hk : DifferentiableOn ℂ k (Metric.ball 0 1))
    (hG : ∀ z : ℂ, G z = z⁻¹ + z * k (z ^ 2))
    (hGinj : Set.InjOn G (Metric.ball (0 : ℂ) 1 \ {0}))
    (hGdiff : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → DifferentiableAt ℂ G z)
    (hc : c = k 0)
    (hM : 1 ≤ M)
    (hk1 : ∀ w ∈ Metric.closedBall (0 : ℂ) (1 / 4), ‖dslope k 0 w‖ ≤ M)
    (hρ0 : 0 < ρ) (hρ2 : ρ ≤ 1 / 2)
    (hρc : ‖c‖ * ρ ^ 2 ≤ 1 / 2) :
    (koebeEll ρ c '' Metric.closedBall 0 (1 + 4 * M * ρ ^ 4))ᶜ ⊆
      G '' (Metric.ball 0 ρ \ {0}) := by
  have hM0 : (0 : ℝ) ≤ M := le_trans (by norm_num) hM
  have hlt : ‖c‖ * ρ ^ 2 < 1 := lt_of_le_of_lt hρc (by norm_num)
  have hpos := koebeEll_gap_pos ρ c hρ0 hlt
  have hbij : Function.Bijective (koebeEll ρ c) :=
    ⟨koebeEll_injective ρ c hρ0 hlt,
      LinearMap.injective_iff_surjective.mp
        (koebeEll_injective ρ c hρ0 hlt)⟩
  set K := (ρ⁻¹ + ‖c‖ * ρ) * (1 + 4 * M * ρ ^ 4) with hKdef
  have hK0 : (0 : ℝ) ≤ K := by
    rw [hKdef]
    apply mul_nonneg
    · have h1 : (0 : ℝ) < ρ⁻¹ := inv_pos.mpr hρ0
      have h2 : (0 : ℝ) ≤ ‖c‖ * ρ := mul_nonneg (norm_nonneg _) hρ0.le
      linarith
    · have h3 : (0 : ℝ) ≤ 4 * M * ρ ^ 4 :=
        mul_nonneg (mul_nonneg (by norm_num) hM0) (pow_nonneg hρ0.le 4)
      linarith
  have hPcont : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
    have heq : (fun p : ℝ × ℝ => circleMap 0 p.1 p.2)
        = (fun p : ℝ × ℝ => ((p.1 : ℝ) : ℂ) *
          Complex.exp (((p.2 : ℝ) : ℂ) * Complex.I)) := by
      funext p
      exact circleMap_zero p.1 p.2
    rw [heq]
    apply Continuous.mul
    · exact Complex.continuous_ofReal.comp continuous_fst
    · apply Complex.continuous_exp.comp
      apply Continuous.mul _ continuous_const
      exact Complex.continuous_ofReal.comp continuous_snd
  have hUopen : IsOpen (Metric.ball (0 : ℂ) ρ \ {0}) :=
    Metric.isOpen_ball.sdiff isClosed_singleton
  have hUball : Metric.ball (0 : ℂ) ρ ⊆ Metric.ball (0 : ℂ) 1 :=
    Metric.ball_subset_ball (by linarith)
  have hUsub : Metric.ball (0 : ℂ) ρ \ {0} ⊆ Metric.ball (0 : ℂ) 1 \ {0} := by
    intro z hz
    exact ⟨hUball hz.1, hz.2⟩
  have hUeq : (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) ''
      (Set.Ioo 0 ρ ×ˢ Set.univ) = Metric.ball 0 ρ \ {0} := by
    ext w
    constructor
    · rintro ⟨⟨t, θ⟩, ⟨ht, -⟩, rfl⟩
      have ht0 : 0 < t := ht.1
      have htρ : t < ρ := ht.2
      have hn : ‖circleMap 0 t θ‖ = t := by
        rw [norm_circleMap_zero, abs_of_pos ht0]
      constructor
      · rw [Metric.mem_ball, dist_zero_right, hn]
        exact htρ
      · rw [Set.mem_singleton_iff]
        intro hcon
        have hcon' : circleMap 0 t θ = 0 := hcon
        rw [hcon', norm_zero] at hn
        linarith
    · rintro ⟨hwball, hwne⟩
      have hw0 : w ≠ 0 := fun h => hwne (Set.mem_singleton_iff.mpr h)
      have ht0 : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      have htρ : ‖w‖ < ρ := by
        have h := Metric.mem_ball.mp hwball
        rwa [dist_zero_right] at h
      refine ⟨(‖w‖, Complex.arg w), ⟨⟨ht0, htρ⟩, Set.mem_univ _⟩, ?_⟩
      have harg := Complex.norm_mul_exp_arg_mul_I w
      simp only []
      rw [circleMap_zero]
      exact harg
  have hUconn : IsPreconnected (Metric.ball (0 : ℂ) ρ \ {0}) := by
    rw [← hUeq]
    exact IsPreconnected.image (isPreconnected_Ioo.prod isPreconnected_univ)
      (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) hPcont.continuousOn
  have hRnn : (0 : ℝ) ≤ 1 + 4 * M * ρ ^ 4 := by
    have h1 : (0 : ℝ) ≤ 4 * M * ρ ^ 4 :=
      mul_nonneg (mul_nonneg (by norm_num) hM0) (pow_nonneg hρ0.le 4)
    linarith
  have hSeq : (fun p : ℝ × ℝ => koebeEll ρ c (circleMap 0 p.1 p.2)) ''
      (Set.Ioi (1 + 4 * M * ρ ^ 4) ×ˢ Set.univ)
      = (koebeEll ρ c '' Metric.closedBall 0 (1 + 4 * M * ρ ^ 4))ᶜ := by
    ext w
    constructor
    · rintro ⟨⟨t, θ⟩, ⟨ht, -⟩, rfl⟩
      intro hcon
      obtain ⟨x, hxmem, heq⟩ := hcon
      have xinj : x = circleMap 0 t θ := hbij.1 heq
      have hxle : ‖x‖ ≤ 1 + 4 * M * ρ ^ 4 := by
        have h := Metric.mem_closedBall.mp hxmem
        rwa [dist_zero_right] at h
      rw [xinj, norm_circleMap_zero, abs_of_pos (lt_of_le_of_lt hRnn ht)] at hxle
      exact absurd hxle (not_le.mpr ht)
    · intro hw
      obtain ⟨x, hx⟩ := hbij.2 w
      have hxnb : x ∉ Metric.closedBall 0 (1 + 4 * M * ρ ^ 4) := by
        intro hmem
        exact hw ⟨x, hmem, hx⟩
      have hxR : 1 + 4 * M * ρ ^ 4 < ‖x‖ := by
        rw [Metric.mem_closedBall, dist_zero_right, not_le] at hxnb
        exact hxnb
      refine ⟨(‖x‖, Complex.arg x), ⟨hxR, Set.mem_univ _⟩, ?_⟩
      have harg := Complex.norm_mul_exp_arg_mul_I x
      simp only []
      rw [circleMap_zero]
      rw [harg, hx]
  have hSconn : IsPreconnected
      (koebeEll ρ c '' Metric.closedBall 0 (1 + 4 * M * ρ ^ 4))ᶜ := by
    rw [← hSeq]
    have hLcont : Continuous (koebeEll ρ c) := by
      have heq : koebeEll ρ c
          = (fun ζ : ℂ => ((ρ⁻¹ : ℝ) : ℂ) * starRingEnd ℂ ζ +
            c * (ρ : ℂ) * ζ) := by
        funext ζ
        exact koebeEll_apply ρ c ζ
      rw [heq]
      apply Continuous.add
      · apply Continuous.mul continuous_const
        exact Complex.continuous_conj
      · apply Continuous.mul continuous_const continuous_id
    exact IsPreconnected.image (isPreconnected_Ioi.prod isPreconnected_univ)
      (fun p : ℝ × ℝ => koebeEll ρ c (circleMap 0 p.1 p.2))
      (hLcont.comp hPcont).continuousOn
  obtain ⟨N, hN⟩ : ∃ N : ℝ,
      ∀ w ∈ Metric.closedBall (0 : ℂ) (1 / 4), ‖k w‖ ≤ N := by
    have hsub : Metric.closedBall (0 : ℂ) (1 / 4 : ℝ) ⊆ Metric.ball (0 : ℂ) 1 := by
      intro z hz
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    exact IsCompact.exists_bound_of_continuousOn (isCompact_closedBall _ _)
      ((hk.mono hsub).continuousOn)
  set N₁ := |N| + 1 with hN₁def
  have hN0 : (0 : ℝ) ≤ N₁ := by
    rw [hN₁def]
    positivity
  have hNk : ∀ w ∈ Metric.closedBall (0 : ℂ) (1 / 4), ‖k w‖ ≤ N₁ := by
    intro w hw
    have h1 := hN w hw
    rw [hN₁def]
    linarith [le_abs_self N]
  have hGlower : ∀ z ∈ Metric.ball (0 : ℂ) ρ, z ≠ 0 →
      ‖z‖⁻¹ - ‖z‖ * N₁ ≤ ‖G z‖ := by
    intro z hz hzne
    have hzn : ‖z‖ < ρ := by
      have h := Metric.mem_ball.mp hz
      rwa [dist_zero_right] at h
    have hz2mem : z ^ 2 ∈ Metric.closedBall (0 : ℂ) (1 / 4) := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_pow]
      have h1 : ‖z‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzn.le 2
      have h2 : ρ ^ 2 ≤ 1 / 4 := by
        have hle := pow_le_pow_left₀ hρ0.le hρ2 2
        norm_num at hle ⊢
        exact hle
      linarith
    have hkN : ‖k (z ^ 2)‖ ≤ N₁ := hNk _ hz2mem
    rw [hG z]
    have hA : ‖z⁻¹‖ = ‖z‖⁻¹ := norm_inv z
    have hB : ‖z * k (z ^ 2)‖ = ‖z‖ * ‖k (z ^ 2)‖ := norm_mul _ _
    have h := norm_sub_norm_le z⁻¹ (-(z * k (z ^ 2)))
    rw [norm_neg, sub_neg_eq_add] at h
    rw [hA, hB] at h
    have hle : ‖z‖ * ‖k (z ^ 2)‖ ≤ ‖z‖ * N₁ :=
      mul_le_mul_of_nonneg_left hkN (norm_nonneg _)
    linarith
  have hGdiffU : DifferentiableOn ℂ G (Metric.ball 0 ρ \ {0}) := by
    intro z hz
    have hz1 : z ∈ Metric.ball (0 : ℂ) 1 := hUball hz.1
    have hzne : z ≠ 0 := fun hcon => hz.2 (Set.mem_singleton_iff.mpr hcon)
    exact ((hGdiff z hz1 hzne).differentiableWithinAt).mono
      (Set.sdiff_subset.trans hUball)
  have hGanalytic : AnalyticOnNhd ℂ G (Metric.ball 0 ρ \ {0}) :=
    hGdiffU.analyticOnNhd hUopen
  have hmemU : ∀ s : ℝ, 0 < s → s < ρ → ((s : ℝ) : ℂ) ∈
      Metric.ball 0 ρ \ {0} := by
    intro s hs0 hsρ
    constructor
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hs0]
      exact hsρ
    · rw [Set.mem_singleton_iff]
      intro hcon
      have h2 : (s : ℝ) = 0 := by exact_mod_cast hcon
      linarith
  have hGnonconst : ¬ ∃ w, ∀ z ∈ Metric.ball 0 ρ \ {0}, G z = w := by
    rintro ⟨w, hw⟩
    have ha := hmemU (ρ / 2) (by linarith) (by linarith)
    have hb := hmemU (ρ / 4) (by linarith) (by linarith)
    have e1 := hw _ ha
    have e2 := hw _ hb
    have einj := hGinj (hUsub ha) (hUsub hb) (by rw [e1, e2])
    have hconr : (ρ / 2 : ℝ) = ρ / 4 := by exact_mod_cast einj
    linarith
  have hVopen : IsOpen (G '' (Metric.ball 0 ρ \ {0})) := by
    have hor := hGanalytic.is_constant_or_isOpen hUconn
    rcases hor with hconst | hopen
    · exact absurd hconst hGnonconst
    · exact hopen _ (fun x hx => hx) hUopen
  have hInter : ((koebeEll ρ c '' Metric.closedBall 0 (1 + 4 * M * ρ ^ 4))ᶜ ∩
      G '' (Metric.ball 0 ρ \ {0})).Nonempty := by
    set t := min (ρ / 2) (min (1 / (2 * (K + 1))) (1 / (2 * (N₁ + 1))))
      with htdef
    have ht0 : 0 < t := by
      rw [htdef]
      apply lt_min (by linarith)
      apply lt_min
      · apply div_pos (by norm_num)
        have hlt1 : (0 : ℝ) < K + 1 := by linarith
        linarith
      · apply div_pos (by norm_num)
        have hlt1 : (0 : ℝ) < N₁ + 1 := by linarith
        linarith
    have htρ : t < ρ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have htK : t * (2 * (K + 1)) ≤ 1 := by
      have h1 : t ≤ 1 / (2 * (K + 1)) :=
        le_trans (min_le_right _ _) (min_le_left _ _)
      have hpos2 : (0 : ℝ) < 2 * (K + 1) := by
        have hlt1 : (0 : ℝ) < K + 1 := by linarith
        linarith
      rw [le_div_iff₀ hpos2] at h1
      exact h1
    have htN : t * (2 * (N₁ + 1)) ≤ 1 := by
      have h1 : t ≤ 1 / (2 * (N₁ + 1)) :=
        le_trans (min_le_right _ _) (min_le_right _ _)
      have hpos2 : (0 : ℝ) < 2 * (N₁ + 1) := by
        have hlt1 : (0 : ℝ) < N₁ + 1 := by linarith
        linarith
      rw [le_div_iff₀ hpos2] at h1
      exact h1
    have htinv : 2 * (K + 1) ≤ t⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ ht0]
      linarith [htK]
    have htN' : t * N₁ ≤ 1 / 2 := by
      have h1 : t * (2 * N₁) ≤ t * (2 * (N₁ + 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) ht0.le
      linarith [htN]
    have htm := hmemU t ht0 htρ
    refine ⟨G ((t : ℝ) : ℂ), ?_, ⟨_, htm, rfl⟩⟩
    rw [Set.mem_compl_iff]
    rintro ⟨η, hηmem, hηe⟩
    have hηn : ‖η‖ ≤ 1 + 4 * M * ρ ^ 4 := by
      have h := Metric.mem_closedBall.mp hηmem
      rwa [dist_zero_right] at h
    have hKbound : ‖koebeEll ρ c η‖ ≤ K := by
      rw [hKdef]
      have hb := (koebeEll_norm_bounds ρ c η hρ0).2
      have hle : (ρ⁻¹ + ‖c‖ * ρ) * ‖η‖
          ≤ (ρ⁻¹ + ‖c‖ * ρ) * (1 + 4 * M * ρ ^ 4) := by
        apply mul_le_mul_of_nonneg_left hηn
        have h1 : (0 : ℝ) < ρ⁻¹ := inv_pos.mpr hρ0
        have h2 : (0 : ℝ) ≤ ‖c‖ * ρ := mul_nonneg (norm_nonneg _) hρ0.le
        linarith
      linarith
    have hGlb := hGlower _ htm.1
      (fun hcon => htm.2 (Set.mem_singleton_iff.mpr hcon))
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0] at hGlb
    rw [← hηe] at hGlb
    linarith [hGlb, hKbound, htinv, htN']
  have hClosure : closure (G '' (Metric.ball 0 ρ \ {0})) ∩
      (koebeEll ρ c '' Metric.closedBall 0 (1 + 4 * M * ρ ^ 4))ᶜ ⊆
      G '' (Metric.ball 0 ρ \ {0}) := by
    intro w ⟨hwcl, hwS⟩
    obtain ⟨z, hzm, hzt⟩ := mem_closure_iff_seq_limit.mp hwcl
    have hzm' : ∀ n, ∃ y, y ∈ Metric.ball 0 ρ \ {0} ∧ G y = z n := hzm
    choose y hymem hyG using hzm'
    have hymem' : ∀ n, y n ∈ Metric.closedBall (0 : ℂ) ρ := by
      intro n
      exact Metric.ball_subset_closedBall (hymem n).1
    obtain ⟨zstar, hzstar, φ, hφmono, hφlim⟩ :=
      IsCompact.tendsto_subseq (isCompact_closedBall _ _) hymem'
    have hGlim : Filter.Tendsto (fun n => G (y (φ n))) Filter.atTop (nhds w) :=
      (hzt.comp hφmono.tendsto_atTop).congr (fun n => (hyG (φ n)).symm)
    have hzne : zstar ≠ 0 := by
      intro hcon
      have hylim0 : Filter.Tendsto (fun n => ‖y (φ n)‖) Filter.atTop (nhds 0) := by
        have h0 : Filter.Tendsto (fun n => y (φ n)) Filter.atTop (nhds 0) := by
          rw [hcon] at hφlim
          exact hφlim
        have h1 := h0.norm
        rwa [norm_zero] at h1
      have hS : (0 : ℝ) < ‖w‖ + 2 + N₁ := by linarith [norm_nonneg w, hN0]
      have hδ : (0 : ℝ) < 1 / (‖w‖ + 2 + N₁) := div_pos (by norm_num) hS
      have ev1 : ∀ᶠ n in Filter.atTop, ‖y (φ n)‖ < 1 / (‖w‖ + 2 + N₁) :=
        hylim0.eventually (Iio_mem_nhds hδ)
      have ev2 : ∀ᶠ n in Filter.atTop, ‖G (y (φ n))‖ < ‖w‖ + 1 := by
        have h1 := hGlim.norm
        have hlt1 : ‖w‖ < ‖w‖ + 1 := by linarith
        exact h1.eventually (Iio_mem_nhds hlt1)
      obtain ⟨n, hn1, hn2⟩ := (ev1.and ev2).exists
      have hnpos : 0 < ‖y (φ n)‖ := norm_pos_iff.mpr
        (fun h => (hymem (φ n)).2 (Set.mem_singleton_iff.mpr h))
      have hlow := hGlower _ (hymem (φ n)).1
        (fun h => (hymem (φ n)).2 (Set.mem_singleton_iff.mpr h))
      have h1 : ‖w‖ + 2 + N₁ ≤ ‖y (φ n)‖⁻¹ := by
        have hlt := (inv_lt_inv₀ (div_pos (by norm_num) hS) hnpos).mpr hn1
        have hδinv : (1 / (‖w‖ + 2 + N₁))⁻¹ = ‖w‖ + 2 + N₁ := by
          rw [one_div, inv_inv]
        rw [hδinv] at hlt
        exact le_of_lt hlt
      have h2 : ‖y (φ n)‖ * N₁ ≤ 1 := by
        have h3 : ‖y (φ n)‖ * N₁ ≤ (1 / (‖w‖ + 2 + N₁)) * N₁ :=
          mul_le_mul_of_nonneg_right (le_of_lt hn1) hN0
        have h4 : (1 / (‖w‖ + 2 + N₁)) * N₁ ≤ 1 := by
          rw [div_mul_eq_mul_div, div_le_one hS]
          linarith [norm_nonneg w]
        linarith
      linarith
    have hzstar1 : zstar ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right]
      have h := Metric.mem_closedBall.mp hzstar
      rw [dist_zero_right] at h
      linarith
    have hGcont : ContinuousAt G zstar := (hGdiff zstar hzstar1 hzne).continuousAt
    have hwG : G zstar = w := by
      have h1 : Filter.Tendsto (fun n => G (y (φ n))) Filter.atTop (nhds (G zstar)) :=
        hGcont.tendsto.comp hφlim
      exact tendsto_nhds_unique h1 hGlim
    have hzρ : ‖zstar‖ ≤ ρ := by
      have h := Metric.mem_closedBall.mp hzstar
      rwa [dist_zero_right] at h
    rcases lt_or_ge ‖zstar‖ ρ with hltρ | hleρ
    · refine ⟨zstar, ⟨?_, ?_⟩, hwG⟩
      · rw [Metric.mem_ball, dist_zero_right]
        exact hltρ
      · intro hcon
        exact hzne (Set.mem_singleton_iff.mp hcon)
    · have heq : ‖zstar‖ = ρ := le_antisymm hzρ hleρ
      have hρne : ρ ≠ 0 := ne_of_gt hρ0
      have hρc0 : ((ρ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hρne
      have hζ1 : ‖zstar / (ρ : ℂ)‖ = 1 := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0,
          heq, div_self hρne]
      have hmem := koebe_G_circle_mem k G c ρ M (zstar / (ρ : ℂ)) hG hc hM
        hk1 hρ0 hρ2 hρc hζ1
      have hrew : (ρ : ℂ) * (zstar / (ρ : ℂ)) = zstar := by
        rw [mul_comm, div_mul_cancel₀ _ hρc0]
      rw [hrew] at hmem
      rw [← hwG] at hwS
      exact (hwS hmem).elim
  exact hSconn.subset_of_closure_inter_subset hVopen hInter hClosure

private theorem koebe_volume_upper (k G : ℂ → ℂ) (c : ℂ) (ρ r M : ℝ)
    (hk : DifferentiableOn ℂ k (Metric.ball 0 1))
    (hG : ∀ z : ℂ, G z = z⁻¹ + z * k (z ^ 2))
    (hGinj : Set.InjOn G (Metric.ball (0 : ℂ) 1 \ {0}))
    (hGdiff : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → DifferentiableAt ℂ G z)
    (hc : c = k 0)
    (hM : 1 ≤ M)
    (hk1 : ∀ w ∈ Metric.closedBall (0 : ℂ) (1 / 4), ‖dslope k 0 w‖ ≤ M)
    (hρ0 : 0 < ρ) (hρ2 : ρ ≤ 1 / 2)
    (hρc : ‖c‖ * ρ ^ 2 ≤ 1 / 2)
    (hρr : ρ < r) (hr1 : r < 1) :
    volume (G '' koebeAnnulus ρ r) ≤
      ENNReal.ofReal (Real.pi * (1 + 4 * M * ρ ^ 4) ^ 2 *
        (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2)) := by
  have hM0 : (0 : ℝ) ≤ M := le_trans (by norm_num) hM
  have hC := koebe_compl_subset_image k G c ρ M hk hG hGinj hGdiff hc hM hk1
    hρ0 hρ2 hρc
  have hsub01 : Metric.ball (0 : ℂ) ρ ⊆ Metric.ball (0 : ℂ) 1 :=
    Metric.ball_subset_ball (by linarith)
  have hdisj : Disjoint (G '' koebeAnnulus ρ r)
      (G '' (Metric.ball 0 ρ \ {0})) := by
    rw [Set.disjoint_left]
    rintro y ⟨x, hxmem, rfl⟩ ⟨x', hx'mem, heq⟩
    have hxx : ρ < ‖x‖ ∧ ‖x‖ < r := hxmem
    have hx10 : x ≠ 0 := by
      intro hcon
      rw [hcon, norm_zero] at hxx
      linarith
    have hx1 : x ∈ Metric.ball (0 : ℂ) 1 \ {0} := by
      constructor
      · rw [Metric.mem_ball, dist_zero_right]
        linarith [hxx.2, hr1]
      · exact fun h => hx10 (Set.mem_singleton_iff.mp h)
    have hx2 : x' ∈ Metric.ball (0 : ℂ) 1 \ {0} :=
      ⟨hsub01 hx'mem.1, hx'mem.2⟩
    have heqx : x' = x := hGinj hx2 hx1 heq
    have hx'ρ : ‖x'‖ < ρ := by
      have h := Metric.mem_ball.mp hx'mem.1
      rwa [dist_zero_right] at h
    rw [heqx] at hx'ρ
    linarith [hxx.1]
  have hsub : G '' koebeAnnulus ρ r ⊆
      koebeEll ρ c '' Metric.closedBall 0 (1 + 4 * M * ρ ^ 4) := by
    intro y hy
    have hyV : y ∉ G '' (Metric.ball 0 ρ \ {0}) := by
      intro hyV
      rw [Set.disjoint_left] at hdisj
      exact hdisj hy hyV
    by_contra hyS
    have hySc : y ∈ (koebeEll ρ c ''
        Metric.closedBall 0 (1 + 4 * M * ρ ^ 4))ᶜ := hyS
    exact hyV (hC hySc)
  have hRnn : (0 : ℝ) ≤ 1 + 4 * M * ρ ^ 4 := by
    have h1 : (0 : ℝ) ≤ 4 * M * ρ ^ 4 :=
      mul_nonneg (mul_nonneg (by norm_num) hM0) (pow_nonneg hρ0.le 4)
    linarith
  have hvol := koebeEll_volume ρ c (1 + 4 * M * ρ ^ 4) hRnn hρ0
    (lt_of_le_of_lt hρc (by norm_num))
  rw [← hvol]
  exact measure_mono hsub

private theorem koebe_c_le_one (k G : ℂ → ℂ) (m : ℂ → ℂ) (c : ℂ)
    (hk : DifferentiableOn ℂ k (Metric.ball 0 1))
    (hG : ∀ z : ℂ, G z = z⁻¹ + z * k (z ^ 2))
    (hGinj : Set.InjOn G (Metric.ball (0 : ℂ) 1 \ {0}))
    (hG' : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 →
      HasDerivAt G (-(((z ^ 2))⁻¹) + m z) z)
    (hm : DifferentiableOn ℂ m (Metric.ball (0 : ℂ) 1))
    (hm0 : m 0 = c)
    (hc : c = k 0)
    (hmeas : Measurable
      (fun z : ℂ => ENNReal.ofReal (‖-(((z ^ 2))⁻¹) + m z‖ ^ 2))) :
    ‖c‖ ≤ 1 := by
  by_cases hc0 : c = 0
  · rw [hc0, norm_zero]
    norm_num
  · by_contra hcon
    rw [not_le] at hcon
    have hcpos : (0 : ℝ) < ‖c‖ := lt_trans (by norm_num) hcon
    have ha0 : (0 : ℝ) ≤ ‖c‖⁻¹ := inv_nonneg.mpr (norm_nonneg c)
    have ha1 : ‖c‖⁻¹ < 1 := by
      have h1 := mul_lt_mul_of_pos_left hcon (inv_pos.mpr hcpos)
      rwa [mul_one, inv_mul_cancel₀ hcpos.ne'] at h1
    set r := (‖c‖⁻¹ + 1) / 2 with hrdef
    have hr0 : (0 : ℝ) < r := by
      rw [hrdef]
      linarith
    have hr1 : r < 1 := by
      rw [hrdef]
      linarith
    have hr2a : ‖c‖⁻¹ < r ^ 2 := by
      have h1a : (0 : ℝ) < 1 - ‖c‖⁻¹ := by linarith
      have hsq : (0 : ℝ) < (1 - ‖c‖⁻¹) ^ 2 := pow_pos h1a 2
      have e : r ^ 2 - ‖c‖⁻¹ = (1 - ‖c‖⁻¹) ^ 2 / 4 := by
        rw [hrdef]
        ring
      linarith
    have hcs : (1 : ℝ) < ‖c‖ * r ^ 2 := by
      have h1 : ‖c‖ * ‖c‖⁻¹ < ‖c‖ * r ^ 2 :=
        mul_lt_mul_of_pos_left hr2a hcpos
      rwa [mul_inv_cancel₀ hcpos.ne'] at h1
    have hkey : (1 : ℝ) < ‖c‖ ^ 2 * r ^ 4 := by
      have e1 : ‖c‖ ^ 2 * r ^ 4 = (‖c‖ * r ^ 2) ^ 2 := by ring
      rw [e1]
      have hlt := pow_lt_pow_left₀ hcs (by norm_num) two_ne_zero
      rwa [one_pow] at hlt
    have hrne : r ≠ 0 := ne_of_gt hr0
    have hδe : (‖c‖ ^ 2 * r ^ 2 - r⁻¹ ^ 2) * r ^ 2
        = ‖c‖ ^ 2 * r ^ 4 - 1 := by
      have hr1inv : r ^ 2 * r⁻¹ ^ 2 = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hrne, one_pow]
      linear_combination -hr1inv
    have hδ : (0 : ℝ) < ‖c‖ ^ 2 * r ^ 2 - r⁻¹ ^ 2 := by
      have harg : (0 : ℝ) < (‖c‖ ^ 2 * r ^ 2 - r⁻¹ ^ 2) * r ^ 2 := by
        rw [hδe]
        linarith [hkey]
      exact pos_of_mul_pos_left harg (le_of_lt (pow_pos hr0 2))
    obtain ⟨M, hM, hk1⟩ := koebe_dslope_bound k hk
    have hM0 : (0 : ℝ) ≤ M := le_trans (by norm_num) hM
    have hGdiff : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 →
        DifferentiableAt ℂ G z :=
      fun z hz hzne => (hG' z hz hzne).differentiableAt
    set B := 8 * M + 16 * M ^ 2 + 1 with hBdef
    have hBpos : (0 : ℝ) < B := by
      rw [hBdef]
      have h1 : (0 : ℝ) ≤ 8 * M := by linarith
      have h2 : (0 : ℝ) ≤ 16 * M ^ 2 := by positivity
      linarith
    set ρ := min (min (1 / 2) (r / 2))
      (min (1 / (2 * (‖c‖ + 1)))
        ((‖c‖ ^ 2 * r ^ 2 - r⁻¹ ^ 2) / (2 * B))) with hρdef
    have hρ0 : 0 < ρ := by
      rw [hρdef]
      refine lt_min (lt_min (by norm_num) (by linarith [hr0])) (lt_min ?_ ?_)
      · exact div_pos (by norm_num) (by linarith [norm_nonneg c])
      · exact div_pos hδ (by linarith [hBpos])
    have hρ2 : ρ ≤ 1 / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
    have hρr : ρ < r := lt_of_le_of_lt
      (le_trans (min_le_left _ _) (min_le_right _ _)) (by linarith [hr0])
    have hρ1 : ρ ≤ 1 := le_trans hρ2 (by norm_num)
    have hρB : ρ ≤ (‖c‖ ^ 2 * r ^ 2 - r⁻¹ ^ 2) / (2 * B) :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    have hρc : ‖c‖ * ρ ^ 2 ≤ 1 / 2 := by
      have h1 : ρ ≤ 1 / (2 * (‖c‖ + 1)) :=
        le_trans (min_le_right _ _) (min_le_left _ _)
      have h2 : (0 : ℝ) < 2 * (‖c‖ + 1) := by linarith [norm_nonneg c]
      have h3 : ρ * (2 * (‖c‖ + 1)) ≤ 1 := (le_div_iff₀ h2).mp h1
      have h4 : ρ * ‖c‖ ≤ 1 / 2 := by linarith [h3]
      have h5 : ‖c‖ * ρ ^ 2 = (ρ * ‖c‖) * ρ := by ring
      have h6 : (ρ * ‖c‖) * ρ ≤ (1 / 2) * ρ :=
        mul_le_mul_of_nonneg_right h4 hρ0.le
      have h7 : (1 / 2 : ℝ) * ρ ≤ 1 / 2 := by linarith [hρ2]
      linarith [h5, h6, h7]
    have hDnn : 0 ≤ ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2 := by
      have hdet := koebeEll_det_abs ρ c hρ0
        (lt_of_le_of_lt hρc (by norm_num))
      rw [← hdet]
      exact abs_nonneg _
    have hDe : ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2 ≤ ρ⁻¹ ^ 2 := by
      linarith [mul_nonneg (sq_nonneg ‖c‖) (sq_nonneg ρ)]
    have hεnn : (0 : ℝ) ≤ 4 * M * ρ ^ 4 :=
      mul_nonneg (mul_nonneg (by norm_num) hM0) (pow_nonneg hρ0.le 4)
    have hU0 : (0 : ℝ) ≤ Real.pi * (1 + 4 * M * ρ ^ 4) ^ 2 *
        (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2) :=
      mul_nonneg
        (mul_nonneg (le_of_lt Real.pi_pos) (sq_nonneg _)) hDnn
    have hlow := koebe_area_lower G m c ρ r hρ0 hρr hr1 hG' hGinj hm hm0
      hmeas
    have hup := koebe_volume_upper k G c ρ r M hk hG hGinj hGdiff hc hM hk1
      hρ0 hρ2 hρc hρr hr1
    have hboth : ENNReal.ofReal
          (Real.pi * (ρ⁻¹ ^ 2 - r⁻¹ ^ 2) + Real.pi * ‖c‖ ^ 2 * (r ^ 2 - ρ ^ 2))
        ≤ ENNReal.ofReal (Real.pi * (1 + 4 * M * ρ ^ 4) ^ 2 *
          (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2)) :=
      le_trans hlow hup
    have hreal : Real.pi * (ρ⁻¹ ^ 2 - r⁻¹ ^ 2)
          + Real.pi * ‖c‖ ^ 2 * (r ^ 2 - ρ ^ 2)
        ≤ Real.pi * (1 + 4 * M * ρ ^ 4) ^ 2 *
          (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2) :=
      (ENNReal.ofReal_le_ofReal_iff hU0).mp hboth
    have hLfactor : Real.pi * (ρ⁻¹ ^ 2 - r⁻¹ ^ 2)
          + Real.pi * ‖c‖ ^ 2 * (r ^ 2 - ρ ^ 2)
        = Real.pi * ((ρ⁻¹ ^ 2 - r⁻¹ ^ 2) + ‖c‖ ^ 2 * (r ^ 2 - ρ ^ 2)) := by
      ring
    have hUfactor : Real.pi * (1 + 4 * M * ρ ^ 4) ^ 2 *
          (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2)
        = Real.pi * ((1 + 4 * M * ρ ^ 4) ^ 2 *
          (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2)) := by
      ring
    rw [hLfactor, hUfactor] at hreal
    have hdiv : (ρ⁻¹ ^ 2 - r⁻¹ ^ 2) + ‖c‖ ^ 2 * (r ^ 2 - ρ ^ 2)
        ≤ (1 + 4 * M * ρ ^ 4) ^ 2 * (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2) :=
      le_of_mul_le_mul_left hreal Real.pi_pos
    have hLHS : (ρ⁻¹ ^ 2 - r⁻¹ ^ 2) + ‖c‖ ^ 2 * (r ^ 2 - ρ ^ 2)
        = (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2) + (‖c‖ ^ 2 * r ^ 2 - r⁻¹ ^ 2) := by
      ring
    have hstep : (1 + 4 * M * ρ ^ 4) ^ 2 * (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2)
        = (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2)
          + (2 * (4 * M * ρ ^ 4) + (4 * M * ρ ^ 4) ^ 2) *
            (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2) := by
      ring
    rw [hLHS, hstep] at hdiv
    have hδ1 : ‖c‖ ^ 2 * r ^ 2 - r⁻¹ ^ 2
        ≤ (2 * (4 * M * ρ ^ 4) + (4 * M * ρ ^ 4) ^ 2) *
          (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2) := by
      linarith
    have h2εnn : (0 : ℝ) ≤ 2 * (4 * M * ρ ^ 4) + (4 * M * ρ ^ 4) ^ 2 :=
      add_nonneg (mul_nonneg (by norm_num) hεnn) (sq_nonneg _)
    have hδ2 : (2 * (4 * M * ρ ^ 4) + (4 * M * ρ ^ 4) ^ 2) *
          (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2)
        ≤ (2 * (4 * M * ρ ^ 4) + (4 * M * ρ ^ 4) ^ 2) * ρ⁻¹ ^ 2 :=
      mul_le_mul_of_nonneg_left hDe h2εnn
    have hδ3 : (2 * (4 * M * ρ ^ 4) + (4 * M * ρ ^ 4) ^ 2) * ρ⁻¹ ^ 2
        = 8 * M * ρ ^ 2 + 16 * M ^ 2 * ρ ^ 6 := by
      have hρne : ρ ≠ 0 := ne_of_gt hρ0
      field_simp
      ring
    have hδle : ‖c‖ ^ 2 * r ^ 2 - r⁻¹ ^ 2
        ≤ 8 * M * ρ ^ 2 + 16 * M ^ 2 * ρ ^ 6 := by
      rw [← hδ3]
      exact le_trans hδ1 hδ2
    have hBM0 : (0 : ℝ) ≤ 8 * M + 16 * M ^ 2 := by
      have h1 : (0 : ℝ) ≤ 8 * M := by linarith
      have h2 : (0 : ℝ) ≤ 16 * M ^ 2 := by positivity
      linarith
    have hρ6 : ρ ^ 6 ≤ ρ ^ 2 := pow_le_pow_of_le_one hρ0.le hρ1
      (by norm_num)
    have hρ2le : ρ ^ 2 ≤ ρ := by
      rw [pow_two]
      have h := mul_le_mul_of_nonneg_right hρ1 hρ0.le
      rwa [one_mul] at h
    have g1 : 16 * M ^ 2 * ρ ^ 6 ≤ 16 * M ^ 2 * ρ ^ 2 :=
      mul_le_mul_of_nonneg_left hρ6 (by positivity)
    have g2 : (8 * M + 16 * M ^ 2) * ρ ^ 2 ≤ (8 * M + 16 * M ^ 2) * ρ :=
      mul_le_mul_of_nonneg_left hρ2le hBM0
    have hfin : (8 * M + 16 * M ^ 2) * ρ < ‖c‖ ^ 2 * r ^ 2 - r⁻¹ ^ 2 := by
      have h1 : (8 * M + 16 * M ^ 2) * ρ
          ≤ (8 * M + 16 * M ^ 2) *
            ((‖c‖ ^ 2 * r ^ 2 - r⁻¹ ^ 2) / (2 * B)) :=
        mul_le_mul_of_nonneg_left hρB hBM0
      have hBB : 8 * M + 16 * M ^ 2 < 2 * B := by
        rw [hBdef]
        linarith [sq_nonneg M, hM0]
      have hBpos2 : (0 : ℝ) < 2 * B := by linarith [hBpos]
      have h2 : (8 * M + 16 * M ^ 2) *
            ((‖c‖ ^ 2 * r ^ 2 - r⁻¹ ^ 2) / (2 * B))
          < ‖c‖ ^ 2 * r ^ 2 - r⁻¹ ^ 2 := by
        rw [← mul_div_assoc, div_lt_iff₀ hBpos2]
        have h3 := mul_lt_mul_of_pos_right hBB hδ
        linarith
      linarith
    linarith [hδle, g1, g2, hfin]

private theorem koebe_bieberbach
    (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) 1))
    (hginj : Set.InjOn g (Metric.ball (0 : ℂ) 1))
    (hg0 : g 0 = 0)
    (hgderiv : deriv g 0 = 1) :
    ‖iteratedDeriv 2 g 0‖ ≤ 4 := by
  obtain ⟨s, hs, hs0, hsne, heq⟩ :=
    exists_sqrt_of_univalent g hg hginj hg0 hgderiv
  obtain ⟨hk, hkinv, hk0⟩ := koebe_inv_sqrt_expansion s hs hs0 hsne
  set k : ℂ → ℂ := dslope (fun w => (s w)⁻¹) 0 with hkdef
  set G : ℂ → ℂ := fun z => z⁻¹ + z * k (z ^ 2) with hGdef
  have hG : ∀ z : ℂ, G z = z⁻¹ + z * k (z ^ 2) := fun z => rfl
  obtain ⟨hsqmem, hGinv, hGne, hGinj⟩ :=
    koebe_G_injOn g s k G hsne heq hkinv hG hginj
  obtain ⟨hu, hm, hm0, hG'⟩ := koebe_G_hasDerivAt k G hk hG
  have hm' : DifferentiableOn ℂ (deriv (fun z : ℂ => z * k (z ^ 2)))
      (Metric.ball 0 1) := hm
  have hm0' : deriv (fun z : ℂ => z * k (z ^ 2)) 0 = k 0 := hm0
  have hG'' : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → HasDerivAt G
      (-(((z ^ 2))⁻¹) + deriv (fun z : ℂ => z * k (z ^ 2)) z) z := hG'
  have hmeasF : Measurable (fun z : ℂ => ENNReal.ofReal
      (‖-(((z ^ 2))⁻¹) + deriv (fun w : ℂ => w * k (w ^ 2)) z‖ ^ 2)) := by
    apply Measurable.ennreal_ofReal
    apply Measurable.pow_const
    apply Measurable.norm
    apply Measurable.add ((continuous_pow 2).measurable.inv).neg
    exact measurable_deriv _
  have hcle := koebe_c_le_one k G (deriv (fun z : ℂ => z * k (z ^ 2)))
    (k 0) hk hG hGinj hG'' hm' hm0' rfl hmeasF
  have hds := deriv_sqrt_eq_iteratedDeriv_two g s hs hs0 heq
  have e : iteratedDeriv 2 g 0 = -((4 : ℂ) * k 0) := by
    have e1 : iteratedDeriv 2 g 0 = 4 * deriv s 0 := by
      rw [hds]
      ring
    have e2 : deriv s 0 = -k 0 := by
      rw [hk0]
      ring
    rw [e1, e2]
    ring
  have h4 : ‖(4 : ℂ) * k 0‖ = 4 * ‖k 0‖ := by
    rw [norm_mul]
    congr 1
    norm_num
  rw [e, norm_neg, h4]
  linarith [hcle]

/--
**Koebe quarter theorem.** Let $f : \mathbb{C} \to \mathbb{C}$ be holomorphic and injective on the
open unit disk $\mathbb{D} = \{z : |z| < 1\}$, with $f(0) = 0$ and $f'(0) = 1$. Then the image
$f(\mathbb{D})$ contains the open disk $\{w : |w| < 1/4\}$.

Proves `Wanted` entry `koebe_quarter`.

Source: Koebe quarter theorem, conjectured by P. Koebe in 1907 and proved by L. Bieberbach,
Sitzungsberichte der Preussischen Akademie der Wissenschaften (1916), 940–955; see Pommerenke,
Univalent Functions; Lean is normalized schlicht inclusion ball (0:ℂ) (1/4) ⊆ f '' ball 0 1.
-/
theorem koebe_quarter
    (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (hinj : Set.InjOn f (Metric.ball (0 : ℂ) 1))
    (h0 : f 0 = 0)
    (hderiv : deriv f 0 = 1) :
    Metric.ball (0 : ℂ) (1/4 : ℝ) ⊆ f '' Metric.ball (0 : ℂ) 1 := by
  exact koebe_of_bieberbach koebe_bieberbach f hf hinj h0 hderiv

end MathlibExt.Analysis.Complex.KoebeQuarterWanted
end
