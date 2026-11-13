/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Manifold.Riemannian.VariationalEigenvalue
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Real.Pi.Bounds

/-!
Dirichlet interval `(0, π)`: compactly supported bump test function, positive
lower bound `dirichletEigenvalue_pos_lower`, and Neumann-versus-Dirichlet
near-miss `variational_lt_dirichlet`.
-/

namespace Manifold.VariationalEigenvalueIntervalDirichletTest

open Bundle MeasureTheory
open scoped ENNReal NNReal Manifold ContDiff

noncomputable section

/-- Restricted volume on `(0, π)`. -/
abbrev μπ : Measure ℝ := volume.restrict (Set.Ioo 0 Real.pi)

/-- The interval `(0, π)` as an open set. -/
def Uπ : TopologicalSpace.Opens ℝ := ⟨Set.Ioo 0 Real.pi, isOpen_Ioo⟩

/-- Bump centered at `1` with outer radius `1 / 2`. -/
def bumpFn : ContDiffBump (1 : ℝ) :=
  ContDiffBump.mk (1 / 4) (1 / 2) (by norm_num) (by norm_num)

/-- The bump as a smooth map on the real line. -/
def testSmooth : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯ :=
  ⟨(bumpFn : ℝ → ℝ), contMDiff_iff_contDiff.mpr (ContDiffBump.contDiff (n := ⊤) bumpFn)⟩

private lemma μπ_univ : μπ Set.univ = ENNReal.ofReal Real.pi := by
  have h1 : μπ Set.univ = volume (Set.univ ∩ Set.Ioo 0 Real.pi) :=
    Measure.restrict_apply MeasurableSet.univ
  have h2 : (Set.univ ∩ Set.Ioo 0 Real.pi : Set ℝ) = Set.Ioo 0 Real.pi :=
    Set.univ_inter _
  rw [h1, h2, Real.volume_Ioo, sub_zero]

private lemma μπ_pos : 0 < μπ Set.univ := by
  rw [μπ_univ]
  exact ENNReal.ofReal_pos.mpr Real.pi_pos

private lemma μπ_fin : μπ Set.univ < ⊤ := by
  rw [μπ_univ]
  exact ENNReal.ofReal_lt_top

instance : IsFiniteMeasure μπ := ⟨μπ_fin⟩

private lemma test_cont : Continuous (⇑testSmooth : ℝ → ℝ) :=
  ContDiffBump.continuous bumpFn

private lemma test_supp : HasCompactSupport (⇑testSmooth : ℝ → ℝ) :=
  ContDiffBump.hasCompactSupport bumpFn

private lemma tsupport_sub :
    tsupport (⇑testSmooth : ℝ → ℝ) ⊆ Set.Ioo 0 Real.pi := by
  have hts : tsupport (⇑testSmooth : ℝ → ℝ) =
      Metric.closedBall (1 : ℝ) (1 / 2 : ℝ) :=
    ContDiffBump.tsupport_eq bumpFn
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  rw [hts]
  intro (x : ℝ) (hx : x ∈ Metric.closedBall (1 : ℝ) (1 / 2 : ℝ))
  have hmem : dist x (1 : ℝ) ≤ (1 / 2 : ℝ) := Metric.mem_closedBall.mp hx
  have habs : |x - 1| ≤ (1 / 2 : ℝ) := by
    have hdist : dist x (1 : ℝ) = |x - 1| := Real.dist_eq x 1
    rw [← hdist]
    exact hmem
  have hlo : (1 / 2 : ℝ) ≤ x := by
    have h1 : -(1 / 2 : ℝ) ≤ x - 1 := (abs_le.mp habs).1
    linarith
  have hhi : x ≤ (3 / 2 : ℝ) := by
    have h2 : x - 1 ≤ (1 / 2 : ℝ) := (abs_le.mp habs).2
    linarith
  exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩

private lemma test_mem : testSmooth ∈ smoothTestSubmodule 𝓘(ℝ, ℝ) Uπ := by
  have hsub : tsupport (⇑testSmooth : ℝ → ℝ) ⊆ (↑Uπ : Set ℝ) := tsupport_sub
  exact ⟨test_supp, hsub⟩

private lemma test_ne : testSmooth ≠ 0 := by
  have hball : (1 : ℝ) ∈ Metric.closedBall (1 : ℝ) bumpFn.rIn := by
    rw [Metric.mem_closedBall, dist_self]
    show (0 : ℝ) ≤ bumpFn.rIn
    have hr : bumpFn.rIn = (1 / 4 : ℝ) := rfl
    rw [hr]
    norm_num
  have h1 : (⇑testSmooth : ℝ → ℝ) 1 = 1 :=
    ContDiffBump.one_of_mem_closedBall bumpFn hball
  intro (hcon : testSmooth = 0)
  have h0 : (⇑testSmooth : ℝ → ℝ) 1 = 0 := by
    rw [hcon]
    exact congrFun ContMDiffMap.coe_zero 1
  rw [h1] at h0
  exact one_ne_zero h0

private lemma phi_one : ∀ x : ℝ, x ∈ Set.Ioo (3 / 4 : ℝ) (5 / 4 : ℝ) →
    (⇑testSmooth : ℝ → ℝ) x = 1 := by
  intro (x : ℝ) (hx : x ∈ Set.Ioo (3 / 4 : ℝ) (5 / 4 : ℝ))
  have hpair : (3 / 4 : ℝ) < x ∧ x < (5 / 4 : ℝ) := Set.mem_Ioo.mp hx
  have hmem : x ∈ Metric.closedBall (1 : ℝ) bumpFn.rIn := by
    rw [Metric.mem_closedBall, Real.dist_eq]
    show |x - 1| ≤ bumpFn.rIn
    have hr : bumpFn.rIn = (1 / 4 : ℝ) := rfl
    rw [hr, abs_le]
    constructor <;> linarith [hpair.1, hpair.2]
  exact ContDiffBump.one_of_mem_closedBall bumpFn hmem

private lemma mass_pos_vol :
    0 < (∫⁻ x, ‖(⇑testSmooth : ℝ → ℝ) x‖ₑ ^ 2 ∂volume) := by
  have hmeas : MeasurableSet (Set.Ioo (3 / 4 : ℝ) (5 / 4 : ℝ)) :=
    isOpen_Ioo.measurableSet
  have hone : ((‖(1 : ℝ)‖ₑ ^ 2 : ℝ≥0∞)) = 1 := by
    have e1 : ‖(1 : ℝ)‖ₑ = ENNReal.ofReal 1 := by
      rw [Real.enorm_eq_ofReal_abs, abs_one]
    rw [e1]
    simp
  have hle : ∀ x : ℝ, (Set.Ioo (3 / 4 : ℝ) (5 / 4 : ℝ)).indicator
      (fun _ => (1 : ℝ≥0∞)) x ≤ (‖(⇑testSmooth : ℝ → ℝ) x‖ₑ ^ 2 : ℝ≥0∞) := by
    intro (x : ℝ)
    by_cases hx : x ∈ Set.Ioo (3 / 4 : ℝ) (5 / 4 : ℝ)
    · have hi : (Set.Ioo (3 / 4 : ℝ) (5 / 4 : ℝ)).indicator
          (fun _ => (1 : ℝ≥0∞)) x = 1 := Set.indicator_of_mem hx _
      have hp : (⇑testSmooth : ℝ → ℝ) x = 1 := phi_one x hx
      rw [hi, hp]
      exact le_of_eq hone.symm
    · have hi : (Set.Ioo (3 / 4 : ℝ) (5 / 4 : ℝ)).indicator
          (fun _ => (1 : ℝ≥0∞)) x = 0 := Set.indicator_of_notMem hx _
      rw [hi]
      exact bot_le
  have hmono : (∫⁻ x, (Set.Ioo (3 / 4 : ℝ) (5 / 4 : ℝ)).indicator
      (fun _ => (1 : ℝ≥0∞)) x ∂volume) ≤
      (∫⁻ x, ‖(⇑testSmooth : ℝ → ℝ) x‖ₑ ^ 2 ∂volume) :=
    lintegral_mono (fun (x : ℝ) => hle x)
  have hind : (∫⁻ x, (Set.Ioo (3 / 4 : ℝ) (5 / 4 : ℝ)).indicator
      (fun _ => (1 : ℝ≥0∞)) x ∂volume) =
      (∫⁻ _ in Set.Ioo (3 / 4 : ℝ) (5 / 4 : ℝ), (1 : ℝ≥0∞) ∂volume) :=
    lintegral_indicator hmeas _
  have hset : (∫⁻ _ in Set.Ioo (3 / 4 : ℝ) (5 / 4 : ℝ), (1 : ℝ≥0∞) ∂volume) =
      volume (Set.Ioo (3 / 4 : ℝ) (5 / 4 : ℝ)) := by
    have hc : (∫⁻ _ in Set.Ioo (3 / 4 : ℝ) (5 / 4 : ℝ), (1 : ℝ≥0∞) ∂volume) =
        1 * (volume.restrict (Set.Ioo (3 / 4 : ℝ) (5 / 4 : ℝ))) Set.univ :=
      lintegral_const 1
    have hr : (volume.restrict (Set.Ioo (3 / 4 : ℝ) (5 / 4 : ℝ))) Set.univ =
        volume (Set.Ioo (3 / 4 : ℝ) (5 / 4 : ℝ)) := by
      have h1 : (volume.restrict (Set.Ioo (3 / 4 : ℝ) (5 / 4 : ℝ))) Set.univ =
          volume (Set.univ ∩ Set.Ioo (3 / 4 : ℝ) (5 / 4 : ℝ)) :=
        Measure.restrict_apply MeasurableSet.univ
      rw [h1, Set.univ_inter]
    rw [hc, hr, one_mul]
  have hvol : (0 : ℝ≥0∞) < volume (Set.Ioo (3 / 4 : ℝ) (5 / 4 : ℝ)) := by
    have hv : volume (Set.Ioo (3 / 4 : ℝ) (5 / 4 : ℝ)) =
        ENNReal.ofReal (1 / 2 : ℝ) := by
      rw [Real.volume_Ioo]
      norm_num
    rw [hv]
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  have hpos : (0 : ℝ≥0∞) < (∫⁻ x, (Set.Ioo (3 / 4 : ℝ) (5 / 4 : ℝ)).indicator
      (fun _ => (1 : ℝ≥0∞)) x ∂volume) := by
    rw [hind, hset]
    exact hvol
  exact lt_of_lt_of_le hpos hmono

private lemma phi_sq_int :
    Integrable (fun x : ℝ => ((⇑testSmooth : ℝ → ℝ) x) ^ 2) volume := by
  have hcont : Continuous (fun x : ℝ => ((⇑testSmooth : ℝ → ℝ) x) ^ 2) :=
    test_cont.pow 2
  have hsup : HasCompactSupport (fun x : ℝ => ((⇑testSmooth : ℝ → ℝ) x) ^ 2) := by
    have hmul : HasCompactSupport ((⇑testSmooth : ℝ → ℝ) *
        (⇑testSmooth : ℝ → ℝ)) :=
      HasCompactSupport.mul_left (f := (⇑testSmooth : ℝ → ℝ)) test_supp
    have heq : (fun x : ℝ => ((⇑testSmooth : ℝ → ℝ) x) ^ 2) =
        ((⇑testSmooth : ℝ → ℝ) * (⇑testSmooth : ℝ → ℝ)) := by
      funext (x : ℝ)
      rw [pow_two, Pi.mul_apply]
    rw [heq]
    exact hmul
  exact hcont.integrable_of_hasCompactSupport hsup

private lemma mass_ofReal_vol :
    (∫⁻ x, ‖(⇑testSmooth : ℝ → ℝ) x‖ₑ ^ 2 ∂volume) =
      ENNReal.ofReal (∫ x, ((⇑testSmooth : ℝ → ℝ) x) ^ 2 ∂volume) := by
  have hpt : ∀ x : ℝ, (‖(⇑testSmooth : ℝ → ℝ) x‖ₑ ^ 2 : ℝ≥0∞) =
      ENNReal.ofReal (((⇑testSmooth : ℝ → ℝ) x) ^ 2) := by
    intro (x : ℝ)
    rw [Real.enorm_eq_ofReal_abs _,
      ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  have hfun : (fun x : ℝ => (‖(⇑testSmooth : ℝ → ℝ) x‖ₑ ^ 2 : ℝ≥0∞)) =
      (fun x : ℝ => ENNReal.ofReal (((⇑testSmooth : ℝ → ℝ) x) ^ 2)) :=
    funext (fun (x : ℝ) => hpt x)
  have hnn : 0 ≤ᵐ[volume] (fun x : ℝ => ((⇑testSmooth : ℝ → ℝ) x) ^ 2) :=
    Filter.Eventually.of_forall (fun (x : ℝ) => sq_nonneg _)
  have hof : ENNReal.ofReal (∫ x, ((⇑testSmooth : ℝ → ℝ) x) ^ 2 ∂volume) =
      (∫⁻ x, ENNReal.ofReal (((⇑testSmooth : ℝ → ℝ) x) ^ 2) ∂volume) :=
    ofReal_integral_eq_lintegral_ofReal phi_sq_int hnn
  rw [hfun, ← hof]

private lemma fderiv_test_eq : ∀ x : ℝ, fderiv ℝ (⇑testSmooth : ℝ → ℝ) x =
    (deriv (⇑testSmooth : ℝ → ℝ) x) • ContinuousLinearMap.id ℝ ℝ := by
  intro (x : ℝ)
  have hcd : ContDiff ℝ _ (⇑testSmooth : ℝ → ℝ) :=
    ContDiffBump.contDiff (n := ⊤) bumpFn
  have hdiff : DifferentiableAt ℝ (⇑testSmooth : ℝ → ℝ) x :=
    (hcd.differentiable (by simp)).differentiableAt
  have h1 : HasDerivAt (⇑testSmooth : ℝ → ℝ) (deriv (⇑testSmooth : ℝ → ℝ) x) x :=
    hdiff.hasDerivAt
  have heq : ContinuousLinearMap.toSpanSingleton ℝ (deriv (⇑testSmooth : ℝ → ℝ) x) =
      (deriv (⇑testSmooth : ℝ → ℝ) x) • ContinuousLinearMap.id ℝ ℝ := by
    ext
    simp
  have h2 : HasFDerivAt (⇑testSmooth : ℝ → ℝ)
      ((deriv (⇑testSmooth : ℝ → ℝ) x) • ContinuousLinearMap.id ℝ ℝ) x :=
    heq ▸ h1.hasFDerivAt
  exact h2.fderiv

private lemma deriv_sq_int :
    Integrable (fun x : ℝ => (deriv (⇑testSmooth : ℝ → ℝ) x) ^ 2) volume := by
  have hcd : ContDiff ℝ _ (⇑testSmooth : ℝ → ℝ) :=
    ContDiffBump.contDiff (n := ⊤) bumpFn
  have hcont : Continuous (deriv (⇑testSmooth : ℝ → ℝ)) :=
    hcd.continuous_deriv (by simp)
  have hsup : HasCompactSupport
      (fun x : ℝ => (deriv (⇑testSmooth : ℝ → ℝ) x) ^ 2) := by
    have hmul : HasCompactSupport ((deriv (⇑testSmooth : ℝ → ℝ)) *
        (deriv (⇑testSmooth : ℝ → ℝ))) :=
      HasCompactSupport.mul_left (f := (deriv (⇑testSmooth : ℝ → ℝ))) test_supp.deriv
    have heq : (fun x : ℝ => (deriv (⇑testSmooth : ℝ → ℝ) x) ^ 2) =
        ((deriv (⇑testSmooth : ℝ → ℝ)) * (deriv (⇑testSmooth : ℝ → ℝ))) := by
      funext (x : ℝ)
      rw [pow_two, Pi.mul_apply]
    rw [heq]
    exact hmul
  exact (hcont.pow 2).integrable_of_hasCompactSupport hsup

private lemma energy_ofReal_vol :
    dirichletEnergy 𝓘(ℝ, ℝ) volume ⇑testSmooth =
      ENNReal.ofReal (∫ x, (deriv (⇑testSmooth : ℝ → ℝ) x) ^ 2 ∂volume) := by
  have hvec : dirichletEnergy 𝓘(ℝ, ℝ) volume ⇑testSmooth =
      (∫⁻ x, ‖fderiv ℝ (⇑testSmooth : ℝ → ℝ) x‖ₑ ^ 2 ∂volume) :=
    dirichletEnergy_vectorSpace volume ⇑testSmooth
  have hpt : ∀ x : ℝ, (‖fderiv ℝ (⇑testSmooth : ℝ → ℝ) x‖ₑ ^ 2 : ℝ≥0∞) =
      ENNReal.ofReal ((deriv (⇑testSmooth : ℝ → ℝ) x) ^ 2) := by
    intro (x : ℝ)
    have hn : ‖fderiv ℝ (⇑testSmooth : ℝ → ℝ) x‖ =
        |deriv (⇑testSmooth : ℝ → ℝ) x| := by
      rw [fderiv_test_eq x, norm_smul]
      simp [Real.norm_eq_abs]
    have hnn : ‖fderiv ℝ (⇑testSmooth : ℝ → ℝ) x‖₊ =
        ‖(deriv (⇑testSmooth : ℝ → ℝ) x : ℝ)‖₊ :=
      Subtype.ext (hn.trans (Real.norm_eq_abs _).symm)
    have he : (‖fderiv ℝ (⇑testSmooth : ℝ → ℝ) x‖ₑ : ℝ≥0∞) =
        ‖(deriv (⇑testSmooth : ℝ → ℝ) x : ℝ)‖ₑ := by
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm, hnn]
    rw [he, Real.enorm_eq_ofReal_abs _,
      ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  have hfun : (fun x : ℝ => (‖fderiv ℝ (⇑testSmooth : ℝ → ℝ) x‖ₑ ^ 2 : ℝ≥0∞)) =
      (fun x : ℝ => ENNReal.ofReal ((deriv (⇑testSmooth : ℝ → ℝ) x) ^ 2)) :=
    funext (fun (x : ℝ) => hpt x)
  have hnn : 0 ≤ᵐ[volume] (fun x : ℝ => (deriv (⇑testSmooth : ℝ → ℝ) x) ^ 2) :=
    Filter.Eventually.of_forall (fun (x : ℝ) => sq_nonneg _)
  have hof : ENNReal.ofReal (∫ x, (deriv (⇑testSmooth : ℝ → ℝ) x) ^ 2 ∂volume) =
      (∫⁻ x, ENNReal.ofReal ((deriv (⇑testSmooth : ℝ → ℝ) x) ^ 2) ∂volume) :=
    ofReal_integral_eq_lintegral_ofReal deriv_sq_int hnn
  rw [hvec, hfun, ← hof]

/-- Nonzero smooth compactly supported function inside `Uπ`. -/
theorem exists_test_function :
    ∃ u : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯,
      u ∈ smoothTestSubmodule 𝓘(ℝ, ℝ) Uπ ∧ u ≠ 0 :=
  ⟨testSmooth, test_mem, test_ne⟩

/-- Bottom Neumann value on `μπ` is `0` via constants. -/
theorem variationalEigenvalue_zero :
    variationalEigenvalue 𝓘(ℝ, ℝ) ⊤ μπ 0 = 0 := by
  have h1 : ContMDiffMap.const (1 : ℝ) ∈
      (⊤ : Submodule ℝ C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) := Submodule.mem_top
  have hpos : 0 < μπ Set.univ := μπ_pos
  have hfin : μπ Set.univ < ⊤ := μπ_fin
  exact variationalEigenvalue_zero_eq_zero 𝓘(ℝ, ℝ) μπ h1 hpos hfin

/-- Dirichlet bottom value on `Uπ` is finite via the bump span. -/
theorem dirichletEigenvalue_lt_top :
    dirichletEigenvalue 𝓘(ℝ, ℝ) Uπ 0 < ⊤ := by
  have hdir : dirichletEigenvalue 𝓘(ℝ, ℝ) Uπ 0 =
      variationalEigenvalue 𝓘(ℝ, ℝ) (smoothTestSubmodule 𝓘(ℝ, ℝ) Uπ)
        (Manifold.riemannianVolume 𝓘(ℝ, ℝ) ℝ) 0 := rfl
  rw [hdir, Manifold.riemannianVolume_real]
  have hmassφ_ne : (∫⁻ x, ‖(⇑testSmooth : ℝ → ℝ) x‖ₑ ^ 2 ∂volume) ≠ 0 :=
    ne_of_gt mass_pos_vol
  have hmassφ_fin : (∫⁻ x, ‖(⇑testSmooth : ℝ → ℝ) x‖ₑ ^ 2 ∂volume) < ⊤ := by
    rw [mass_ofReal_vol]
    exact ENNReal.ofReal_lt_top
  have henergyφ_fin : dirichletEnergy 𝓘(ℝ, ℝ) volume ⇑testSmooth < ⊤ := by
    rw [energy_ofReal_vol]
    exact ENNReal.ofReal_lt_top
  have hscale_mass : ∀ c : ℝ, (∫⁻ x,
      ‖⇑(c • testSmooth : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) x‖ₑ ^ 2 ∂volume) =
      (‖c‖ₑ ^ 2) * (∫⁻ x, ‖(⇑testSmooth : ℝ → ℝ) x‖ₑ ^ 2 ∂volume) := by
    intro (c : ℝ)
    have hfun : ⇑(c • testSmooth : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) =
        (fun x : ℝ => c * (⇑testSmooth : ℝ → ℝ) x) := by
      rw [ContMDiffMap.coe_smul]
      funext (x : ℝ)
      rw [Pi.smul_apply, smul_eq_mul]
    have hsq : (fun x : ℝ => (⇑(c • testSmooth :
        C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) x) ^ 2) =
        (fun x : ℝ => c ^ 2 * ((⇑testSmooth : ℝ → ℝ) x) ^ 2) := by
      funext (x : ℝ)
      rw [hfun]
      ring
    have hint : Integrable (fun x : ℝ => (⇑(c • testSmooth :
        C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) x) ^ 2) volume := by
      rw [hsq]
      exact phi_sq_int.const_mul _
    have hval : (∫ x, (⇑(c • testSmooth :
        C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) x) ^ 2 ∂volume) =
        c ^ 2 * (∫ x, ((⇑testSmooth : ℝ → ℝ) x) ^ 2 ∂volume) := by
      rw [hsq]
      exact integral_const_mul _ _
    have hc2 : ((‖c‖ₑ ^ 2 : ℝ≥0∞)) = ENNReal.ofReal (c ^ 2) := by
      rw [Real.enorm_eq_ofReal_abs c, ← ENNReal.ofReal_pow (abs_nonneg c),
        sq_abs]
    have hpt : (∫⁻ x, ‖⇑(c • testSmooth :
        C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) x‖ₑ ^ 2 ∂volume) =
        ENNReal.ofReal (∫ x, (⇑(c • testSmooth :
          C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) x) ^ 2 ∂volume) := by
      have hpw : ∀ x : ℝ, (‖⇑(c • testSmooth :
          C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) x‖ₑ ^ 2 : ℝ≥0∞) =
          ENNReal.ofReal ((⇑(c • testSmooth :
            C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) x) ^ 2) := by
        intro (x : ℝ)
        rw [Real.enorm_eq_ofReal_abs _,
          ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
      have hfe : (fun x : ℝ => (‖⇑(c • testSmooth :
          C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) x‖ₑ ^ 2 : ℝ≥0∞)) =
          (fun x : ℝ => ENNReal.ofReal ((⇑(c • testSmooth :
            C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) x) ^ 2)) :=
        funext (fun (x : ℝ) => hpw x)
      have hnn : 0 ≤ᵐ[volume] (fun x : ℝ => (⇑(c • testSmooth :
          C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) x) ^ 2) :=
        Filter.Eventually.of_forall (fun (x : ℝ) => sq_nonneg _)
      have hof : ENNReal.ofReal (∫ x, (⇑(c • testSmooth :
          C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) x) ^ 2 ∂volume) =
          (∫⁻ x, ENNReal.ofReal ((⇑(c • testSmooth :
            C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) x) ^ 2) ∂volume) :=
        ofReal_integral_eq_lintegral_ofReal hint hnn
      rw [hfe, ← hof]
    rw [hpt, hval, ENNReal.ofReal_mul (sq_nonneg c), ← hc2, ← mass_ofReal_vol]
  have hV : ∀ u : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯,
      u ∈ (ℝ ∙ testSmooth :
        Submodule ℝ C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) → u ≠ 0 →
      rayleighQuotient 𝓘(ℝ, ℝ) volume ⇑u =
        rayleighQuotient 𝓘(ℝ, ℝ) volume ⇑testSmooth := by
    intro (u : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) (hu : u ∈ ℝ ∙ testSmooth)
      (hune : u ≠ 0)
    obtain ⟨c, hcu⟩ := Submodule.mem_span_singleton.mp hu
    have hcne : c ≠ 0 := by
      intro (hc0 : c = 0)
      exact hune (by rw [← hcu, hc0]; simp)
    have hueq : u = c • testSmooth := hcu.symm
    have hder : ∀ x : ℝ, deriv (⇑u : ℝ → ℝ) x =
        c * deriv (⇑testSmooth : ℝ → ℝ) x := by
      intro (x : ℝ)
      have hcd : ContDiff ℝ _ (⇑testSmooth : ℝ → ℝ) :=
        ContDiffBump.contDiff (n := ⊤) bumpFn
      have hdiff : DifferentiableAt ℝ (⇑testSmooth : ℝ → ℝ) x :=
        (hcd.differentiable (by simp)).differentiableAt
      have hmul : HasDerivAt (fun y : ℝ => c * (⇑testSmooth : ℝ → ℝ) y)
          (c * deriv (⇑testSmooth : ℝ → ℝ) x) x :=
        hdiff.hasDerivAt.const_mul c
      have heq : (⇑u : ℝ → ℝ) = (fun y : ℝ => c * (⇑testSmooth : ℝ → ℝ) y) := by
        rw [hueq, ContMDiffMap.coe_smul]
        funext (y : ℝ)
        rw [Pi.smul_apply, smul_eq_mul]
      rw [heq]
      exact hmul.deriv
    have hmass_u : (∫⁻ x, ‖(⇑u : ℝ → ℝ) x‖ₑ ^ 2 ∂volume) =
        (‖c‖ₑ ^ 2) * (∫⁻ x, ‖(⇑testSmooth : ℝ → ℝ) x‖ₑ ^ 2 ∂volume) := by
      rw [hueq]
      exact hscale_mass c
    have henergy_u : dirichletEnergy 𝓘(ℝ, ℝ) volume ⇑u =
        (‖c‖ₑ ^ 2) * dirichletEnergy 𝓘(ℝ, ℝ) volume ⇑testSmooth := by
      have hsq : (fun x : ℝ => (deriv (⇑u : ℝ → ℝ) x) ^ 2) =
          (fun x : ℝ => c ^ 2 * (deriv (⇑testSmooth : ℝ → ℝ) x) ^ 2) := by
        funext (x : ℝ)
        rw [hder]
        ring
      have hvec_u : dirichletEnergy 𝓘(ℝ, ℝ) volume ⇑u =
          (∫⁻ x, ‖fderiv ℝ (⇑u : ℝ → ℝ) x‖ₑ ^ 2 ∂volume) :=
        dirichletEnergy_vectorSpace volume ⇑u
      have hpt : ∀ x : ℝ, (‖fderiv ℝ (⇑u : ℝ → ℝ) x‖ₑ ^ 2 : ℝ≥0∞) =
          ENNReal.ofReal ((deriv (⇑u : ℝ → ℝ) x) ^ 2) := by
        intro (x : ℝ)
        have hcd : ContDiff ℝ ∞ (⇑u : ℝ → ℝ) := by
          have hbase : ContDiff ℝ ∞ (⇑testSmooth : ℝ → ℝ) :=
            ContDiffBump.contDiff (n := ⊤) bumpFn
          have hmul : ContDiff ℝ ∞ (fun y : ℝ => c * (⇑testSmooth : ℝ → ℝ) y) :=
            contDiff_const.mul hbase
          have heq : (⇑u : ℝ → ℝ) =
              (fun y : ℝ => c * (⇑testSmooth : ℝ → ℝ) y) := by
            rw [hueq, ContMDiffMap.coe_smul]
            funext (y : ℝ)
            rw [Pi.smul_apply, smul_eq_mul]
          rw [heq]
          exact hmul
        have hdiff : DifferentiableAt ℝ (⇑u : ℝ → ℝ) x :=
          (hcd.differentiable (by simp)).differentiableAt
        have h1 : HasDerivAt (⇑u : ℝ → ℝ) (deriv (⇑u : ℝ → ℝ) x) x :=
          hdiff.hasDerivAt
        have heq2 : ContinuousLinearMap.toSpanSingleton ℝ
            (deriv (⇑u : ℝ → ℝ) x) =
            (deriv (⇑u : ℝ → ℝ) x) • ContinuousLinearMap.id ℝ ℝ := by
          ext
          simp
        have h2 : HasFDerivAt (⇑u : ℝ → ℝ)
            ((deriv (⇑u : ℝ → ℝ) x) • ContinuousLinearMap.id ℝ ℝ) x :=
          heq2 ▸ h1.hasFDerivAt
        have hfd : fderiv ℝ (⇑u : ℝ → ℝ) x =
            (deriv (⇑u : ℝ → ℝ) x) • ContinuousLinearMap.id ℝ ℝ := h2.fderiv
        have hn : ‖fderiv ℝ (⇑u : ℝ → ℝ) x‖ = |deriv (⇑u : ℝ → ℝ) x| := by
          rw [hfd, norm_smul]
          simp [Real.norm_eq_abs]
        have hnn : ‖fderiv ℝ (⇑u : ℝ → ℝ) x‖₊ =
            ‖(deriv (⇑u : ℝ → ℝ) x : ℝ)‖₊ :=
          Subtype.ext (hn.trans (Real.norm_eq_abs _).symm)
        have he : (‖fderiv ℝ (⇑u : ℝ → ℝ) x‖ₑ : ℝ≥0∞) =
            ‖(deriv (⇑u : ℝ → ℝ) x : ℝ)‖ₑ := by
          rw [enorm_eq_nnnorm, enorm_eq_nnnorm, hnn]
        rw [he, Real.enorm_eq_ofReal_abs _,
          ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
      have hint : Integrable (fun x : ℝ => (deriv (⇑u : ℝ → ℝ) x) ^ 2)
          volume := by
        rw [hsq]
        exact deriv_sq_int.const_mul _
      have hval : (∫ x, (deriv (⇑u : ℝ → ℝ) x) ^ 2 ∂volume) =
          c ^ 2 * (∫ x, (deriv (⇑testSmooth : ℝ → ℝ) x) ^ 2 ∂volume) := by
        rw [hsq]
        exact integral_const_mul _ _
      have hnn : 0 ≤ᵐ[volume] (fun x : ℝ => (deriv (⇑u : ℝ → ℝ) x) ^ 2) :=
        Filter.Eventually.of_forall (fun (x : ℝ) => sq_nonneg _)
      have hof : (∫⁻ x, ‖fderiv ℝ (⇑u : ℝ → ℝ) x‖ₑ ^ 2 ∂volume) =
          ENNReal.ofReal (∫ x, (deriv (⇑u : ℝ → ℝ) x) ^ 2 ∂volume) := by
        have hf3 : (fun x : ℝ => (‖fderiv ℝ (⇑u : ℝ → ℝ) x‖ₑ ^ 2 : ℝ≥0∞)) =
            (fun x : ℝ => ENNReal.ofReal ((deriv (⇑u : ℝ → ℝ) x) ^ 2)) :=
          funext (fun (x : ℝ) => hpt x)
        have hof2 : ENNReal.ofReal (∫ x, (deriv (⇑u : ℝ → ℝ) x) ^ 2 ∂volume) =
            (∫⁻ x, ENNReal.ofReal ((deriv (⇑u : ℝ → ℝ) x) ^ 2) ∂volume) :=
          ofReal_integral_eq_lintegral_ofReal hint hnn
        rw [hf3, ← hof2]
      have hc2 : ((‖c‖ₑ ^ 2 : ℝ≥0∞)) = ENNReal.ofReal (c ^ 2) := by
        rw [Real.enorm_eq_ofReal_abs c, ← ENNReal.ofReal_pow (abs_nonneg c),
          sq_abs]
      rw [hvec_u, hof, hval, ENNReal.ofReal_mul (sq_nonneg c), ← hc2,
        ← energy_ofReal_vol]
    have ha0 : (‖c‖ₑ ^ 2 : ℝ≥0∞) ≠ 0 := by
      have hcabs : (0 : ℝ) < |c| ^ 2 := by
        rw [sq_pos_iff]
        exact ne_of_gt (abs_pos.mpr hcne)
      have hpos : (0 : ℝ≥0∞) < ‖c‖ₑ ^ 2 := by
        have heq : ((‖c‖ₑ ^ 2 : ℝ≥0∞)) = ENNReal.ofReal (|c| ^ 2) := by
          rw [Real.enorm_eq_ofReal_abs c, ← ENNReal.ofReal_pow (abs_nonneg c)]
        rw [heq]
        exact ENNReal.ofReal_pos.mpr hcabs
      exact ne_of_gt hpos
    have haT : (‖c‖ₑ ^ 2 : ℝ≥0∞) ≠ ⊤ := by
      have heq : ((‖c‖ₑ ^ 2 : ℝ≥0∞)) = ENNReal.ofReal (c ^ 2) := by
        rw [Real.enorm_eq_ofReal_abs c, ← ENNReal.ofReal_pow (abs_nonneg c),
          sq_abs]
      rw [heq]
      exact ENNReal.ofReal_lt_top.ne
    unfold rayleighQuotient
    rw [hmass_u, henergy_u]
    exact ENNReal.mul_div_mul_left _ _ ha0 haT
  have hsup_le : (⨆ (u : ↥(ℝ ∙ testSmooth :
      Submodule ℝ C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯)), ⨆ (_ : u ≠ 0),
      rayleighQuotient 𝓘(ℝ, ℝ) volume ⇑(u : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯)) ≤
      dirichletEnergy 𝓘(ℝ, ℝ) volume ⇑testSmooth /
        ∫⁻ x, ‖(⇑testSmooth : ℝ → ℝ) x‖ₑ ^ 2 ∂volume := by
    apply iSup_le
    intro (u : ↥(ℝ ∙ testSmooth :
      Submodule ℝ C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯))
    apply iSup_le
    intro (hu0 : u ≠ 0)
    have hu_mem : (u : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) ∈ ℝ ∙ testSmooth :=
      u.property
    have hu_ne : (u : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) ≠ 0 := by
      intro (h0 : (u : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) = 0)
      apply hu0
      apply Subtype.ext
      simpa using h0
    have heq : rayleighQuotient 𝓘(ℝ, ℝ) volume
        ⇑(u : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) =
        rayleighQuotient 𝓘(ℝ, ℝ) volume ⇑testSmooth :=
      hV _ hu_mem hu_ne
    have hrw : rayleighQuotient 𝓘(ℝ, ℝ) volume ⇑testSmooth =
        dirichletEnergy 𝓘(ℝ, ℝ) volume ⇑testSmooth /
          ∫⁻ x, ‖(⇑testSmooth : ℝ → ℝ) x‖ₑ ^ 2 ∂volume := rfl
    rw [heq, hrw]
  exact lt_of_le_of_lt (le_trans (variationalEigenvalue_le_iSup 𝓘(ℝ, ℝ) volume 0 (by
    intro (u : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) (hu : u ∈ ℝ ∙ testSmooth)
    obtain ⟨c, hcu⟩ := Submodule.mem_span_singleton.mp hu
    rw [← hcu]
    exact (smoothTestSubmodule 𝓘(ℝ, ℝ) Uπ).smul_mem c test_mem)
    (finrank_span_singleton test_ne) (by
    intro (u : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) (hu : u ∈ ℝ ∙ testSmooth)
      (hune : u ≠ 0)
    obtain ⟨c, hcu⟩ := Submodule.mem_span_singleton.mp hu
    have hcne : c ≠ 0 := by
      intro (hc0 : c = 0)
      exact hune (by rw [← hcu, hc0]; simp)
    have hueq : u = c • testSmooth := hcu.symm
    have hscale : (∫⁻ x, ‖⇑u x‖ₑ ^ 2 ∂volume) =
        (‖c‖ₑ ^ 2) * (∫⁻ x, ‖(⇑testSmooth : ℝ → ℝ) x‖ₑ ^ 2 ∂volume) := by
      rw [hueq]
      exact hscale_mass c
    have ha0 : (‖c‖ₑ ^ 2 : ℝ≥0∞) ≠ 0 := by
      have hcabs : (0 : ℝ) < |c| ^ 2 := by
        rw [sq_pos_iff]
        exact ne_of_gt (abs_pos.mpr hcne)
      have hpos : (0 : ℝ≥0∞) < ‖c‖ₑ ^ 2 := by
        have heq : ((‖c‖ₑ ^ 2 : ℝ≥0∞)) = ENNReal.ofReal (|c| ^ 2) := by
          rw [Real.enorm_eq_ofReal_abs c, ← ENNReal.ofReal_pow (abs_nonneg c)]
        rw [heq]
        exact ENNReal.ofReal_pos.mpr hcabs
      exact ne_of_gt hpos
    have haT : (‖c‖ₑ ^ 2 : ℝ≥0∞) < ⊤ := by
      have heq : ((‖c‖ₑ ^ 2 : ℝ≥0∞)) = ENNReal.ofReal (c ^ 2) := by
        rw [Real.enorm_eq_ofReal_abs c, ← ENNReal.ofReal_pow (abs_nonneg c),
          sq_abs]
      rw [heq]
      exact ENNReal.ofReal_lt_top
    constructor
    · rw [hscale]
      exact ENNReal.mul_pos ha0 hmassφ_ne
    · rw [hscale]
      exact ENNReal.mul_lt_top haT hmassφ_fin)) hsup_le)
    (ENNReal.div_lt_top henergyφ_fin.ne hmassφ_ne)

/-- The `fderiv` of a smooth real function is `deriv` times the identity. -/
private lemma fderiv_eq_deriv (u : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) (x : ℝ) :
    fderiv ℝ (⇑u : ℝ → ℝ) x =
      (deriv (⇑u : ℝ → ℝ) x) • ContinuousLinearMap.id ℝ ℝ := by
  have hcd : ContDiff ℝ ∞ (⇑u : ℝ → ℝ) :=
    contMDiff_iff_contDiff.mp (ContMDiffMap.contMDiff u)
  have hdiffx : DifferentiableAt ℝ (⇑u : ℝ → ℝ) x :=
    hcd.differentiable (by simp) x
  have h1 : HasDerivAt (⇑u : ℝ → ℝ) (deriv (⇑u : ℝ → ℝ) x) x :=
    hdiffx.hasDerivAt
  have heq : ContinuousLinearMap.toSpanSingleton ℝ (deriv (⇑u : ℝ → ℝ) x) =
      (deriv (⇑u : ℝ → ℝ) x) • ContinuousLinearMap.id ℝ ℝ := by
    ext
    simp
  have h2 : HasFDerivAt (⇑u : ℝ → ℝ)
      ((deriv (⇑u : ℝ → ℝ) x) • ContinuousLinearMap.id ℝ ℝ) x :=
    heq ▸ h1.hasFDerivAt
  exact h2.fderiv

/-- Mass of a Dirichlet test function as a real integral. -/
private lemma mass_eq_real (u : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯)
    (hmem : u ∈ smoothTestSubmodule 𝓘(ℝ, ℝ) Uπ) :
    (∫⁻ x, ‖(⇑u : ℝ → ℝ) x‖ₑ ^ 2 ∂volume) =
      ENNReal.ofReal (∫ x, ((⇑u : ℝ → ℝ) x) ^ 2 ∂volume) := by
  obtain ⟨hsup, _⟩ := hmem
  have hcd : ContDiff ℝ ∞ (⇑u : ℝ → ℝ) :=
    contMDiff_iff_contDiff.mp (ContMDiffMap.contMDiff u)
  have hcont2 : Continuous (fun x : ℝ => ((⇑u : ℝ → ℝ) x) ^ 2) :=
    hcd.continuous.pow 2
  have hsup2 : HasCompactSupport (fun x : ℝ => ((⇑u : ℝ → ℝ) x) ^ 2) := by
    have hmul : HasCompactSupport ((⇑u : ℝ → ℝ) * (⇑u : ℝ → ℝ)) :=
      HasCompactSupport.mul_left (f := (⇑u : ℝ → ℝ)) hsup
    have heq : (fun x : ℝ => ((⇑u : ℝ → ℝ) x) ^ 2) =
        ((⇑u : ℝ → ℝ) * (⇑u : ℝ → ℝ)) := by
      funext (x : ℝ)
      rw [pow_two, Pi.mul_apply]
    rw [heq]
    exact hmul
  have hint : Integrable (fun x : ℝ => ((⇑u : ℝ → ℝ) x) ^ 2) volume :=
    hcont2.integrable_of_hasCompactSupport hsup2
  have hpt : ∀ x : ℝ, (‖(⇑u : ℝ → ℝ) x‖ₑ ^ 2 : ℝ≥0∞) =
      ENNReal.ofReal (((⇑u : ℝ → ℝ) x) ^ 2) := by
    intro (x : ℝ)
    rw [Real.enorm_eq_ofReal_abs _,
      ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  have hfun : (fun x : ℝ => (‖(⇑u : ℝ → ℝ) x‖ₑ ^ 2 : ℝ≥0∞)) =
      (fun x : ℝ => ENNReal.ofReal (((⇑u : ℝ → ℝ) x) ^ 2)) :=
    funext (fun (x : ℝ) => hpt x)
  have hnn : 0 ≤ᵐ[volume] (fun x : ℝ => ((⇑u : ℝ → ℝ) x) ^ 2) :=
    Filter.Eventually.of_forall (fun (x : ℝ) => sq_nonneg _)
  have hof : ENNReal.ofReal (∫ x, ((⇑u : ℝ → ℝ) x) ^ 2 ∂volume) =
      (∫⁻ x, ENNReal.ofReal (((⇑u : ℝ → ℝ) x) ^ 2) ∂volume) :=
    ofReal_integral_eq_lintegral_ofReal hint hnn
  rw [hfun, ← hof]

/-- Energy of a Dirichlet test function as a real integral. -/
private lemma energy_eq_real (u : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯)
    (hmem : u ∈ smoothTestSubmodule 𝓘(ℝ, ℝ) Uπ) :
    dirichletEnergy 𝓘(ℝ, ℝ) volume ⇑u =
      ENNReal.ofReal (∫ x, (deriv (⇑u : ℝ → ℝ) x) ^ 2 ∂volume) := by
  obtain ⟨hsup, _⟩ := hmem
  have hcd : ContDiff ℝ ∞ (⇑u : ℝ → ℝ) :=
    contMDiff_iff_contDiff.mp (ContMDiffMap.contMDiff u)
  have hvec : dirichletEnergy 𝓘(ℝ, ℝ) volume ⇑u =
      (∫⁻ x, ‖fderiv ℝ (⇑u : ℝ → ℝ) x‖ₑ ^ 2 ∂volume) :=
    dirichletEnergy_vectorSpace volume ⇑u
  have hg_cont : Continuous (deriv (⇑u : ℝ → ℝ)) :=
    hcd.continuous_deriv (by simp)
  have hgcont2 : Continuous (fun x : ℝ => (deriv (⇑u : ℝ → ℝ) x) ^ 2) :=
    hg_cont.pow 2
  have hsup2 : HasCompactSupport (fun x : ℝ => (deriv (⇑u : ℝ → ℝ) x) ^ 2) := by
    have hmul : HasCompactSupport ((deriv (⇑u : ℝ → ℝ)) *
        (deriv (⇑u : ℝ → ℝ))) :=
      HasCompactSupport.mul_left (f := (deriv (⇑u : ℝ → ℝ))) hsup.deriv
    have heq : (fun x : ℝ => (deriv (⇑u : ℝ → ℝ) x) ^ 2) =
        ((deriv (⇑u : ℝ → ℝ)) * (deriv (⇑u : ℝ → ℝ))) := by
      funext (x : ℝ)
      rw [pow_two, Pi.mul_apply]
    rw [heq]
    exact hmul
  have hint : Integrable (fun x : ℝ => (deriv (⇑u : ℝ → ℝ) x) ^ 2) volume :=
    hgcont2.integrable_of_hasCompactSupport hsup2
  have hpt : ∀ x : ℝ, (‖fderiv ℝ (⇑u : ℝ → ℝ) x‖ₑ ^ 2 : ℝ≥0∞) =
      ENNReal.ofReal ((deriv (⇑u : ℝ → ℝ) x) ^ 2) := by
    intro (x : ℝ)
    have hn : ‖fderiv ℝ (⇑u : ℝ → ℝ) x‖ =
        |deriv (⇑u : ℝ → ℝ) x| := by
      rw [fderiv_eq_deriv u x, norm_smul]
      simp [Real.norm_eq_abs]
    have hnn : ‖fderiv ℝ (⇑u : ℝ → ℝ) x‖₊ =
        ‖(deriv (⇑u : ℝ → ℝ) x : ℝ)‖₊ :=
      Subtype.ext (hn.trans (Real.norm_eq_abs _).symm)
    have he : (‖fderiv ℝ (⇑u : ℝ → ℝ) x‖ₑ : ℝ≥0∞) =
        ‖(deriv (⇑u : ℝ → ℝ) x : ℝ)‖ₑ := by
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm, hnn]
    rw [he, Real.enorm_eq_ofReal_abs _,
      ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  have hfun : (fun x : ℝ => (‖fderiv ℝ (⇑u : ℝ → ℝ) x‖ₑ ^ 2 : ℝ≥0∞)) =
      (fun x : ℝ => ENNReal.ofReal ((deriv (⇑u : ℝ → ℝ) x) ^ 2)) :=
    funext (fun (x : ℝ) => hpt x)
  have hnn2 : 0 ≤ᵐ[volume] (fun x : ℝ => (deriv (⇑u : ℝ → ℝ) x) ^ 2) :=
    Filter.Eventually.of_forall (fun (x : ℝ) => sq_nonneg _)
  have hof : ENNReal.ofReal (∫ x, (deriv (⇑u : ℝ → ℝ) x) ^ 2 ∂volume) =
      (∫⁻ x, ENNReal.ofReal ((deriv (⇑u : ℝ → ℝ) x) ^ 2) ∂volume) :=
    ofReal_integral_eq_lintegral_ofReal hint hnn2
  rw [hvec, hfun, ← hof]

/-- Real Poincaré inequality on `(0, π)` for Dirichlet test functions. -/
private lemma real_lower_bound (u : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯)
    (hmem : u ∈ smoothTestSubmodule 𝓘(ℝ, ℝ) Uπ) :
    (Real.pi ^ 2)⁻¹ * (∫ x, ((⇑u : ℝ → ℝ) x) ^ 2 ∂volume) ≤
      (∫ x, (deriv (⇑u : ℝ → ℝ) x) ^ 2 ∂volume) := by
  obtain ⟨hsup, hsub⟩ := hmem
  have hU : (↑Uπ : Set ℝ) = Set.Ioo 0 Real.pi := rfl
  have hcd : ContDiff ℝ ∞ (⇑u : ℝ → ℝ) :=
    contMDiff_iff_contDiff.mp (ContMDiffMap.contMDiff u)
  have hu_cont : Continuous (⇑u : ℝ → ℝ) := hcd.continuous
  have hg_cont : Continuous (deriv (⇑u : ℝ → ℝ)) :=
    hcd.continuous_deriv (by simp)
  have hdiff : ∀ x : ℝ, DifferentiableAt ℝ (⇑u : ℝ → ℝ) x := fun (x : ℝ) =>
    hcd.differentiable (by simp) x
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hvan : ∀ x : ℝ, x ∉ Set.Ioo 0 Real.pi → (⇑u : ℝ → ℝ) x = 0 := by
    intro (x : ℝ) (hx : x ∈ Set.Ioo 0 Real.pi → False)
    by_contra hne
    have hsm : x ∈ Function.support (⇑u : ℝ → ℝ) :=
      Function.mem_support.mpr hne
    have hts : x ∈ tsupport (⇑u : ℝ → ℝ) := subset_closure hsm
    have h1 : x ∈ (↑Uπ : Set ℝ) := hsub hts
    rw [hU] at h1
    exact hx h1
  have hu0 : (⇑u : ℝ → ℝ) 0 = 0 := by
    apply hvan 0
    intro (hcon : (0:ℝ) ∈ Set.Ioo 0 Real.pi)
    exact lt_irrefl _ (Set.mem_Ioo.mp hcon).1
  have hFTC : ∀ x : ℝ,
      (∫ t in (0:ℝ)..x, deriv (⇑u : ℝ → ℝ) t) = (⇑u : ℝ → ℝ) x := by
    intro (x : ℝ)
    have hder_int : IntervalIntegrable (deriv (⇑u : ℝ → ℝ)) volume 0 x :=
      hg_cont.intervalIntegrable _ _
    have hftc : (∫ y in (0:ℝ)..x, deriv (⇑u : ℝ → ℝ) y) =
        (⇑u : ℝ → ℝ) x - (⇑u : ℝ → ℝ) 0 :=
      intervalIntegral.integral_deriv_eq_sub
        (fun (y : ℝ) (_ : y ∈ Set.uIcc (0:ℝ) x) => hdiff y) hder_int
    rw [hu0, sub_zero] at hftc
    exact hftc
  have hSnn : (0:ℝ) ≤ ∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t| :=
    intervalIntegral.integral_nonneg (le_of_lt hpi)
      (fun (t : ℝ) (_ : t ∈ Set.Icc (0:ℝ) Real.pi) => abs_nonneg _)
  have hpt : ∀ x : ℝ, x ∈ Set.Icc (0:ℝ) Real.pi →
      |(⇑u : ℝ → ℝ) x| ≤ ∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t| := by
    intro (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) Real.pi)
    have hx0 : (0:ℝ) ≤ x := hx.1
    have hxπ : x ≤ Real.pi := hx.2
    have habs : |∫ t in (0:ℝ)..x, deriv (⇑u : ℝ → ℝ) t| ≤
        ∫ t in (0:ℝ)..x, |deriv (⇑u : ℝ → ℝ) t| :=
      intervalIntegral.abs_integral_le_integral_abs hx0
    have h1 : IntervalIntegrable (fun t : ℝ => |deriv (⇑u : ℝ → ℝ) t|)
        volume 0 x :=
      hg_cont.abs.intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun t : ℝ => |deriv (⇑u : ℝ → ℝ) t|)
        volume x Real.pi :=
      hg_cont.abs.intervalIntegrable _ _
    have hadd : (∫ t in (0:ℝ)..x, |deriv (⇑u : ℝ → ℝ) t|) +
        (∫ t in x..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) =
        (∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) :=
      intervalIntegral.integral_add_adjacent_intervals h1 h2
    have hnn : (0:ℝ) ≤ ∫ t in x..Real.pi, |deriv (⇑u : ℝ → ℝ) t| :=
      intervalIntegral.integral_nonneg hxπ
        (fun (t : ℝ) (_ : t ∈ Set.Icc x Real.pi) => abs_nonneg _)
    rw [← hFTC x]
    linarith [habs, hadd, hnn]
  have hCS : (∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) ^ 2 ≤
      Real.pi * (∫ t in (0:ℝ)..Real.pi, (deriv (⇑u : ℝ → ℝ) t) ^ 2) := by
    have hpi_ne : Real.pi ≠ 0 := ne_of_gt hpi
    have hcont2 : Continuous (fun x : ℝ =>
        (|deriv (⇑u : ℝ → ℝ) x| -
          (∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) / Real.pi) ^ 2) :=
      ((hg_cont.abs).sub continuous_const).pow 2
    have hnn2 : (0:ℝ) ≤ ∫ x in (0:ℝ)..Real.pi,
        (|deriv (⇑u : ℝ → ℝ) x| -
          (∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) / Real.pi) ^ 2 :=
      intervalIntegral.integral_nonneg (le_of_lt hpi)
        (fun (x : ℝ) (_ : x ∈ Set.Icc (0:ℝ) Real.pi) => sq_nonneg _)
    have hexpand : (∫ x in (0:ℝ)..Real.pi,
          (|deriv (⇑u : ℝ → ℝ) x| -
            (∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) / Real.pi) ^ 2) =
        (∫ t in (0:ℝ)..Real.pi, (deriv (⇑u : ℝ → ℝ) t) ^ 2) -
          2 * ((∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) / Real.pi) *
            (∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) +
          (((∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) / Real.pi) ^ 2) *
            Real.pi := by
      have hpt2 : ∀ x : ℝ,
          (|deriv (⇑u : ℝ → ℝ) x| -
            (∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) / Real.pi) ^ 2 =
            (deriv (⇑u : ℝ → ℝ) x) ^ 2 +
              ((-2 * ((∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) /
                Real.pi)) * |deriv (⇑u : ℝ → ℝ) x| +
                (((∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) /
                  Real.pi) ^ 2)) := by
        intro (x : ℝ)
        have hsq : (|deriv (⇑u : ℝ → ℝ) x|) ^ 2 =
            (deriv (⇑u : ℝ → ℝ) x) ^ 2 :=
          sq_abs _
        calc (|deriv (⇑u : ℝ → ℝ) x| -
              (∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) / Real.pi) ^ 2
              = (|deriv (⇑u : ℝ → ℝ) x|) ^ 2 -
                2 * ((∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) /
                  Real.pi) * |deriv (⇑u : ℝ → ℝ) x| +
                (((∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) /
                  Real.pi) ^ 2) := by
                ring
            _ = _ := by rw [hsq]; ring
      have e1 : (∫ x in (0:ℝ)..Real.pi,
            (|deriv (⇑u : ℝ → ℝ) x| -
              (∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) / Real.pi) ^ 2) =
          ∫ x in (0:ℝ)..Real.pi,
            ((deriv (⇑u : ℝ → ℝ) x) ^ 2 +
              ((-2 * ((∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) /
                Real.pi)) * |deriv (⇑u : ℝ → ℝ) x| +
                (((∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) /
                  Real.pi) ^ 2))) :=
        intervalIntegral.integral_congr
          (fun (x : ℝ) (_ : x ∈ Set.uIcc (0:ℝ) Real.pi) => hpt2 x)
      have j1 : IntervalIntegrable (fun x : ℝ => (deriv (⇑u : ℝ → ℝ) x) ^ 2)
          volume 0 Real.pi :=
        (hg_cont.pow 2).intervalIntegrable _ _
      have j2 : IntervalIntegrable (fun x : ℝ =>
          (-2 * ((∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) / Real.pi)) *
            |deriv (⇑u : ℝ → ℝ) x|) volume 0 Real.pi :=
        (continuous_const.mul hg_cont.abs).intervalIntegrable _ _
      have j23 : IntervalIntegrable (fun x : ℝ =>
          (-2 * ((∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) / Real.pi)) *
            |deriv (⇑u : ℝ → ℝ) x| +
            (((∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) / Real.pi) ^ 2))
          volume 0 Real.pi :=
        ((continuous_const.mul hg_cont.abs).add continuous_const).intervalIntegrable
          _ _
      have j3 : IntervalIntegrable (fun _ : ℝ =>
          (((∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) / Real.pi) ^ 2 : ℝ))
          volume 0 Real.pi :=
        intervalIntegrable_const
      rw [e1, intervalIntegral.integral_add j1 j23,
        intervalIntegral.integral_add j2 j3, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const]
      simp only [smul_eq_mul, sub_zero]
      ring
    rw [hexpand] at hnn2
    have hfield : ((∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) / Real.pi) ^ 2 *
        Real.pi =
        ((∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) / Real.pi) *
          (∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) := by
      rw [pow_two, mul_assoc, div_mul_cancel₀ _ hpi_ne]
    have hle : ((∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) / Real.pi) *
        (∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) ≤
        (∫ t in (0:ℝ)..Real.pi, (deriv (⇑u : ℝ → ℝ) t) ^ 2) := by
      linarith [hnn2, hfield]
    have hS2 : (((∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) / Real.pi) *
        (∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|)) * Real.pi =
        (∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) ^ 2 := by
      rw [mul_right_comm, div_mul_cancel₀ _ hpi_ne, pow_two]
    calc (∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) ^ 2
        = ((((∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) / Real.pi) *
          (∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|)) * Real.pi) := hS2.symm
      _ ≤ (∫ t in (0:ℝ)..Real.pi, (deriv (⇑u : ℝ → ℝ) t) ^ 2) * Real.pi :=
          mul_le_mul_of_nonneg_right hle (le_of_lt hpi)
      _ = Real.pi * (∫ t in (0:ℝ)..Real.pi, (deriv (⇑u : ℝ → ℝ) t) ^ 2) :=
          mul_comm _ _
  have hMint : (∫ t in (0:ℝ)..Real.pi, ((⇑u : ℝ → ℝ) t) ^ 2) ≤
      Real.pi * (∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) ^ 2 := by
    have hsq_int : IntervalIntegrable (fun t : ℝ => ((⇑u : ℝ → ℝ) t) ^ 2)
        volume 0 Real.pi :=
      (hu_cont.pow 2).intervalIntegrable _ _
    have hconst_int : IntervalIntegrable (fun _ : ℝ =>
        (((∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) ^ 2 : ℝ)))
        volume 0 Real.pi :=
      intervalIntegrable_const
    have hsqpt : ∀ x : ℝ, x ∈ Set.Icc (0:ℝ) Real.pi →
        ((⇑u : ℝ → ℝ) x) ^ 2 ≤
          (∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) ^ 2 := by
      intro (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) Real.pi)
      have h12 := abs_le.mp (hpt x hx)
      exact sq_le_sq' h12.1 h12.2
    have hmono : (∫ t in (0:ℝ)..Real.pi, ((⇑u : ℝ → ℝ) t) ^ 2) ≤
        (∫ x in (0:ℝ)..Real.pi,
          (((∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) ^ 2 : ℝ))) :=
      intervalIntegral.integral_mono_on (le_of_lt hpi) hsq_int hconst_int hsqpt
    have hconst_val : (∫ x in (0:ℝ)..Real.pi,
        (((∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) ^ 2 : ℝ))) =
        Real.pi * ((∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) ^ 2) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul, sub_zero]
    rw [hconst_val] at hmono
    exact hmono
  have hE_int : Integrable (fun x : ℝ => (deriv (⇑u : ℝ → ℝ) x) ^ 2) volume := by
    have hgcont2 : Continuous (fun x : ℝ => (deriv (⇑u : ℝ → ℝ) x) ^ 2) :=
      hg_cont.pow 2
    have hsup2 : HasCompactSupport (fun x : ℝ => (deriv (⇑u : ℝ → ℝ) x) ^ 2) := by
      have hmul : HasCompactSupport ((deriv (⇑u : ℝ → ℝ)) *
          (deriv (⇑u : ℝ → ℝ))) :=
        HasCompactSupport.mul_left (f := (deriv (⇑u : ℝ → ℝ))) hsup.deriv
      have heq : (fun x : ℝ => (deriv (⇑u : ℝ → ℝ) x) ^ 2) =
          ((deriv (⇑u : ℝ → ℝ)) * (deriv (⇑u : ℝ → ℝ))) := by
        funext (x : ℝ)
        rw [pow_two, Pi.mul_apply]
      rw [heq]
      exact hmul
    exact hgcont2.integrable_of_hasCompactSupport hsup2
  have hQ_le_E : (∫ t in (0:ℝ)..Real.pi, (deriv (⇑u : ℝ → ℝ) t) ^ 2) ≤
      (∫ x, (deriv (⇑u : ℝ → ℝ) x) ^ 2 ∂volume) := by
    have hIoc : (∫ t in (0:ℝ)..Real.pi, (deriv (⇑u : ℝ → ℝ) t) ^ 2) =
        ∫ x in Set.Ioc 0 Real.pi, (deriv (⇑u : ℝ → ℝ) x) ^ 2 ∂volume :=
      intervalIntegral.integral_of_le (le_of_lt hpi)
    have hmono : (∫ x in Set.Ioc (0:ℝ) Real.pi, (deriv (⇑u : ℝ → ℝ) x) ^ 2
        ∂volume) ≤
        (∫ x in Set.univ, (deriv (⇑u : ℝ → ℝ) x) ^ 2 ∂volume) :=
      setIntegral_mono_set (hE_int.integrableOn)
        (Filter.Eventually.of_forall
          (fun (x : ℝ) => sq_nonneg ((deriv (⇑u : ℝ → ℝ) x))))
        (Filter.Eventually.of_forall
          (fun (x : ℝ) (_ : x ∈ Set.Ioc 0 Real.pi) => Set.mem_univ x))
    have huniv : (∫ x in Set.univ, (deriv (⇑u : ℝ → ℝ) x) ^ 2 ∂volume) =
        (∫ x, (deriv (⇑u : ℝ → ℝ) x) ^ 2 ∂volume) := by
      rw [Measure.restrict_univ]
    rw [hIoc, ← huniv]
    exact hmono
  have hM_eq : (∫ x, ((⇑u : ℝ → ℝ) x) ^ 2 ∂volume) =
      (∫ t in (0:ℝ)..Real.pi, ((⇑u : ℝ → ℝ) t) ^ 2) := by
    have hms : MeasurableSet (Set.Ioo (0:ℝ) Real.pi) := isOpen_Ioo.measurableSet
    have hIoo : (∫ x, ((⇑u : ℝ → ℝ) x) ^ 2 ∂volume) =
        ∫ x in Set.Ioo 0 Real.pi, ((⇑u : ℝ → ℝ) x) ^ 2 ∂volume := by
      have hcongr : (fun x : ℝ => ((⇑u : ℝ → ℝ) x) ^ 2) =ᵐ[volume]
          (Set.Ioo 0 Real.pi).indicator
            (fun y : ℝ => ((⇑u : ℝ → ℝ) y) ^ 2) := by
        apply Filter.Eventually.of_forall
        intro (x : ℝ)
        by_cases hx : x ∈ Set.Ioo 0 Real.pi
        · rw [Set.indicator_of_mem hx _]
        · have h0 : (⇑u : ℝ → ℝ) x = 0 := hvan x hx
          simp [h0, Set.indicator_of_notMem hx _]
      have h1 : (∫ x, ((⇑u : ℝ → ℝ) x) ^ 2 ∂volume) =
          (∫ x, (Set.Ioo 0 Real.pi).indicator
            (fun y : ℝ => ((⇑u : ℝ → ℝ) y) ^ 2) x ∂volume) :=
        integral_congr_ae hcongr
      rwa [integral_indicator hms] at h1
    have hIoc : (∫ x in Set.Ioo (0:ℝ) Real.pi, ((⇑u : ℝ → ℝ) x) ^ 2 ∂volume) =
        ∫ x in Set.Ioc 0 Real.pi, ((⇑u : ℝ → ℝ) x) ^ 2 ∂volume := by
      rw [integral_Ioc_eq_integral_Ioo]
    have hle : (∫ t in (0:ℝ)..Real.pi, ((⇑u : ℝ → ℝ) t) ^ 2) =
        ∫ x in Set.Ioc 0 Real.pi, ((⇑u : ℝ → ℝ) x) ^ 2 ∂volume :=
      intervalIntegral.integral_of_le (le_of_lt hpi)
    rw [hIoo, hIoc, ← hle]
  have hchain : (∫ x, ((⇑u : ℝ → ℝ) x) ^ 2 ∂volume) ≤
      Real.pi ^ 2 * (∫ x, (deriv (⇑u : ℝ → ℝ) x) ^ 2 ∂volume) := by
    rw [hM_eq]
    calc (∫ t in (0:ℝ)..Real.pi, ((⇑u : ℝ → ℝ) t) ^ 2)
        ≤ Real.pi * (∫ t in (0:ℝ)..Real.pi, |deriv (⇑u : ℝ → ℝ) t|) ^ 2 :=
          hMint
      _ ≤ Real.pi *
          (Real.pi * (∫ t in (0:ℝ)..Real.pi, (deriv (⇑u : ℝ → ℝ) t) ^ 2)) :=
          mul_le_mul_of_nonneg_left hCS (le_of_lt hpi)
      _ = Real.pi ^ 2 * (∫ t in (0:ℝ)..Real.pi, (deriv (⇑u : ℝ → ℝ) t) ^ 2) := by
          ring
      _ ≤ Real.pi ^ 2 * (∫ x, (deriv (⇑u : ℝ → ℝ) x) ^ 2 ∂volume) :=
          mul_le_mul_of_nonneg_left hQ_le_E (pow_nonneg (le_of_lt hpi) 2)
  have hpi2 : (0:ℝ) < Real.pi ^ 2 := pow_pos hpi 2
  calc (Real.pi ^ 2)⁻¹ * (∫ x, ((⇑u : ℝ → ℝ) x) ^ 2 ∂volume)
      ≤ (Real.pi ^ 2)⁻¹ *
        (Real.pi ^ 2 * (∫ x, (deriv (⇑u : ℝ → ℝ) x) ^ 2 ∂volume)) :=
        mul_le_mul_of_nonneg_left hchain (le_of_lt (inv_pos.mpr hpi2))
    _ = (∫ x, (deriv (⇑u : ℝ → ℝ) x) ^ 2 ∂volume) :=
        inv_mul_cancel_left₀ (ne_of_gt hpi2) _

/-- Uniform Rayleigh lower bound for Dirichlet test functions. -/
private lemma rayleigh_lower (u : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯)
    (hmem : u ∈ smoothTestSubmodule 𝓘(ℝ, ℝ) Uπ)
    (hmass_ne : (∫⁻ x, ‖(⇑u : ℝ → ℝ) x‖ₑ ^ 2 ∂volume) ≠ 0)
    (hmass_fin : (∫⁻ x, ‖(⇑u : ℝ → ℝ) x‖ₑ ^ 2 ∂volume) ≠ ⊤) :
    ENNReal.ofReal ((Real.pi ^ 2)⁻¹) ≤ rayleighQuotient 𝓘(ℝ, ℝ) volume ⇑u := by
  have hreal : (Real.pi ^ 2)⁻¹ * (∫ x, ((⇑u : ℝ → ℝ) x) ^ 2 ∂volume) ≤
      (∫ x, (deriv (⇑u : ℝ → ℝ) x) ^ 2 ∂volume) :=
    real_lower_bound u hmem
  have hmass : (∫⁻ x, ‖(⇑u : ℝ → ℝ) x‖ₑ ^ 2 ∂volume) =
      ENNReal.ofReal (∫ x, ((⇑u : ℝ → ℝ) x) ^ 2 ∂volume) :=
    mass_eq_real u hmem
  have henergy : dirichletEnergy 𝓘(ℝ, ℝ) volume ⇑u =
      ENNReal.ofReal (∫ x, (deriv (⇑u : ℝ → ℝ) x) ^ 2 ∂volume) :=
    energy_eq_real u hmem
  have hcnn : (0:ℝ) ≤ (Real.pi ^ 2)⁻¹ :=
    le_of_lt (inv_pos.mpr (pow_pos Real.pi_pos 2))
  have hM0 : ENNReal.ofReal (∫ x, ((⇑u : ℝ → ℝ) x) ^ 2 ∂volume) ≠ 0 := by
    rw [← hmass]
    exact hmass_ne
  have hMT : ENNReal.ofReal (∫ x, ((⇑u : ℝ → ℝ) x) ^ 2 ∂volume) ≠ ⊤ := by
    rw [← hmass]
    exact hmass_fin
  unfold rayleighQuotient
  rw [henergy, hmass,
    ENNReal.le_div_iff_mul_le (Or.inl hM0) (Or.inl hMT),
    ← ENNReal.ofReal_mul hcnn]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Dirichlet bottom on `(0, π)` is at least the explicit constant `(π ^ 2)⁻¹`. -/
theorem dirichletEigenvalue_pos_lower :
    ENNReal.ofReal ((Real.pi ^ 2)⁻¹) ≤ dirichletEigenvalue 𝓘(ℝ, ℝ) Uπ 0 := by
  have hdir : dirichletEigenvalue 𝓘(ℝ, ℝ) Uπ 0 =
      variationalEigenvalue 𝓘(ℝ, ℝ) (smoothTestSubmodule 𝓘(ℝ, ℝ) Uπ)
        (Manifold.riemannianVolume 𝓘(ℝ, ℝ) ℝ) 0 := rfl
  rw [hdir, Manifold.riemannianVolume_real]
  refine le_variationalEigenvalue 𝓘(ℝ, ℝ) volume 0
    (fun u hu hune hpos hfin => ?_)
  exact rayleigh_lower u hu (ne_of_gt hpos) (ne_of_lt hfin)

/-- The boundary condition changes the value: Neumann bottom `0` is below Dirichlet bottom. -/
theorem variational_lt_dirichlet :
    variationalEigenvalue 𝓘(ℝ, ℝ) ⊤ μπ 0 <
      dirichletEigenvalue 𝓘(ℝ, ℝ) Uπ 0 := by
  have h0 : variationalEigenvalue 𝓘(ℝ, ℝ) ⊤ μπ 0 = 0 :=
    variationalEigenvalue_zero
  have hle : ENNReal.ofReal ((Real.pi ^ 2)⁻¹) ≤
      dirichletEigenvalue 𝓘(ℝ, ℝ) Uπ 0 :=
    dirichletEigenvalue_pos_lower
  have hpos : (0:ℝ≥0∞) < ENNReal.ofReal ((Real.pi ^ 2)⁻¹) :=
    ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos Real.pi_pos 2))
  rw [h0]
  exact lt_of_lt_of_le hpos hle

/-- The bump mass is positive and finite via the core mass lemma. -/
theorem mass_pos_finite_core :
    0 < (∫⁻ x, ‖(⇑testSmooth : ℝ → ℝ) x‖ₑ ^ 2 ∂volume) ∧
      (∫⁻ x, ‖(⇑testSmooth : ℝ → ℝ) x‖ₑ ^ 2 ∂volume) < ⊤ :=
  Manifold.mass_pos_lt_top_of_mem_smoothTestSubmodule volume test_mem test_ne

end

end Manifold.VariationalEigenvalueIntervalDirichletTest
