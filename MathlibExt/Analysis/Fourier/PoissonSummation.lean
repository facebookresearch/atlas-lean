/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_SchwartzMap_tsum_eq_tsum_fourier_euclideanSpace.lean`
and
`P2M/Sol/S_SchwartzMap_tsum_eq_tsum_fourier_euclideanSpace.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

open MeasureTheory Real Complex Set TopologicalSpace Topology Submodule WithLp
open scoped FourierTransform InnerProductSpace

noncomputable section

namespace PiPoissonSummation

variable {d : Type*} [Fintype d]

private def intVec (n : d → ℤ) : d → ℝ := fun i => (n i : ℝ)

private def periodize (f : (d → ℝ) → ℂ) (x : d → ℝ) : ℂ :=
  ∑' n : d → ℤ, f (x + intVec n)

private theorem periodize_add_intVec (f : (d → ℝ) → ℂ) (x : d → ℝ) (m : d → ℤ) :
    periodize f (x + intVec m) = periodize f x := by
  unfold periodize
  have hstep : ∀ n : d → ℤ,
      f (x + intVec m + intVec n) = f (x + intVec ((Equiv.addLeft m) n)) := fun n => by
    congr 1
    unfold intVec
    ext i; simp only [Equiv.coe_addLeft, Pi.add_apply]; push_cast; ring
  rw [tsum_congr hstep, (Equiv.addLeft m).tsum_eq (fun n : d → ℤ => f (x + intVec n))]

private def toUnitAddTorus : (d → ℝ) → UnitAddTorus d := fun x i => (x i : UnitAddCircle)

private def piFourierIntegral (f : (d → ℝ) → ℂ) (ξ : d → ℝ) : ℂ :=
  ∫ v, f v * (𝐞 (-∑ i, v i * ξ i) : ℂ) ∂(volume : Measure (d → ℝ))

private theorem toUnitAddTorus_add_intVec (x : d → ℝ) (n : d → ℤ) :
    toUnitAddTorus (x + intVec n) = toUnitAddTorus x := by
  funext i
  simp only [toUnitAddTorus, intVec, Pi.add_apply]
  have : ((n i : ℝ) : UnitAddCircle) = 0 := by
    exact_mod_cast (AddCircle.coe_eq_zero_iff 1 (x := (n i : ℝ))).mpr ⟨n i, by simp⟩
  rw [AddCircle.coe_add, this, add_zero]

private theorem mFourier_toUnitAddTorus (m : d → ℤ) (x : d → ℝ) :
    UnitAddTorus.mFourier m (toUnitAddTorus x) = (𝐞 (∑ i, (m i : ℝ) * x i) : ℂ) := by
  simp only [toUnitAddTorus, UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply,
    Real.fourierChar_apply]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

section FourierCoeff

private def negCharCM (m : d → ℤ) : C((d → ℝ), ℂ) :=
  (UnitAddTorus.mFourier (-m)).comp
    ⟨toUnitAddTorus, continuous_pi fun i =>
      (AddCircle.continuous_mk' 1).comp (continuous_apply i)⟩

private theorem norm_negCharCM (m : d → ℤ) (x : d → ℝ) : ‖negCharCM m x‖ = 1 := by
  simp only [negCharCM, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    UnitAddTorus.mFourier, norm_prod]
  simp only [fourier_apply, Circle.norm_coe, Finset.prod_const_one]

private theorem negCharCM_add_intVec (m : d → ℤ) (x : d → ℝ) (n : d → ℤ) :
    negCharCM m (x + intVec n) = negCharCM m x := by
  simp only [negCharCM, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    toUnitAddTorus_add_intVec]

private theorem negCharCM_eq_fourierChar (m : d → ℤ) (x : d → ℝ) :
    negCharCM m x = (𝐞 (-∑ i, x i * (m i : ℝ)) : ℂ) := by
  simp only [negCharCM, ContinuousMap.comp_apply, ContinuousMap.coe_mk, toUnitAddTorus,
    UnitAddTorus.mFourier, Pi.neg_apply, fourier_coe_apply, Real.fourierChar_apply]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [← Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

private theorem pi_Ioc_ae_eq_pi_Ico :
    {x : d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}
      =ᵐ[(volume : Measure (d → ℝ))]
    Set.pi Set.univ (fun _ : d => Set.Ico (0 : ℝ) 1) := by
  have h1 : {x : d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}
      = Set.pi Set.univ (fun _ : d => Set.Ioc (0 : ℝ) 1) := by
    ext x; simp
  rw [h1]
  exact (Measure.univ_pi_Ioc_ae_eq_Icc).trans (Measure.univ_pi_Ico_ae_eq_Icc).symm

private theorem coe_basisFun_equivFun_symm (n : d → ℤ) :
    ((((Pi.basisFun ℝ d).restrictScalars ℤ).equivFun.symm n :
        span ℤ (Set.range (Pi.basisFun ℝ d))) : d → ℝ) = intVec n := by
  classical
  rw [Module.Basis.equivFun_symm_apply]
  simp only [Submodule.coe_sum, SetLike.val_smul, Module.Basis.restrictScalars_apply,
    Pi.basisFun_apply]
  ext j
  simp only [intVec, Finset.sum_apply, Pi.smul_apply, Pi.single_apply,
    smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp [zsmul_eq_mul]

private theorem mFourierCoeff_eq_piFourierIntegral (f : C((d → ℝ), ℂ))
    (hf : ∀ K : Compacts (d → ℝ),
      Summable fun n : d → ℤ => ‖(f.comp (ContinuousMap.addRight (intVec n))).restrict K‖)
    (hf_int : Integrable (⇑f) (volume : Measure (d → ℝ)))
    (F : C(UnitAddTorus d, ℂ))
    (hF : ∀ x : d → ℝ, F (toUnitAddTorus x) = periodize f x)
    (m : d → ℤ) :
    UnitAddTorus.mFourierCoeff F m = piFourierIntegral f (intVec m) := by
  classical

  set e : C((d → ℝ), ℂ) := negCharCM m with he_def
  let cubeIoc : Set (d → ℝ) := {x | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}
  let cubeIcc : Set (d → ℝ) := Set.Icc (0 : d → ℝ) 1
  have hcubeIoc_meas : MeasurableSet cubeIoc :=
    MeasurableSet.univ_pi' fun _ => measurableSet_Ioc
  have hcubeIcc_compact : IsCompact cubeIcc := isCompact_Icc
  have hcubeIoc_sub : cubeIoc ⊆ cubeIcc := fun x hx =>
    ⟨fun i => (hx i).1.le, fun i => (hx i).2⟩
  have hcubeIoc_vol : (volume : Measure (d → ℝ)) cubeIoc = 1 := by
    have : cubeIoc = Set.pi Set.univ (fun _ : d => Set.Ioc (0 : ℝ) 1) := by
      ext x; simp [cubeIoc]
    rw [this]
    simp [volume_pi, Measure.pi_pi, Real.volume_Ioc]
  have hcubeIoc_vol' : (volume : Measure (d → ℝ)).real cubeIoc = 1 := by
    simp [Measure.real, hcubeIoc_vol]

  let G : (d → ℤ) → C((d → ℝ), ℂ) := fun n => e * f.comp (ContinuousMap.addRight (intVec n))
  have hG_eq : ∀ n x, G n x = e x * f (x + intVec n) := fun n x => rfl

  have hG_intOn : ∀ n, IntegrableOn (G n) cubeIoc volume := fun n =>
    ((G n).continuous.continuousOn.integrableOn_compact hcubeIcc_compact).mono_set hcubeIoc_sub

  let hK : Compacts (d → ℝ) := ⟨cubeIcc, hcubeIcc_compact⟩
  have neK : ∀ n x, ‖G n x‖ = ‖f (x + intVec n)‖ := fun n x => by
    rw [hG_eq, norm_mul, norm_negCharCM, one_mul]
  have hG_sum_int : Summable fun n => ∫ x in cubeIoc, ‖G n x‖ := by
    refine (hf hK).of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_)
    calc ∫ x in cubeIoc, ‖G n x‖
        ≤ ∫ _ in cubeIoc, ‖(f.comp (ContinuousMap.addRight (intVec n))).restrict hK‖ := by
          refine setIntegral_mono_on (hG_intOn n).norm
            (integrableOn_const (by rw [hcubeIoc_vol]; exact ENNReal.one_ne_top))
            hcubeIoc_meas (fun x hx => ?_)
          rw [neK]
          have h := ((f.comp (ContinuousMap.addRight (intVec n))).restrict hK
            ).norm_coe_le_norm ⟨x, hcubeIoc_sub hx⟩
          simpa only [ContinuousMap.restrict_apply, ContinuousMap.comp_apply,
            ContinuousMap.coe_addRight] using h
      _ = ‖(f.comp (ContinuousMap.addRight (intVec n))).restrict hK‖ := by
          rw [setIntegral_const, hcubeIoc_vol', one_smul]

  have hef_int : Integrable (fun v => e v * f v) volume :=
    hf_int.bdd_mul (c := 1) e.continuous.aestronglyMeasurable
      (ae_of_all _ fun x => (norm_negCharCM m x).le)

  haveI : VAddInvariantMeasure ↥(span ℤ (Set.range ⇑(Pi.basisFun ℝ d))) (d → ℝ) volume :=
    inferInstanceAs (VAddInvariantMeasure
      (span ℤ (Set.range ⇑(Pi.basisFun ℝ d))).toAddSubgroup (d → ℝ) volume)
  have hFD := ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ d) (volume : Measure (d → ℝ))
  rw [ZSpan.fundamentalDomain_pi_basisFun] at hFD
  let φ : (d → ℤ) ≃ ↥(span ℤ (Set.range ⇑(Pi.basisFun ℝ d))) :=
    (((Pi.basisFun ℝ d).restrictScalars ℤ).equivFun).symm.toEquiv
  have hφ : ∀ n : d → ℤ, (↑(φ n) : d → ℝ) = intVec n := fun n =>
    coe_basisFun_equivFun_symm n

  calc UnitAddTorus.mFourierCoeff F m
      = ∫ x in cubeIoc, UnitAddTorus.mFourier (-m) (fun i => (x i : UnitAddCircle))
          • F (fun i => x i) := by
        rw [UnitAddTorus.mFourierCoeff_eq_integral F m 0]
        congr 1
        · ext x; simp [cubeIoc]
    _ = ∫ x in cubeIoc, e x * periodize (⇑f) x := by
        refine setIntegral_congr_fun hcubeIoc_meas fun x _ => ?_
        rw [smul_eq_mul, ← hF x]
        rfl
    _ = ∫ x in cubeIoc, ∑' n : d → ℤ, G n x := by
        refine setIntegral_congr_fun hcubeIoc_meas fun x _ => ?_
        simp only [hG_eq, periodize, ← tsum_mul_left]
    _ = ∑' n : d → ℤ, ∫ x in cubeIoc, G n x := by
        rw [← integral_tsum_of_summable_integral_norm hG_intOn hG_sum_int]
    _ = ∑' n : d → ℤ, ∫ x in cubeIoc, (fun v => e v * f v) (x + intVec n) := by
        refine tsum_congr fun n => setIntegral_congr_fun hcubeIoc_meas fun x _ => ?_
        rw [hG_eq, ← negCharCM_add_intVec m x n]
    _ = ∑' n : d → ℤ, ∫ x in Set.pi Set.univ (fun _ => Set.Ico (0:ℝ) 1),
          (fun v => e v * f v) (x + intVec n) := by
        exact tsum_congr fun n => setIntegral_congr_set pi_Ioc_ae_eq_pi_Ico
    _ = ∑' g : ↥(span ℤ (Set.range ⇑(Pi.basisFun ℝ d))),
          ∫ x in Set.pi Set.univ (fun _ => Set.Ico (0:ℝ) 1),
          (fun v => e v * f v) (g +ᵥ x) := by
        rw [← φ.tsum_eq]
        refine tsum_congr fun n => setIntegral_congr_fun
          (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun x _ => ?_
        congr 1
        show x + intVec n = (↑(φ n) : d → ℝ) + x
        rw [hφ, add_comm]
    _ = ∫ v, e v * f v := by
        exact (hFD.integral_eq_tsum'' (fun v => e v * f v) hef_int).symm
    _ = piFourierIntegral (⇑f) (intVec m) := by
        unfold piFourierIntegral intVec
        congr 1
        ext v
        rw [mul_comm, negCharCM_eq_fourierChar]

end FourierCoeff

private theorem isOpenQuotientMap_toUnitAddTorus :
    IsOpenQuotientMap (toUnitAddTorus (d := d)) := by
  have h : toUnitAddTorus (d := d) = Pi.map (fun _ : d => ((↑·) : ℝ → UnitAddCircle)) := by
    ext x i; rfl
  rw [h]
  exact IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk

private theorem toUnitAddTorus_surjective : Function.Surjective (toUnitAddTorus (d := d)) :=
  (isOpenQuotientMap_toUnitAddTorus (d := d)).surjective

private theorem toUnitAddTorus_eq_iff (x y : d → ℝ) :
    toUnitAddTorus x = toUnitAddTorus y ↔ ∃ n : d → ℤ, y = x + intVec n := by
  constructor
  · intro hxy
    have hcoord : ∀ i, ∃ k : ℤ, y i - x i = k := fun i => by
      have hi0 : (y i : AddCircle (1:ℝ)) - (x i : AddCircle (1:ℝ)) = 0 :=
        sub_eq_zero.mpr (congrFun hxy i).symm
      have hi : ((y i - x i : ℝ) : AddCircle (1:ℝ)) = 0 := by
        rwa [AddCircle.coe_sub]
      obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff 1).mp hi
      exact ⟨k, by rw [← hk]; simp⟩
    refine ⟨fun i => (hcoord i).choose, ?_⟩
    ext i
    have := (hcoord i).choose_spec
    simp only [intVec, Pi.add_apply]
    linarith [this]
  · rintro ⟨n, rfl⟩
    exact (toUnitAddTorus_add_intVec x n).symm

private theorem periodize_eq_of_toUnitAddTorus_eq (f : (d → ℝ) → ℂ) {x y : d → ℝ}
    (hxy : toUnitAddTorus x = toUnitAddTorus y) :
    periodize f x = periodize f y := by
  obtain ⟨n, rfl⟩ := (toUnitAddTorus_eq_iff x y).mp hxy
  exact (periodize_add_intVec f x n).symm

section PeriodizeLift

set_option maxHeartbeats 16000000

private def periodizeCM (f : C((d → ℝ), ℂ))
    (hf : ∀ K : Compacts (d → ℝ),
      Summable fun n : d → ℤ => ‖(f.comp (ContinuousMap.addRight (intVec n))).restrict K‖) :
    C((d → ℝ), ℂ) :=
  ∑' n : d → ℤ, f.comp (ContinuousMap.addRight (intVec n))

private theorem periodizeCM_apply (f : C((d → ℝ), ℂ))
    (hf : ∀ K : Compacts (d → ℝ),
      Summable fun n : d → ℤ => ‖(f.comp (ContinuousMap.addRight (intVec n))).restrict K‖)
    (x : d → ℝ) :
    periodizeCM f hf x = periodize (⇑f) x := by
  have hsum : Summable (fun n : d → ℤ => f.comp (ContinuousMap.addRight (intVec n))) :=
    ContinuousMap.summable_of_locally_summable_norm hf
  unfold periodizeCM periodize
  rw [← ContinuousMap.tsum_apply hsum x]
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_addRight]

private def periodizeLiftFun (f : C((d → ℝ), ℂ))
    (hf : ∀ K : Compacts (d → ℝ),
      Summable fun n : d → ℤ => ‖(f.comp (ContinuousMap.addRight (intVec n))).restrict K‖) :
    UnitAddTorus d → ℂ :=
  fun z => periodizeCM f hf (Function.surjInv toUnitAddTorus_surjective z)

private theorem periodizeLiftFun_toUnitAddTorus (f : C((d → ℝ), ℂ))
    (hf : ∀ K : Compacts (d → ℝ),
      Summable fun n : d → ℤ => ‖(f.comp (ContinuousMap.addRight (intVec n))).restrict K‖)
    (x : d → ℝ) :
    periodizeLiftFun f hf (toUnitAddTorus x) = periodize (⇑f) x := by
  have hfib : toUnitAddTorus (Function.surjInv toUnitAddTorus_surjective
      (toUnitAddTorus (d := d) x)) = toUnitAddTorus x :=
    Function.surjInv_eq toUnitAddTorus_surjective (toUnitAddTorus x)
  calc periodizeLiftFun f hf (toUnitAddTorus x)
      = periodizeCM f hf (Function.surjInv toUnitAddTorus_surjective (toUnitAddTorus x)) := rfl
    _ = periodize (⇑f) (Function.surjInv toUnitAddTorus_surjective (toUnitAddTorus x)) :=
        periodizeCM_apply f hf _
    _ = periodize (⇑f) x := periodize_eq_of_toUnitAddTorus_eq (⇑f) hfib

private def periodizeLift (f : C((d → ℝ), ℂ))
    (hf : ∀ K : Compacts (d → ℝ),
      Summable fun n : d → ℤ => ‖(f.comp (ContinuousMap.addRight (intVec n))).restrict K‖) :
    C(UnitAddTorus d, ℂ) where
  toFun := periodizeLiftFun f hf
  continuous_toFun := by
    rw [(isOpenQuotientMap_toUnitAddTorus (d := d)).isQuotientMap.continuous_iff]
    have hcomp : periodizeLiftFun f hf ∘ toUnitAddTorus = ⇑(periodizeCM f hf) := by
      ext x
      rw [Function.comp_apply, periodizeLiftFun_toUnitAddTorus f hf x, periodizeCM_apply f hf]
    rw [hcomp]
    exact (periodizeCM f hf).continuous

private theorem periodizeLift_toUnitAddTorus (f : C((d → ℝ), ℂ))
    (hf : ∀ K : Compacts (d → ℝ),
      Summable fun n : d → ℤ => ‖(f.comp (ContinuousMap.addRight (intVec n))).restrict K‖)
    (x : d → ℝ) :
    periodizeLift f hf (toUnitAddTorus x) = periodize (⇑f) x :=
  periodizeLiftFun_toUnitAddTorus f hf x

end PeriodizeLift

private theorem periodize_eq_tsum_piFourierIntegral (f : C((d → ℝ), ℂ))
    (hf : ∀ K : Compacts (d → ℝ),
      Summable fun n : d → ℤ => ‖(f.comp (ContinuousMap.addRight (intVec n))).restrict K‖)
    (hf_int : Integrable (⇑f) (volume : Measure (d → ℝ)))
    (hFf : Summable fun m : d → ℤ => piFourierIntegral f (intVec m))
    (x : d → ℝ) :
    periodize f x
      = ∑' m : d → ℤ, piFourierIntegral f (intVec m)
          * UnitAddTorus.mFourier m (toUnitAddTorus x) := by
  set F := periodizeLift f hf
  rw [← periodizeLift_toUnitAddTorus f hf x]
  have hcoeff : ∀ m, UnitAddTorus.mFourierCoeff F m = piFourierIntegral f (intVec m) :=
    mFourierCoeff_eq_piFourierIntegral f hf hf_int F (periodizeLift_toUnitAddTorus f hf)
  have hsum : Summable (UnitAddTorus.mFourierCoeff F) := by
    refine hFf.congr fun m => ?_
    exact (hcoeff m).symm
  have := (UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsum
    (toUnitAddTorus x)).tsum_eq
  rw [← this]
  refine tsum_congr fun m => ?_
  rw [hcoeff m, smul_eq_mul]

section Schwartz

private theorem finrank_span_basisFun :
    Module.finrank ℤ (span ℤ (Set.range (Pi.basisFun ℝ d)) : Submodule ℤ (d → ℝ))
      = Fintype.card d :=
  Module.finrank_eq_card_basis ((Pi.basisFun ℝ d).restrictScalars ℤ)

private theorem summable_norm_intVec_inv_pow {N : ℕ} (hN : Fintype.card d < N) :
    Summable fun n : d → ℤ => ‖intVec (d := d) n‖⁻¹ ^ N := by
  have hfin : Module.finrank ℤ
      (span ℤ (Set.range (Pi.basisFun ℝ d)) : Submodule ℤ (d → ℝ)) < N := by
    rw [finrank_span_basisFun]; exact hN
  have hL : Summable fun z : span ℤ (Set.range (Pi.basisFun ℝ d)) => ‖(z : d → ℝ)‖⁻¹ ^ N :=
    ZLattice.summable_norm_pow_inv (span ℤ (Set.range (Pi.basisFun ℝ d))) N hfin
  have := ((((Pi.basisFun ℝ d).restrictScalars ℤ).equivFun.toEquiv.symm.summable_iff
    (f := fun z : span ℤ (Set.range (Pi.basisFun ℝ d)) => ‖(z : d → ℝ)‖⁻¹ ^ N))).mpr hL
  refine this.congr fun n => ?_
  simp only [Function.comp_apply, LinearEquiv.coe_toEquiv_symm]
  congr 2
  exact congrArg norm (coe_basisFun_equivFun_symm n)

private theorem summable_norm_schwartz_intVec (g : SchwartzMap (d → ℝ) ℂ) :
    Summable fun n : d → ℤ => ‖(g : (d → ℝ) → ℂ) (intVec n)‖ := by
  set N := Fintype.card d + 1
  have hsum := summable_norm_intVec_inv_pow (d := d) (N := N) (Nat.lt_succ_self _)
  refine Summable.of_norm_bounded_eventually
    (g := fun n : d → ℤ => SchwartzMap.seminorm ℝ N 0 g * ‖intVec (d := d) n‖⁻¹ ^ N)
    (hsum.mul_left _) ?_
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset (s := {(0 : d → ℤ)}) (Set.finite_singleton _) ?_
  intro n hn
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hn ⊢
  by_contra hne
  apply hn
  have hne0 : intVec (d := d) n ≠ 0 := by
    intro h; apply hne; ext i
    have := congrFun h i
    simpa [intVec] using this
  have hpos : (0 : ℝ) < ‖intVec (d := d) n‖ ^ N := pow_pos (norm_pos_iff.mpr hne0) _
  have hdecay := SchwartzMap.norm_pow_mul_le_seminorm ℝ g N (intVec n)
  rw [norm_norm, inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
  exact hdecay

private theorem one_add_norm_intVec_le {R : ℝ} (hR : 0 ≤ R) {x : d → ℝ}
    (hx : x ∈ Metric.closedBall (0 : d → ℝ) R) (n : d → ℤ) :
    1 + ‖intVec (d := d) n‖ ≤ (1 + R) * (1 + ‖x + intVec n‖) := by
  have hxR : ‖x‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
  have h1 : ‖intVec (d := d) n‖ ≤ ‖x‖ + ‖x + intVec n‖ := by
    calc ‖intVec (d := d) n‖ = ‖x + intVec n - x‖ := by ring_nf
      _ ≤ ‖x + intVec n‖ + ‖x‖ := norm_sub_le _ _
      _ = ‖x‖ + ‖x + intVec n‖ := add_comm _ _
  calc 1 + ‖intVec (d := d) n‖
      ≤ 1 + (R + ‖x + intVec n‖) := by linarith [h1, hxR]
    _ ≤ (1 + R) * (1 + ‖x + intVec n‖) := by
        have h2 : 0 ≤ ‖x + intVec (d := d) n‖ := norm_nonneg _
        nlinarith

private theorem summable_one_add_norm_intVec_inv_pow {N : ℕ} (hN : Fintype.card d < N) :
    Summable fun n : d → ℤ => (1 + ‖intVec (d := d) n‖)⁻¹ ^ N := by
  have hsum := summable_norm_intVec_inv_pow (d := d) hN
  refine Summable.of_norm_bounded_eventually (g := fun n => ‖intVec (d := d) n‖⁻¹ ^ N) hsum ?_
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset (s := {(0 : d → ℤ)}) (Set.finite_singleton _) ?_
  intro n hn
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hn ⊢
  by_contra hne
  apply hn
  have hne0 : intVec (d := d) n ≠ 0 := by
    intro h; apply hne; ext i
    have := congrFun h i
    simpa [intVec] using this
  have h1 : (1 + ‖intVec (d := d) n‖)⁻¹ ^ N ≤ ‖intVec (d := d) n‖⁻¹ ^ N := by
    apply pow_le_pow_left₀ (by positivity)
    exact inv_anti₀ (norm_pos_iff.mpr hne0) (by linarith [norm_nonneg (intVec (d := d) n)])
  rw [Real.norm_of_nonneg (by positivity)]
  exact h1

private theorem summable_norm_restrict_schwartz_comp_addRight
    (h : SchwartzMap (d → ℝ) ℂ) (K : Compacts (d → ℝ)) :
    Summable fun n : d → ℤ =>
      ‖(h.toContinuousMap.comp (ContinuousMap.addRight (intVec n))).restrict K‖ := by
  classical
  set N := Fintype.card d + 1
  set C := (2:ℝ)^N * (Finset.Iic (N, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) h
    with hC_def
  have hC_nonneg : 0 ≤ C := mul_nonneg (by positivity) (apply_nonneg _ _)
  have hKbdd : Bornology.IsBounded (K : Set (d → ℝ)) := K.2.isBounded
  obtain ⟨R, hR_nonneg, hKR⟩ : ∃ R ≥ 0, (K : Set (d → ℝ)) ⊆ Metric.closedBall 0 R := by
    obtain ⟨R, hKR⟩ := hKbdd.subset_closedBall 0
    exact ⟨max R 0, le_max_right _ _,
      hKR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩
  have hsum := summable_one_add_norm_intVec_inv_pow (d := d) (N := N) (Nat.lt_succ_self _)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (hsum.mul_left (C * (1 + R)^N))
  have hbound : ∀ x ∈ (K : Set (d → ℝ)),
      ‖h (x + intVec n)‖ ≤ C * (1 + R)^N * (1 + ‖intVec (d := d) n‖)⁻¹ ^ N := by
    intro x hxK
    have hxR := hKR hxK
    have hdecay := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, 0))
      (k := N) (n := 0) le_rfl le_rfl h (x + intVec n)
    rw [norm_iteratedFDeriv_zero] at hdecay
    have huni := one_add_norm_intVec_le hR_nonneg hxR n
    have hpos : (0:ℝ) < (1 + ‖x + intVec (d := d) n‖)^N := pow_pos (by positivity) _
    have hpos' : (0:ℝ) < (1 + ‖intVec (d := d) n‖)^N := pow_pos (by positivity) _
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpos']
    calc ‖h (x + intVec n)‖ * (1 + ‖intVec (d := d) n‖) ^ N
        ≤ ‖h (x + intVec n)‖ * ((1 + R) * (1 + ‖x + intVec n‖)) ^ N := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact pow_le_pow_left₀ (by positivity) huni N
      _ = (1 + R)^N * (‖h (x + intVec n)‖ * (1 + ‖x + intVec n‖) ^ N) := by
          rw [mul_pow]; ring
      _ ≤ (1 + R)^N * C := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [mul_comm]
          exact hdecay
      _ = C * (1 + R)^N := mul_comm _ _
  refine (ContinuousMap.norm_le _ ?_).mpr ?_
  · exact mul_nonneg (mul_nonneg hC_nonneg (by positivity)) (by positivity)
  · rintro ⟨x, hxK⟩
    simp only [ContinuousMap.restrict_apply, ContinuousMap.comp_apply,
      ContinuousMap.coe_addRight]
    exact hbound x hxK

private abbrev euclideanToPi : EuclideanSpace ℝ d ≃L[ℝ] (d → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : d => ℝ)

private theorem piFourierIntegral_eq_fourier_euclidean (h : SchwartzMap (d → ℝ) ℂ) (ξ : d → ℝ) :
    piFourierIntegral (⇑h) ξ
      = (𝓕 (⇑(SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (euclideanToPi (d := d)) h)
            : EuclideanSpace ℝ d → ℂ)) (toLp 2 ξ) := by
  unfold piFourierIntegral
  rw [Real.fourier_eq]
  rw [← MeasurePreserving.integral_comp (PiLp.volume_preserving_ofLp d)
    (MeasurableEquiv.toLp 2 (d → ℝ)).symm.measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    Circle.smul_def, smul_eq_mul]
  have hinner : ∑ i, (ofLp v) i * ξ i = ⟪v, toLp 2 ξ⟫_ℝ := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  rw [← hinner, mul_comm]
  rfl

private theorem summable_piFourierIntegral_schwartz_intVec (h : SchwartzMap (d → ℝ) ℂ) :
    Summable fun m : d → ℤ => piFourierIntegral (⇑h) (intVec m) := by
  let h' : SchwartzMap (EuclideanSpace ℝ d) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (euclideanToPi (d := d)) h
  let g' : SchwartzMap (EuclideanSpace ℝ d) ℂ := 𝓕 h'
  let g : SchwartzMap (d → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (euclideanToPi (d := d)).symm g'
  have hg : ∀ ξ : d → ℝ, piFourierIntegral (⇑h) ξ = g ξ := fun ξ => by
    rw [piFourierIntegral_eq_fourier_euclidean h ξ]
    simp only [g, g', h', SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
    rfl
  simp_rw [hg]
  exact (summable_norm_schwartz_intVec g).of_norm

private theorem SchwartzMap.tsum_add_intVec_eq_tsum_piFourierIntegral
    (h : SchwartzMap (d → ℝ) ℂ) (x : d → ℝ) :
    ∑' n : d → ℤ, h (x + intVec n)
      = ∑' m : d → ℤ, piFourierIntegral h (intVec m) * (𝐞 (∑ i, (m i : ℝ) * x i) : ℂ) := by
  have := PiPoissonSummation.periodize_eq_tsum_piFourierIntegral h.toContinuousMap
    (summable_norm_restrict_schwartz_comp_addRight h) h.integrable
    (summable_piFourierIntegral_schwartz_intVec h) x
  simp only [periodize, mFourier_toUnitAddTorus] at this ⊢
  exact this

private theorem SchwartzMap.tsum_intVec_eq_tsum_piFourierIntegral (h : SchwartzMap (d → ℝ) ℂ) :
    ∑' n : d → ℤ, h (intVec n) = ∑' m : d → ℤ, piFourierIntegral h (intVec m) := by
  have := PiPoissonSummation.SchwartzMap.tsum_add_intVec_eq_tsum_piFourierIntegral h 0
  simpa using this

end Schwartz

end PiPoissonSummation

end

section Euclidean
open PiPoissonSummation

/-- Poisson summation for a Schwartz function on a finite-dimensional
Euclidean space: summing `f` over the integer lattice translates of `x`
equals summing the Fourier transform of `f` over the lattice, weighted by
the character `𝐞 ⟪n, x⟫`. This is the multi-dimensional analogue of the
one-dimensional `SchwartzMap.tsum_eq_tsum_fourier` in Mathlib. -/
public theorem SchwartzMap.tsum_eq_tsum_fourier_euclideanSpace
    {ι : Type*} [Fintype ι] (f : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (x : EuclideanSpace ℝ ι) :
    ∑' n : ι → ℤ, f (x + WithLp.toLp 2 (fun i ↦ (n i : ℝ))) =
      ∑' n : ι → ℤ, 𝓕 f (WithLp.toLp 2 (fun i ↦ (n i : ℝ))) *
        (𝐞 ⟪(WithLp.toLp 2 (fun i ↦ (n i : ℝ)) : EuclideanSpace ℝ ι), x⟫_ℝ : ℂ) := by
  set h : SchwartzMap (ι → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (euclideanToPi (d := ι)).symm f with hh
  have hh_apply : ∀ v : ι → ℝ, h v = f (WithLp.toLp 2 v) := fun v => by
    simp only [hh, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
    rfl
  have hback : SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (euclideanToPi (d := ι)) h = f := by
    ext v
    simp only [hh, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
    rfl
  have key := PiPoissonSummation.SchwartzMap.tsum_add_intVec_eq_tsum_piFourierIntegral
    h (WithLp.ofLp x)
  have hL : ∀ n : ι → ℤ, h (ofLp x + intVec n) = f (x + WithLp.toLp 2 (fun i ↦ (n i : ℝ))) := by
    intro n
    rw [hh_apply, WithLp.toLp_add, WithLp.toLp_ofLp]
    rfl
  have hR : ∀ m : ι → ℤ, piFourierIntegral (⇑h) (intVec m)
      = 𝓕 f (WithLp.toLp 2 (fun i ↦ (m i : ℝ))) := by
    intro m
    rw [piFourierIntegral_eq_fourier_euclidean h (intVec m), hback]
    rfl
  have hχ : ∀ m : ι → ℤ, (𝐞 (∑ i, (m i : ℝ) * (WithLp.ofLp x) i) : ℂ)
      = (𝐞 ⟪(WithLp.toLp 2 (fun i ↦ (m i : ℝ)) : EuclideanSpace ℝ ι), x⟫_ℝ : ℂ) := by
    intro m
    congr 2
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  simp only [hL, hR, hχ] at key
  exact key

end Euclidean
