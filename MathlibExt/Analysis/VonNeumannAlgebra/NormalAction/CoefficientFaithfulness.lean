/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalAction.TensorCoefficient
public import MathlibExt.Analysis.VonNeumannAlgebra.NormalAction.CoefficientNormality
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Faithfulness of the original Haar coefficient representation

The actual indicator of a measurable finite-Haar neighborhood, multiplied by
an original Hilbert vector, is an actual Lp H 2 vector. If an original coefficient
operator vanishes, its exact a.e. formula makes the continuous inverse-action
vector orbit vanish on that open neighborhood. Haar full support promotes the
a.e. equality to the original pointwise equality, including at the identity.

This supplies injectivity needed by the original normal faithful coefficient
inclusion and source crossed-product constructor. The exact H-first tensor
coefficient inherits it through the already proved original unitary coordinates.
Normality and membership in the spatial ambient remain separate prerequisites.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter
open scoped ENNReal Topology TensorProduct InnerProductSpace CStarAlgebra

namespace VonNeumannAlgebra.NormalAction

noncomputable section

universe uG uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-- The actual original regular coefficient star representation on Haar Lp is injective. -/
theorem regularCoefficient_injective (α : NormalAction G M) :
    Function.Injective (regularCoefficientHom μ α) := by
  classical
  have hzero (x : M) (hx : regularCoefficientHom μ α x = 0) : x = 0 := by
    change regularCoefficient μ α x = 0 at hx
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    change (x : H →L[ℂ] H) v = 0
    obtain ⟨V, hVone, hVopen, hVfinite⟩ := μ.exists_isOpen_measure_lt_top (1 : G)
    have hVmeas : MeasurableSet V := hVopen.measurableSet
    have hMem : MemLp (V.indicator fun _ : G => v) 2 μ :=
      memLp_indicator_const 2 hVmeas.nullMeasurableSet v (Or.inr hVfinite.ne)
    let ξ : Lp H 2 μ := hMem.toLp (V.indicator fun _ : G => v)
    have hξ : (ξ : G → H) =ᵐ[μ] V.indicator (fun _ : G => v) := hMem.coeFn_toLp
    let F : G → H := fun s => (α s⁻¹ x : H →L[ℂ] H) v
    have hF : Continuous F := (continuous_vector_apply α x v).comp continuous_inv
    have hCoeff := regularCoefficient_ae_eq μ α x ξ
    rw [hx] at hCoeff
    have hAE : ∀ᵐ s ∂μ, s ∈ V → F s = 0 := by
      filter_upwards [hCoeff, hξ, Lp.coeFn_zero H 2 μ] with s hsCoeff hsξ hsZero
      intro hsV
      have hξv : ξ s = v := by
        rw [hsξ]
        exact Set.indicator_of_mem hsV (fun _ : G => v)
      change (α s⁻¹ x : H →L[ℂ] H) v = 0
      exact (congrArg (fun w : H => (α s⁻¹ x : H →L[ℂ] H) w) hξv).symm.trans
        (hsCoeff.symm.trans hsZero)
    have hAEV : F =ᵐ[μ.restrict V] (fun _ : G => (0 : H)) :=
      (ae_restrict_iff' hVmeas).2 hAE
    have hZeroContinuous : Continuous (fun _ : G => (0 : H)) := continuous_const
    have hEq := Measure.eqOn_open_of_ae_eq (μ := μ) hAEV hVopen
      hF.continuousOn hZeroContinuous.continuousOn
    have hOne : F (1 : G) = 0 := hEq hVone
    have hFone : F (1 : G) = (x : H →L[ℂ] H) v := by
      dsimp only [F]
      simp only [inv_one, map_one, NormalStarAlgEquiv.one_apply]
    exact hFone.symm.trans hOne
  intro x y hxy
  have hmap : regularCoefficientHom μ α (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (hzero (x - y) hmap)

/-- The exact original H-first tensor coefficient representation is injective through the verified coordinates. -/
theorem regularCoefficientTensor_injective (α : NormalAction G M) :
    Function.Injective (regularCoefficientTensorHom μ α) := by
  let Φ := L2.tensorToLpRight (𝕜 := ℂ) (H := H) μ
  intro x y hxy
  apply regularCoefficient_injective μ α
  have hConj : Φ.symm.conjStarAlgEquiv (regularCoefficientHom μ α x) =
      Φ.symm.conjStarAlgEquiv (regularCoefficientHom μ α y) := hxy
  exact Φ.symm.conjStarAlgEquiv.injective hConj

/-- The literal original spatial normal coefficient homomorphism is faithful. -/
theorem regularCoefficientSpatialNormalHom_injective (α : NormalAction G M) :
    Function.Injective (regularCoefficientSpatialNormalHom μ α) := by
  intro x y hxy
  apply regularCoefficientTensor_injective μ α
  exact congrArg (fun z : spatialTensorProduct M (⊤ : VonNeumannAlgebra (Lp ℂ 2 μ)) =>
    (z : UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
      UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)))) hxy

end

end VonNeumannAlgebra.NormalAction
