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

public import MathlibExt.Analysis.InnerProductSpace.Group.HaarL2.RadonProduct
public import MathlibExt.MeasureTheory.Function.L2Space.TensorProduct
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Actual compact-support Lp-valued sections of the Borel product

A continuous compact-support product function determines its actual scalar
L2 section in the second coordinate. Uniform compact support makes the
section map continuous in the original Lp norm without countability or
sigma-finiteness. The resulting compact-support Hilbert-valued function has
the exact original iterated square integral. The existing one-measure tensor
unitary then gives a literal full factor-tensor representative of equal norm.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set
open scoped CompactlySupported TensorProduct Topology

noncomputable section

universe uX uY

namespace CompactlySupportedContinuousMap

section Sections

variable {X : Type uX} [TopologicalSpace X]
variable {Y : Type uY} [TopologicalSpace Y] [T2Space Y]

/-- The literal compact-support complex section in the original second coordinate. -/
def sectionRightComplex (F : C_c(X × Y, ℂ)) (x : X) : C_c(Y, ℂ) where
  toFun y := F (x, y)
  continuous_toFun := F.continuous.comp (continuous_const.prodMk continuous_id)
  hasCompactSupport' := by
    apply HasCompactSupport.intro (F.hasCompactSupport.image continuous_snd)
    intro y hy
    exact image_eq_zero_of_notMem_tsupport (fun hxy => hy ⟨(x, y), hxy, rfl⟩)

/-- The complex section retains each original pointwise value. -/
@[simp]
theorem sectionRightComplex_apply (F : C_c(X × Y, ℂ)) (x : X) (y : Y) :
    sectionRightComplex F x y = F (x, y) := rfl

variable [MeasurableSpace Y] [BorelSpace Y] (ν : Measure Y) [ν.Regular]

/-- The actual original L2 vector of a compact-support section. -/
def sectionRightLp (F : C_c(X × Y, ℂ)) (x : X) : Lp ℂ 2 ν :=
  HaarL2.compactSupportInclusion ν (sectionRightComplex F x)

/-- Every section has its original pointwise values almost everywhere. -/
theorem sectionRightLp_ae_eq (F : C_c(X × Y, ℂ)) (x : X) :
    sectionRightLp ν F x =ᵐ[ν] fun y => F (x, y) :=
  HaarL2.compactSupportInclusion_ae_eq ν (sectionRightComplex F x)

/-- The section's squared L2 norm is its actual original square integral. -/
theorem norm_sectionRightLp_sq (F : C_c(X × Y, ℂ)) (x : X) :
    ‖sectionRightLp ν F x‖ ^ 2 = ∫ y : Y, ‖F (x, y)‖ ^ 2 ∂ν :=
  HaarL2.norm_compactSupportInclusion_sq ν (sectionRightComplex F x)

/-- Differences of sections have the actual integral squared-distance norm. -/
theorem norm_sectionRightLp_sub_sq (F : C_c(X × Y, ℂ)) (x x' : X) :
    ‖sectionRightLp ν F x - sectionRightLp ν F x'‖ ^ 2 =
      ∫ y : Y, ‖F (x, y) - F (x', y)‖ ^ 2 ∂ν := by
  change ‖HaarL2.compactSupportInclusion ν (sectionRightComplex F x) -
    HaarL2.compactSupportInclusion ν (sectionRightComplex F x')‖ ^ 2 = _
  rw [← map_sub, HaarL2.norm_compactSupportInclusion_sq]
  simp only [CompactlySupportedContinuousMap.sub_apply, sectionRightComplex_apply]

/-- Uniform compact support makes the actual Lp-valued section map norm-continuous. -/
theorem continuous_sectionRightLp (F : C_c(X × Y, ℂ)) : Continuous (sectionRightLp ν F) := by
  apply continuous_iff_continuousAt.mpr
  intro x₀
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hI : Continuous (fun x : X => ∫ y : Y, ‖F (x, y) - F (x₀, y)‖ ^ 2 ∂ν) := by
    apply continuousOn_univ.mp
    apply continuousOn_integral_of_compact_support (F.hasCompactSupport.image continuous_snd)
    · rw [univ_prod_univ]
      have hanchor : Continuous (fun _ : X × Y => x₀) := continuous_const
      refine ((F.continuous.sub (F.continuous.comp
        (hanchor.prodMk continuous_snd))).norm.pow 2).continuousOn.congr ?_
      rintro ⟨x, y⟩ _
      rfl
    · intro x y _ hy
      have hx : F (x, y) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hxy => hy ⟨(x, y), hxy, rfl⟩)
      have hx₀ : F (x₀, y) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hxy => hy ⟨(x₀, y), hxy, rfl⟩)
      simp only [hx, hx₀, sub_self, norm_zero, zero_pow two_ne_zero]
  have hN : Continuous (fun x : X => ‖sectionRightLp ν F x - sectionRightLp ν F x₀‖) := by
    have hEq : (fun x : X => ‖sectionRightLp ν F x - sectionRightLp ν F x₀‖) =
        fun x : X => Real.sqrt (∫ y : Y, ‖F (x, y) - F (x₀, y)‖ ^ 2 ∂ν) := by
      funext x
      rw [← norm_sectionRightLp_sub_sq,
        Real.sqrt_sq (norm_nonneg (sectionRightLp ν F x - sectionRightLp ν F x₀))]
    rw [hEq]
    exact Real.continuous_sqrt.comp hI
  simpa only [sub_self, norm_zero] using (hN.continuousAt (x := x₀)).tendsto

variable [T2Space X]

/-- The actual section map as an original compact-support Hilbert-valued function. -/
def sectionToLp (F : C_c(X × Y, ℂ)) : C_c(X, Lp ℂ 2 ν) where
  toFun := sectionRightLp ν F
  continuous_toFun := continuous_sectionRightLp ν F
  hasCompactSupport' := by
    apply HasCompactSupport.intro (F.hasCompactSupport.image continuous_fst)
    intro x hx
    have hzero : sectionRightComplex F x = 0 := by
      apply CompactlySupportedContinuousMap.ext
      intro y
      change F (x, y) = 0
      exact image_eq_zero_of_notMem_tsupport (fun hxy => hx ⟨(x, y), hxy, rfl⟩)
    change HaarL2.compactSupportInclusion ν (sectionRightComplex F x) = 0
    rw [hzero, map_zero]

/-- The compact-support section constructor retains its computed Lp section at every point. -/
@[simp]
theorem sectionToLp_apply (F : C_c(X × Y, ℂ)) (x : X) :
    sectionToLp ν F x = sectionRightLp ν F x := rfl

/-- The actual compact-support section construction is complex linear. -/
def sectionToLpLinearMap : C_c(X × Y, ℂ) →ₗ[ℂ] C_c(X, Lp ℂ 2 ν) where
  toFun := sectionToLp ν
  map_add' F G := CompactlySupportedContinuousMap.ext (fun x => by
    change HaarL2.compactSupportInclusion ν (sectionRightComplex (F + G) x) =
      HaarL2.compactSupportInclusion ν (sectionRightComplex F x) +
        HaarL2.compactSupportInclusion ν (sectionRightComplex G x)
    have hsection : sectionRightComplex (F + G) x =
        sectionRightComplex F x + sectionRightComplex G x := by
      apply CompactlySupportedContinuousMap.ext
      intro y
      rfl
    rw [hsection, map_add])
  map_smul' c F := CompactlySupportedContinuousMap.ext (fun x => by
    change HaarL2.compactSupportInclusion ν (sectionRightComplex (c • F) x) =
      c • HaarL2.compactSupportInclusion ν (sectionRightComplex F x)
    have hsection : sectionRightComplex (c • F) x = c • sectionRightComplex F x := by
      apply CompactlySupportedContinuousMap.ext
      intro y
      rfl
    rw [hsection, map_smul])

/-- A pure compact-support product has the original scalar-times-vector section. -/
theorem sectionRightLp_mulProd (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) (x : X) :
    sectionRightLp ν (mulProd f g) x = f x • HaarL2.compactSupportInclusion ν g := by
  change HaarL2.compactSupportInclusion ν (sectionRightComplex (mulProd f g) x) =
    f x • HaarL2.compactSupportInclusion ν g
  rw [← map_smul]
  congr 1

end Sections

end CompactlySupportedContinuousMap

namespace MeasureTheory.HaarL2

open CompactlySupportedContinuousMap

variable {X : Type uX} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable {Y : Type uY} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]
variable (μ : Measure X) (ν : Measure Y) [μ.Regular] [ν.Regular]

/-- The Borel measurable space of the literal product used by the section square-integral comparison. -/
local instance instSectionsProductBorelMeasurableSpace : MeasurableSpace (X × Y) := borel (X × Y)
local instance instSectionsProductBorelSpace : BorelSpace (X × Y) := ⟨rfl⟩

/-- The original Hilbert-valued L2 inclusion of the actual compact-support Lp-valued sections. -/
def productToIteratedLp : C_c(X × Y, ℂ) →ₗ[ℂ] Lp (Lp ℂ 2 ν) 2 μ :=
  (compactSupportInclusion (H := Lp ℂ 2 ν) μ).comp (sectionToLpLinearMap ν)

omit [LocallyCompactSpace X] [LocallyCompactSpace Y] in
/-- The iterated L2 construction has the original section values almost everywhere. -/
theorem productToIteratedLp_ae_eq (F : C_c(X × Y, ℂ)) :
    productToIteratedLp μ ν F =ᵐ[μ] sectionRightLp ν F := by
  change compactSupportInclusion (H := Lp ℂ 2 ν) μ (sectionToLp ν F) =ᵐ[μ] sectionRightLp ν F
  filter_upwards [compactSupportInclusion_ae_eq (H := Lp ℂ 2 ν) μ (sectionToLp ν F)] with x hx
  simpa only [sectionToLp_apply] using hx

/-- The actual iterated section L2 norm has the original Borel product square integral. -/
theorem norm_productToIteratedLp_sq (F : C_c(X × Y, ℂ)) :
    ‖productToIteratedLp μ ν F‖ ^ 2 = ‖compactSupportInclusion (Measure.radonProd μ ν) F‖ ^ 2 := by
  change ‖compactSupportInclusion μ (sectionToLp ν F)‖ ^ 2 = _
  rw [norm_compactSupportInclusion_sq, norm_compactSupportInclusion_sq]
  calc
    (∫ x : X, ‖sectionToLp ν F x‖ ^ 2 ∂μ) = ∫ x : X, ∫ y : Y, ‖F (x, y)‖ ^ 2 ∂ν ∂μ :=
      integral_congr_ae (Eventually.of_forall fun x => norm_sectionRightLp_sq ν F x)
    _ = ∫ z : X × Y, ‖F z‖ ^ 2 ∂(Measure.radonProd μ ν) := by
      simpa only [CompactlySupportedContinuousMap.normSq_apply] using
        (Measure.integral_radonProd μ ν (normSq F)).symm

/-- The actual full factor-tensor vector supplied by the proved one-measure Hilbert-valued tensor unitary. -/
def compactProductTensorRepresentative :
    C_c(X × Y, ℂ) →ₗ[ℂ] UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) :=
  (L2.tensorToLp (𝕜 := ℂ) (H := Lp ℂ 2 ν) μ).symm.toLinearMap.comp (productToIteratedLp μ ν)

/-- The full factor-tensor representative has the exact original product L2 squared norm. -/
theorem norm_compactProductTensorRepresentative_sq (F : C_c(X × Y, ℂ)) :
    ‖compactProductTensorRepresentative μ ν F‖ ^ 2 =
      ‖compactSupportInclusion (Measure.radonProd μ ν) F‖ ^ 2 := by
  change ‖(L2.tensorToLp (𝕜 := ℂ) (H := Lp ℂ 2 ν) μ).symm (productToIteratedLp μ ν F)‖ ^ 2 = _
  rw [LinearIsometryEquiv.norm_map]
  exact norm_productToIteratedLp_sq μ ν F

/-- The full factor-tensor representative preserves the original product L2 norm. -/
theorem norm_compactProductTensorRepresentative (F : C_c(X × Y, ℂ)) :
    ‖compactProductTensorRepresentative μ ν F‖ =
      ‖compactSupportInclusion (Measure.radonProd μ ν) F‖ := by
  simpa only [Real.sqrt_sq (norm_nonneg (compactProductTensorRepresentative μ ν F)),
    Real.sqrt_sq (norm_nonneg (compactSupportInclusion (Measure.radonProd μ ν) F))] using
    congrArg Real.sqrt (norm_compactProductTensorRepresentative_sq μ ν F)

end MeasureTheory.HaarL2

end
