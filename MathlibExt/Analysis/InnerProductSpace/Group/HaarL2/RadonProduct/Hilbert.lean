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

public import MathlibExt.Analysis.InnerProductSpace.Group.HaarL2.RadonProduct.Unitary
public import MathlibExt.Analysis.InnerProductSpace.Group.HaarL2.TensorProduct

/-!
# The actual scalar product tensor amplified by a Hilbert space

Tensor congruence amplifies the verified original scalar Radon product unitary
by the identity on H. Its actual forward and inverse completion maps give an
isometry equivalence, and the existing one-measure tensor-to-Lp comparison
then gives the full H-valued Borel Radon Lp space. H may be zero.

The source-side mapped model is the stock completion of the original full
scalar factor tensor tensored with H. No product unitary, norm certificate,
countability or s-finiteness assumption is supplied as an input.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory
open scoped CompactlySupported TensorProduct InnerProductSpace

namespace MeasureTheory.HaarL2

noncomputable section

universe uX uY uH

variable {X : Type uX} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable {Y : Type uY} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]
variable (μ : Measure X) (ν : Measure Y) [μ.Regular] [ν.Regular]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual Borel measurable space of the original topological product. -/
local instance instHilbertProductBorelMeasurableSpace : MeasurableSpace (X × Y) := borel (X × Y)
local instance instHilbertProductBorelSpace : BorelSpace (X × Y) := ⟨rfl⟩

/-- The original full scalar factor tensor, amplified by H, is actual H-valued product Lp. -/
def radonProductTensorHilbertUnitary :
    UniformSpace.Completion
      ((UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) ⊗[ℂ] H) ≃ₗᵢ[ℂ]
      Lp H 2 (Measure.radonProd μ ν) := by
  let e := TensorProduct.congrIsometry (radonProductTensorUnitary μ ν) (LinearIsometryEquiv.refl ℂ H)
  let f := e.toLinearIsometry.completion
  let g := e.symm.toLinearIsometry.completion
  have hfg : f.toLinearMap.comp g.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro z
    change f (g z) = z
    refine UniformSpace.Completion.induction_on z
      (isClosed_eq (f.continuous.comp g.continuous) continuous_id) ?_
    intro z
    change e.toLinearIsometry.completion
        (e.symm.toLinearIsometry.completion
          (z : UniformSpace.Completion ((Lp ℂ 2 (Measure.radonProd μ ν)) ⊗[ℂ] H))) =
      (z : UniformSpace.Completion ((Lp ℂ 2 (Measure.radonProd μ ν)) ⊗[ℂ] H))
    rw [LinearIsometry.completion_apply_coe, LinearIsometry.completion_apply_coe]
    exact congrArg (fun z : (Lp ℂ 2 (Measure.radonProd μ ν)) ⊗[ℂ] H =>
      (z : UniformSpace.Completion ((Lp ℂ 2 (Measure.radonProd μ ν)) ⊗[ℂ] H)))
      (e.apply_symm_apply z)
  have hgf : g.toLinearMap.comp f.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro z
    change g (f z) = z
    refine UniformSpace.Completion.induction_on z
      (isClosed_eq (g.continuous.comp f.continuous) continuous_id) ?_
    intro z
    change e.symm.toLinearIsometry.completion
        (e.toLinearIsometry.completion
          (z : UniformSpace.Completion
            ((UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) ⊗[ℂ] H))) =
      (z : UniformSpace.Completion
        ((UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) ⊗[ℂ] H))
    rw [LinearIsometry.completion_apply_coe, LinearIsometry.completion_apply_coe]
    exact congrArg
      (fun z : (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) ⊗[ℂ] H =>
        (z : UniformSpace.Completion
          ((UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) ⊗[ℂ] H)))
      (e.symm_apply_apply z)
  let E := LinearIsometryEquiv.ofLinearIsometry f g.toLinearMap hfg hgf
  exact E.trans (L2.tensorToLp (𝕜 := ℂ) (H := H) (Measure.radonProd μ ν))

/-- The amplified constructor has the original stock tensor-congruence linear-map DATA. -/
theorem radonProductTensorHilbertUnitary_toLinearMap :
    (radonProductTensorHilbertUnitary (H := H) μ ν).toLinearMap =
      (L2.tensorToLp (𝕜 := ℂ) (H := H) (Measure.radonProd μ ν)).toLinearMap.comp
        ((TensorProduct.congrIsometry (radonProductTensorUnitary μ ν)
          (LinearIsometryEquiv.refl ℂ H)).toLinearIsometry.completion).toLinearMap := rfl

/-- Every full scalar tensor vector amplified by ξ has its actual scalar-vector values a.e. -/
theorem radonProductTensorHilbertUnitary_tmul_ae
    (t : UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) (ξ : H) :
    radonProductTensorHilbertUnitary (H := H) μ ν
        ((t ⊗ₜ[ℂ] ξ :
          (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) ⊗[ℂ] H) :
            UniformSpace.Completion
              ((UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) ⊗[ℂ] H)) =ᵐ[Measure.radonProd μ ν]
      fun z => radonProductTensorUnitary μ ν t z • ξ := by
  change L2.tensorToLp (Measure.radonProd μ ν)
      ((TensorProduct.congrIsometry (radonProductTensorUnitary μ ν)
          (LinearIsometryEquiv.refl ℂ H)).toLinearIsometry.completion
          ((t ⊗ₜ[ℂ] ξ :
            (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) ⊗[ℂ] H) :
              UniformSpace.Completion
                ((UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) ⊗[ℂ] H))) =ᵐ[Measure.radonProd μ ν] _
  rw [LinearIsometry.completion_apply_coe]
  change L2.tensorToLp (Measure.radonProd μ ν)
      (((radonProductTensorUnitary μ ν t) ⊗ₜ[ℂ] ξ :
        (Lp ℂ 2 (Measure.radonProd μ ν)) ⊗[ℂ] H) :
          UniformSpace.Completion ((Lp ℂ 2 (Measure.radonProd μ ν)) ⊗[ℂ] H)) =ᵐ[Measure.radonProd μ ν] _
  exact L2.tensorToLp_tmul_ae (Measure.radonProd μ ν) (radonProductTensorUnitary μ ν t) ξ

/-- Original compact-support factor vectors and ξ retain their literal product values a.e. -/
theorem radonProductTensorHilbertUnitary_compact_tmul_ae
    (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) (ξ : H) :
    radonProductTensorHilbertUnitary (H := H) μ ν
        (((((compactSupportInclusion μ f) ⊗ₜ[ℂ] (compactSupportInclusion ν g) :
          (Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) :
            UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) ⊗ₜ[ℂ] ξ) :
              UniformSpace.Completion
                ((UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) ⊗[ℂ] H)) =ᵐ[Measure.radonProd μ ν]
      fun z => (f z.1 * g z.2) • ξ := by
  filter_upwards [radonProductTensorHilbertUnitary_tmul_ae μ ν
      (((compactSupportInclusion μ f) ⊗ₜ[ℂ] (compactSupportInclusion ν g) :
        (Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) :
          UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) ξ,
    radonProductTensorUnitary_tmul_ae μ ν f g] with z hvector hscalar
  exact hvector.trans (congrArg (fun c : ℂ => c • ξ) hscalar)

/-- The same amplified tensor is the original H-valued Haar-L2 compact-support completion model. -/
def radonProductHilbertCompletionUnitary :
    UniformSpace.Completion
      ((UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) ⊗[ℂ] H) ≃ₗᵢ[ℂ]
      CompletionCore (H := H) (Measure.radonProd μ ν) :=
  (radonProductTensorHilbertUnitary (H := H) μ ν).trans
    (completionToLp (H := H) (Measure.radonProd μ ν)).symm

/-- The mapped original completion model has the same actual H-valued product Lp vector. -/
theorem radonProductHilbertCompletionUnitary_toLp
    (z : UniformSpace.Completion
      ((UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) ⊗[ℂ] H)) :
    completionToLp (H := H) (Measure.radonProd μ ν)
        (radonProductHilbertCompletionUnitary (H := H) μ ν z) =
      radonProductTensorHilbertUnitary (H := H) μ ν z :=
  LinearIsometryEquiv.apply_symm_apply _ _

end

end MeasureTheory.HaarL2
