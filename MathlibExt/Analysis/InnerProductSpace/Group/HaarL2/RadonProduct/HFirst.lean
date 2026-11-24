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

public import MathlibExt.Analysis.InnerProductSpace.Group.HaarL2.RadonProduct.Mixed
public import MathlibExt.Analysis.InnerProductSpace.Group.HaarL2.RadonProduct.Swap
public import MathlibExt.MeasureTheory.Function.L2Space.RightTensorProduct

/-!
# The original H-first nested double tensor as full Borel product L2

Use the actual first tensor-to-Lp unitary, completed stock commutation,
the verified reversed mixed-product unitary and literal coordinate exchange.
Their composition retains the entire original H-first nested carrier and
all pure-vector values. Both Haar choices stay explicit; H may be zero.

This supplies the coordinate model required before the original partial
Fourier construction. It selects no normalized dual Haar or Fourier unitary
from a Source theorem. Terminal Plancherel and generator-transport proofs
remain wholly open.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory UniformSpace
open scoped CompactlySupported TensorProduct

namespace MeasureTheory.HaarL2

noncomputable section

universe uX uY uH

section SingleMeasure

variable {X : Type uX} [MeasurableSpace X]
variable (μ : Measure X)
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The two actual one-measure tensor maps agree on their original exchanged pure vectors. -/
private theorem tensorToLpRight_tmul_eq (ξ : H) (f : Lp ℂ 2 μ) :
    L2.tensorToLpRight μ
        ((ξ ⊗ₜ[ℂ] f : H ⊗[ℂ] (Lp ℂ 2 μ)) : Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) =
      L2.tensorToLp μ
        ((f ⊗ₜ[ℂ] ξ : (Lp ℂ 2 μ) ⊗[ℂ] H) : Completion ((Lp ℂ 2 μ) ⊗[ℂ] H)) := by
  apply Lp.ext
  exact (L2.tensorToLpRight_tmul_ae μ ξ f).trans (L2.tensorToLp_tmul_ae μ f ξ).symm

end SingleMeasure

section TensorCoordinates

variable {X : Type uX} [MeasurableSpace X]
variable {Y : Type uY} [MeasurableSpace Y]
variable (μ : Measure X) (ν : Measure Y)
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual completed first tensor-to-Lp congruence has its original linear-map field. -/
private def radonProductHFirstCongruenceMap :
    Completion ((Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) ⊗[ℂ] (Lp ℂ 2 ν)) →ₗ[ℂ]
      Completion ((Lp H 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) :=
  (LinearIsometryEquiv.completion
    (TensorProduct.congrIsometry (L2.tensorToLpRight (𝕜 := ℂ) (H := H) μ)
      (LinearIsometryEquiv.refl ℂ (Lp ℂ 2 ν)))).toLinearMap

/-- The actual completed tensor commutation has its original linear-map field. -/
private def radonProductHFirstCommMap :
    Completion ((Lp H 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) →ₗ[ℂ]
      Completion ((Lp ℂ 2 ν) ⊗[ℂ] (Lp H 2 μ)) :=
  (LinearIsometryEquiv.completion
    (TensorProduct.commIsometry ℂ (Lp H 2 μ) (Lp ℂ 2 ν))).toLinearMap

/-- The actual first congruence acts on the entire original completed first-factor vector. -/
private theorem radonProductHFirstCongruenceMap_tmul
    (z : Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) (g : Lp ℂ 2 ν) :
    radonProductHFirstCongruenceMap (H := H) μ ν
        ((z ⊗ₜ[ℂ] g : (Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) ⊗[ℂ] (Lp ℂ 2 ν)) :
          Completion ((Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) ⊗[ℂ] (Lp ℂ 2 ν))) =
      (((L2.tensorToLpRight μ z) ⊗ₜ[ℂ] g : (Lp H 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) :
        Completion ((Lp H 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) := by
  change (LinearIsometryEquiv.completion
    (TensorProduct.congrIsometry (L2.tensorToLpRight (𝕜 := ℂ) (H := H) μ)
      (LinearIsometryEquiv.refl ℂ (Lp ℂ 2 ν))))
    ((z ⊗ₜ[ℂ] g : (Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) ⊗[ℂ] (Lp ℂ 2 ν)) :
      Completion ((Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) ⊗[ℂ] (Lp ℂ 2 ν))) = _
  rw [LinearIsometryEquiv.completion_apply_coe]
  rfl

omit [CompleteSpace H] in
/-- The actual commutation map keeps the literal whole Lp vector and second scalar factor. -/
private theorem radonProductHFirstCommMap_tmul (f : Lp H 2 μ) (g : Lp ℂ 2 ν) :
    radonProductHFirstCommMap (H := H) μ ν
        ((f ⊗ₜ[ℂ] g : (Lp H 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) :
          Completion ((Lp H 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) =
      ((g ⊗ₜ[ℂ] f : (Lp ℂ 2 ν) ⊗[ℂ] (Lp H 2 μ)) :
        Completion ((Lp ℂ 2 ν) ⊗[ℂ] (Lp H 2 μ))) := by
  change (LinearIsometryEquiv.completion
    (TensorProduct.commIsometry ℂ (Lp H 2 μ) (Lp ℂ 2 ν)))
    ((f ⊗ₜ[ℂ] g : (Lp H 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) :
      Completion ((Lp H 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) = _
  rw [LinearIsometryEquiv.completion_apply_coe]
  simp only [TensorProduct.commIsometry_apply, TensorProduct.comm_tmul]

end TensorCoordinates

section Product

variable {X : Type uX} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable {Y : Type uY} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]
variable (μ : Measure X) (ν : Measure Y) [μ.Regular] [ν.Regular]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The original X-first product Borel measurable space. -/
local instance instHFirstXYMeasurableSpace : MeasurableSpace (X × Y) := borel (X × Y)
local instance instHFirstXYBorelSpace : BorelSpace (X × Y) := ⟨rfl⟩

/-- The original Y-first product Borel measurable space. -/
local instance instHFirstYXMeasurableSpace : MeasurableSpace (Y × X) := borel (Y × X)
local instance instHFirstYXBorelSpace : BorelSpace (Y × X) := ⟨rfl⟩

/-- The entire original H-first nested double tensor is full H-valued Borel Radon product L2. -/
def radonProductHFirstTensorUnitary :
    Completion ((Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) ⊗[ℂ] (Lp ℂ 2 ν)) ≃ₗᵢ[ℂ]
      Lp H 2 (Measure.radonProd μ ν) :=
  (((LinearIsometryEquiv.completion
      (TensorProduct.congrIsometry (L2.tensorToLpRight (𝕜 := ℂ) (H := H) μ)
        (LinearIsometryEquiv.refl ℂ (Lp ℂ 2 ν)))).trans
      (LinearIsometryEquiv.completion
        (TensorProduct.commIsometry ℂ (Lp H 2 μ) (Lp ℂ 2 ν)))).trans
      (radonProductMixedTensorUnitary (H := H) ν μ)).trans
      (radonProductSwapIsometry (H := H) ν μ)

/-- The original nested unitary selects its actual congruence, commutation, mixed and swap fields. -/
private theorem radonProductHFirstTensorUnitary_apply
    (z : Completion ((Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) ⊗[ℂ] (Lp ℂ 2 ν))) :
    radonProductHFirstTensorUnitary (H := H) μ ν z =
      radonProductSwapIsometry (H := H) ν μ
        (radonProductMixedTensorUnitary (H := H) ν μ
          (radonProductHFirstCommMap (H := H) μ ν (radonProductHFirstCongruenceMap (H := H) μ ν z))) := rfl

/-- Original whole scalar factors and the H vector retain the literal completed pure values. -/
theorem radonProductHFirstTensorUnitary_tmul (ξ : H) (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    radonProductHFirstTensorUnitary (H := H) μ ν
        ((((ξ ⊗ₜ[ℂ] f : H ⊗[ℂ] (Lp ℂ 2 μ)) : Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) ⊗ₜ[ℂ] g) :
          Completion ((Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) ⊗[ℂ] (Lp ℂ 2 ν))) =
      radonProductSwapIsometry (H := H) ν μ
        (radonProductTensorHilbertUnitary (H := H) ν μ
          ((((g ⊗ₜ[ℂ] f : (Lp ℂ 2 ν) ⊗[ℂ] (Lp ℂ 2 μ)) :
            Completion ((Lp ℂ 2 ν) ⊗[ℂ] (Lp ℂ 2 μ))) ⊗ₜ[ℂ] ξ) :
              Completion ((Completion ((Lp ℂ 2 ν) ⊗[ℂ] (Lp ℂ 2 μ))) ⊗[ℂ] H))) := by
  rw [radonProductHFirstTensorUnitary_apply, radonProductHFirstCongruenceMap_tmul,
    radonProductHFirstCommMap_tmul, tensorToLpRight_tmul_eq]
  exact congrArg (fun v : Lp H 2 (Measure.radonProd ν μ) => radonProductSwapIsometry (H := H) ν μ v)
    (radonProductMixedTensorUnitary_tmul ν μ g f ξ)

/-- Original compact scalar factors give their H-valued product in the original coordinate order a.e. -/
theorem radonProductHFirstTensorUnitary_compact_tmul_ae
    (ξ : H) (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) :
    radonProductHFirstTensorUnitary (H := H) μ ν
        ((((ξ ⊗ₜ[ℂ] (compactSupportInclusion μ f) : H ⊗[ℂ] (Lp ℂ 2 μ)) :
          Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) ⊗ₜ[ℂ] (compactSupportInclusion ν g)) :
            Completion ((Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) ⊗[ℂ] (Lp ℂ 2 ν))) =ᵐ[Measure.radonProd μ ν]
      fun z : X × Y => (f z.1 * g z.2) • ξ := by
  rw [radonProductHFirstTensorUnitary_tmul]
  have hpres := Measure.measurePreserving_prodSwap_radonProd μ ν
  have hQ : QuasiMeasurePreserving (Prod.swap : X × Y → Y × X)
      (Measure.radonProd μ ν) (Measure.radonProd ν μ) :=
    ⟨hpres.measurable, by rw [hpres.map_eq]⟩
  let t : Completion ((Completion ((Lp ℂ 2 ν) ⊗[ℂ] (Lp ℂ 2 μ))) ⊗[ℂ] H) :=
    ((((compactSupportInclusion ν g) ⊗ₜ[ℂ] (compactSupportInclusion μ f) :
      (Lp ℂ 2 ν) ⊗[ℂ] (Lp ℂ 2 μ)) :
        Completion ((Lp ℂ 2 ν) ⊗[ℂ] (Lp ℂ 2 μ))) ⊗ₜ[ℂ] ξ)
  let v : Lp H 2 (Measure.radonProd ν μ) := radonProductTensorHilbertUnitary (H := H) ν μ t
  have hpure : v =ᵐ[Measure.radonProd ν μ] fun z : Y × X => (g z.1 * f z.2) • ξ :=
    radonProductTensorHilbertUnitary_compact_tmul_ae ν μ g f ξ
  filter_upwards [radonProductSwapIsometry_ae_eq ν μ v, hQ.ae_eq_comp hpure] with z h₁ h₂
  exact h₁.trans (h₂.trans (by
    change (g z.2 * f z.1) • ξ = (f z.1 * g z.2) • ξ
    rw [mul_comm]))

/-- The original H-first double tensor reaches the same actual product compact-support completion. -/
def radonProductHFirstCompletionUnitary :
    Completion ((Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) ⊗[ℂ] (Lp ℂ 2 ν)) ≃ₗᵢ[ℂ]
      CompletionCore (H := H) (Measure.radonProd μ ν) :=
  (radonProductHFirstTensorUnitary (H := H) μ ν).trans
    (completionToLp (H := H) (Measure.radonProd μ ν)).symm

/-- The original completion model has the literal full H-valued product Lp vector. -/
theorem radonProductHFirstCompletionUnitary_toLp
    (z : Completion ((Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) ⊗[ℂ] (Lp ℂ 2 ν))) :
    completionToLp (H := H) (Measure.radonProd μ ν)
        (radonProductHFirstCompletionUnitary (H := H) μ ν z) =
      radonProductHFirstTensorUnitary (H := H) μ ν z :=
  LinearIsometryEquiv.apply_symm_apply _ _

end Product

end

end MeasureTheory.HaarL2
