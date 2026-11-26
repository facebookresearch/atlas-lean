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
# Hilbert amplification of the scalar Radon tensor comparison

For a complete complex Hilbert space `H`, tensor the scalar Radon unitary `U_R : T ≃ Lp ℂ 2 R`
with the identity on `H`, then use the one-measure scalar-to-vector L² comparison.

This gives `U_H : Completion(T⊗H) ≃ Lp H 2 R` with `U_H(t⊗ξ)(z)=U_R(t)(z) • ξ` almost
everywhere. On compact-support factor tensors its value is `f(x)g(y) • ξ`. The same map also
identifies the source with the separated compact-support L² completion of the product space.
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

/-- **Borel product structure for Hilbert-valued Radon L².** For topological `X,Y`, the
product measurable carrier uses `borel(X×Y)`. -/
local instance instHilbertProductBorelMeasurableSpace : MeasurableSpace (X × Y) := borel (X × Y)
local instance instHilbertProductBorelSpace : BorelSpace (X × Y) := ⟨rfl⟩

/-- **Amplified scalar Radon tensor unitary.** Let `X,Y` be locally compact Hausdorff Borel
spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on `borel(X×Y)`, `i_μ,i_ν,i_R`
for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)`, `A(z)` for the
algebraic factor tensor inclusion into `T`, and `F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. Let `H` be
a complete complex Hilbert space, `U_R : T ≃ₗᵢ[ℂ] Lp ℂ 2 R` the scalar Radon tensor
unitary, and `U_H : Completion(T⊗H) ≃ₗᵢ[ℂ] Lp H 2 R` its Hilbert amplification.
`radonProductTensorHilbertUnitary μ ν=U_H`, obtained by the completion of `U_R⊗I_H`
followed by the one-measure L² tensor unitary. -/
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

/-- **Linear composition of the amplified Radon comparison.** Let `X,Y` be locally compact
Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. Let `H` be a complete complex Hilbert space, `U_R : T
≃ₗᵢ[ℂ] Lp ℂ 2 R` the scalar Radon tensor unitary, and `U_H : Completion(T⊗H) ≃ₗᵢ[ℂ] Lp H 2
R` its Hilbert amplification. the linear map of `U_H` is `tensorToLp R ∘
Completion(U_R⊗I_H)`. -/
theorem radonProductTensorHilbertUnitary_toLinearMap :
    (radonProductTensorHilbertUnitary (H := H) μ ν).toLinearMap =
      (L2.tensorToLp (𝕜 := ℂ) (H := H) (Measure.radonProd μ ν)).toLinearMap.comp
        ((TensorProduct.congrIsometry (radonProductTensorUnitary μ ν)
          (LinearIsometryEquiv.refl ℂ H)).toLinearIsometry.completion).toLinearMap := rfl

/-- **Pure tensor action of the Hilbert-amplified Radon unitary.** Let `X,Y` be locally
compact Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. Let `H` be a complete complex Hilbert space, `U_R : T
≃ₗᵢ[ℂ] Lp ℂ 2 R` the scalar Radon tensor unitary, and `U_H : Completion(T⊗H) ≃ₗᵢ[ℂ] Lp H 2
R` its Hilbert amplification. for `t∈T`, `ξ∈H`, `U_H(t⊗ξ)(z)=U_R(t)(z) • ξ` for `R`-almost
every `z`. -/
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

/-- **Compact factor tensor formula of the Hilbert amplification.** Let `X,Y` be locally
compact Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. Let `H` be a complete complex Hilbert space, `U_R : T
≃ₗᵢ[ℂ] Lp ℂ 2 R` the scalar Radon tensor unitary, and `U_H : Completion(T⊗H) ≃ₗᵢ[ℂ] Lp H 2
R` its Hilbert amplification. for compact-support `f,g` and `ξ∈H`, `U_H((i_μ f⊗i_ν
g)⊗ξ)(x,y)=f(x)g(y) • ξ` almost everywhere. -/
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

/-- **Hilbert tensor realization of the separated product compact-support completion.** Let
`X,Y` be locally compact Hausdorff Borel spaces and `μ,ν` regular measures. Write
`R=radonProd μ ν` on `borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions,
`T=Completion(Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion
into `T`, and `F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. Let `H` be a complete complex Hilbert space,
`U_R : T ≃ₗᵢ[ℂ] Lp ℂ 2 R` the scalar Radon tensor unitary, and `U_H : Completion(T⊗H)
≃ₗᵢ[ℂ] Lp H 2 R` its Hilbert amplification. the map `Completion(T⊗H) →
CompletionCore(H,R)` is `J_R⁻¹∘U_H`, where `J_R` identifies the separated compact-support
L² completion with `Lp H 2 R`. -/
def radonProductHilbertCompletionUnitary :
    UniformSpace.Completion
      ((UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) ⊗[ℂ] H) ≃ₗᵢ[ℂ]
      CompletionCore (H := H) (Measure.radonProd μ ν) :=
  (radonProductTensorHilbertUnitary (H := H) μ ν).trans
    (completionToLp (H := H) (Measure.radonProd μ ν)).symm

/-- **Product L² value of the compact-support completion comparison.** Let `X,Y` be locally
compact Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. Let `H` be a complete complex Hilbert space, `U_R : T
≃ₗᵢ[ℂ] Lp ℂ 2 R` the scalar Radon tensor unitary, and `U_H : Completion(T⊗H) ≃ₗᵢ[ℂ] Lp H 2
R` its Hilbert amplification. for every source vector `z`, applying `J_R` to
`radonProductHilbertCompletionUnitary μ ν z` gives `U_H(z)`. -/
theorem radonProductHilbertCompletionUnitary_toLp
    (z : UniformSpace.Completion
      ((UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) ⊗[ℂ] H)) :
    completionToLp (H := H) (Measure.radonProd μ ν)
        (radonProductHilbertCompletionUnitary (H := H) μ ν z) =
      radonProductTensorHilbertUnitary (H := H) μ ν z :=
  LinearIsometryEquiv.apply_symm_apply _ _

end

end MeasureTheory.HaarL2
