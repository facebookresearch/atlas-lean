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
# Nested Hilbert-first tensors as full Radon L²

For locally compact Hausdorff Borel spaces, regular measures `μ,ν` and complete complex Hilbert
space `H`, the nested tensor `Z=Completion(Completion(H⊗L²(μ))⊗L²(ν))` is isometrically
equivalent to `Lp H 2 (radonProd μ ν)`.

The map first realizes `H⊗L²(μ)`, commutes the two outer factors, uses the reversed mixed Radon
unitary, and swaps the product coordinates. On compact-support pure factors it has
representative `f(x)g(y) • ξ`. The preliminary congruence maps work for arbitrary measurable
spaces and measures, without a Fourier transform.
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

/-- **Agreement of the two one-measure tensor orders on pure vectors.** Let `X` be measurable,
`μ` any measure and `H` a complete complex Hilbert space. For `ξ∈H`, `f∈Lp ℂ 2 μ`,
`tensorToLpRight μ (ξ⊗f)=tensorToLp μ (f⊗ξ)` in `Lp H 2 μ`. -/
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

/-- **Completed tensor congruence of the first Hilbert L² factor.** Let `X,Y` be measurable
spaces with measures `μ,ν` and `H` a complete complex Hilbert space. Let `U_μ :
Completion(H⊗Lp ℂ 2 μ) ≃ₗᵢ[ℂ] Lp H 2 μ` be `tensorToLpRight μ`, with `U_μ(ξ⊗f)(x)=f(x) •
ξ`. the map is `Completion(U_μ⊗I_(Lp ℂ 2 ν))`, from the nested `Z` to `Completion(Lp H 2
μ⊗Lp ℂ 2 ν)`. -/
private def radonProductHFirstCongruenceMap :
    Completion ((Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) ⊗[ℂ] (Lp ℂ 2 ν)) →ₗ[ℂ]
      Completion ((Lp H 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) :=
  (LinearIsometryEquiv.completion
    (TensorProduct.congrIsometry (L2.tensorToLpRight (𝕜 := ℂ) (H := H) μ)
      (LinearIsometryEquiv.refl ℂ (Lp ℂ 2 ν)))).toLinearMap

/-- **Completed commutation of a vector L² factor and scalar L² factor.** Let `X,Y` be
measurable with measures `μ,ν` and `H` a complex normed inner-product space. The linear
map `Completion(Lp H 2 μ⊗Lp ℂ 2 ν) → Completion(Lp ℂ 2 ν⊗Lp H 2 μ)` sends `F⊗g` to `g⊗F`;
completeness of `H` is not required. -/
private def radonProductHFirstCommMap :
    Completion ((Lp H 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) →ₗ[ℂ]
      Completion ((Lp ℂ 2 ν) ⊗[ℂ] (Lp H 2 μ)) :=
  (LinearIsometryEquiv.completion
    (TensorProduct.commIsometry ℂ (Lp H 2 μ) (Lp ℂ 2 ν))).toLinearMap

/-- **Pure value of the first-factor completion congruence.** Let `X,Y` be measurable spaces
with measures `μ,ν` and `H` a complete complex Hilbert space. Let `U_μ : Completion(H⊗Lp ℂ
2 μ) ≃ₗᵢ[ℂ] Lp H 2 μ` be `tensorToLpRight μ`, with `U_μ(ξ⊗f)(x)=f(x) • ξ`. for
`z∈Completion(H⊗Lp ℂ 2 μ)`, `g∈Lp ℂ 2 ν`, the congruence sends `z⊗g` to `U_μ(z)⊗g` in the
completed outer tensor. -/
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
/-- **Pure value of completed vector-scalar tensor commutation.** Let `X,Y` be measurable with
measures `μ,ν` and `H` a complex normed inner-product space. For `F∈Lp H 2 μ`, `g∈Lp ℂ 2
ν`, the completed commutation map sends `F⊗g` to `g⊗F`, without completeness of `H`. -/
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

/-- **Borel structure of the first coordinate order in the nested tensor model.** For
topological `X,Y`, use `borel(X×Y)` from its product topology. -/
local instance instHFirstXYMeasurableSpace : MeasurableSpace (X × Y) := borel (X × Y)
local instance instHFirstXYBorelSpace : BorelSpace (X × Y) := ⟨rfl⟩

/-- **Borel structure of the reversed coordinate order in the nested tensor model.** For
topological `X,Y`, use `borel(Y×X)` from its reversed product topology. -/
local instance instHFirstYXMeasurableSpace : MeasurableSpace (Y × X) := borel (Y × X)
local instance instHFirstYXBorelSpace : BorelSpace (Y × X) := ⟨rfl⟩

/-- **Full nested Hilbert-first Radon tensor unitary.** Let `X,Y` be locally compact Hausdorff
Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on `borel(X×Y)`,
`i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)`,
`A(z)` for the algebraic factor tensor inclusion into `T`, and `F(f⊗g)=i_R((x,y) ↦
f(x)g(y))`. Let `H` be a complete complex Hilbert space and `Z=Completion(Completion(H⊗Lp
ℂ 2 μ)⊗Lp ℂ 2 ν)`. Let `U_μ=tensorToLpRight μ`, `C=Completion(U_μ⊗I)`, `K` be completed
tensor commutation, `M` the mixed Radon unitary for the reversed factors `(ν,μ)`, and `S`
coordinate swap from the reversed Radon L² space. Put `V=S∘M∘K∘C`.
`radonProductHFirstTensorUnitary μ ν=V : Z ≃ₗᵢ[ℂ] Lp H 2 R`, with all four isometric maps
in the indicated order. -/
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

/-- **Four-map vector formula of the nested Radon unitary.** Let `X,Y` be locally compact
Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. Let `H` be a complete complex Hilbert space and
`Z=Completion(Completion(H⊗Lp ℂ 2 μ)⊗Lp ℂ 2 ν)`. Let `U_μ=tensorToLpRight μ`,
`C=Completion(U_μ⊗I)`, `K` be completed tensor commutation, `M` the mixed Radon unitary
for the reversed factors `(ν,μ)`, and `S` coordinate swap from the reversed Radon L²
space. Put `V=S∘M∘K∘C`. for `z∈Z`, `radonProductHFirstTensorUnitary μ ν z=S(M(K(C(z))))`. -/
private theorem radonProductHFirstTensorUnitary_apply
    (z : Completion ((Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) ⊗[ℂ] (Lp ℂ 2 ν))) :
    radonProductHFirstTensorUnitary (H := H) μ ν z =
      radonProductSwapIsometry (H := H) ν μ
        (radonProductMixedTensorUnitary (H := H) ν μ
          (radonProductHFirstCommMap (H := H) μ ν (radonProductHFirstCongruenceMap (H := H) μ ν z))) := rfl

/-- **Pure whole-factor value of the nested Radon tensor unitary.** Let `X,Y` be locally
compact Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. Let `H` be a complete complex Hilbert space and
`Z=Completion(Completion(H⊗Lp ℂ 2 μ)⊗Lp ℂ 2 ν)`. Let `U_μ=tensorToLpRight μ`,
`C=Completion(U_μ⊗I)`, `K` be completed tensor commutation, `M` the mixed Radon unitary
for the reversed factors `(ν,μ)`, and `S` coordinate swap from the reversed Radon L²
space. Put `V=S∘M∘K∘C`. for `ξ∈H`, `f∈Lp ℂ 2 μ`, `g∈Lp ℂ 2 ν`, `V((ξ⊗f)⊗g)` is the
coordinate swap of the reversed Hilbert-amplified Radon image of `(g⊗f)⊗ξ`. -/
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

/-- **Compact-support pure formula in the nested Hilbert-first order.** Let `X,Y` be locally
compact Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. Let `H` be a complete complex Hilbert space and
`Z=Completion(Completion(H⊗Lp ℂ 2 μ)⊗Lp ℂ 2 ν)`. Let `U_μ=tensorToLpRight μ`,
`C=Completion(U_μ⊗I)`, `K` be completed tensor commutation, `M` the mixed Radon unitary
for the reversed factors `(ν,μ)`, and `S` coordinate swap from the reversed Radon L²
space. Put `V=S∘M∘K∘C`. for compact-support scalar `f,g` and `ξ∈H`, `V((ξ⊗i_μ f)⊗i_ν
g)(x,y)=f(x)g(y) • ξ` for `R`-almost every `(x,y)`. -/
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
    hpres.quasiMeasurePreserving
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

/-- **Nested tensor unitary into the separated product compact-support completion.** Let `X,Y`
be locally compact Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ
ν` on `borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2
μ ⊗[ℂ] Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. Let `H` be a complete complex Hilbert space and
`Z=Completion(Completion(H⊗Lp ℂ 2 μ)⊗Lp ℂ 2 ν)`. Let `U_μ=tensorToLpRight μ`,
`C=Completion(U_μ⊗I)`, `K` be completed tensor commutation, `M` the mixed Radon unitary
for the reversed factors `(ν,μ)`, and `S` coordinate swap from the reversed Radon L²
space. Put `V=S∘M∘K∘C`. the map into `CompletionCore(H,R)` is `J_R⁻¹∘V`, where `J_R` is
the product compact-support L² completion comparison. -/
def radonProductHFirstCompletionUnitary :
    Completion ((Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) ⊗[ℂ] (Lp ℂ 2 ν)) ≃ₗᵢ[ℂ]
      CompletionCore (H := H) (Measure.radonProd μ ν) :=
  (radonProductHFirstTensorUnitary (H := H) μ ν).trans
    (completionToLp (H := H) (Measure.radonProd μ ν)).symm

/-- **Product L² value of the nested compact-support completion unitary.** Let `X,Y` be
locally compact Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν`
on `borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ
⊗[ℂ] Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. Let `H` be a complete complex Hilbert space and
`Z=Completion(Completion(H⊗Lp ℂ 2 μ)⊗Lp ℂ 2 ν)`. Let `U_μ=tensorToLpRight μ`,
`C=Completion(U_μ⊗I)`, `K` be completed tensor commutation, `M` the mixed Radon unitary
for the reversed factors `(ν,μ)`, and `S` coordinate swap from the reversed Radon L²
space. Put `V=S∘M∘K∘C`. for `z∈Z`, applying `J_R` to `radonProductHFirstCompletionUnitary
μ ν z` yields `V(z)`. -/
theorem radonProductHFirstCompletionUnitary_toLp
    (z : Completion ((Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) ⊗[ℂ] (Lp ℂ 2 ν))) :
    completionToLp (H := H) (Measure.radonProd μ ν)
        (radonProductHFirstCompletionUnitary (H := H) μ ν z) =
      radonProductHFirstTensorUnitary (H := H) μ ν z :=
  LinearIsometryEquiv.apply_symm_apply _ _

end Product

end

end MeasureTheory.HaarL2
