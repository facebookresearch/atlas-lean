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
public import MathlibExt.Analysis.InnerProductSpace.TensorProduct.CyclicCompletion
public import Mathlib.Analysis.Normed.Operator.Extend


/-!
# Isometric extension from factor tensors into Borel Radon L²

For locally compact Hausdorff Borel factors with regular measures, compact-support factor
tensors are dense in `T=Completion(Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)`. Their Radon product map has the
same norm as their factor-tensor inclusion.

It extends to a bounded linear map `E : T → Lp ℂ 2 (radonProd μ ν)` preserving every norm and
inner product. On compact-support pure tensors it has almost-everywhere value `f(x)g(y)`.
Surjectivity is established separately; the norm structures here are the Hilbert completion and
inherited L² norm structures.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set
open scoped CompactlySupported TensorProduct InnerProductSpace

namespace MeasureTheory.HaarL2

noncomputable section

universe uX uY

section FactorCore

variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Y : Type uY} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
variable (μ : Measure X) (ν : Measure Y) [μ.Regular] [ν.Regular]

/-- **Isometric inclusion of factor Hilbert tensors into their completion.** Let `X,Y` be
measurable spaces with measures `μ,ν`, and `T=Completion(Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)` with its
Hilbert tensor norm. `stockFactorTensorCompletionInclusion μ ν` is the linear isometry
from the algebraic tensor `Lp ℂ 2 μ⊗Lp ℂ 2 ν` into `T`. -/
def stockFactorTensorCompletionInclusion :
    (Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν) →ₗᵢ[ℂ]
      UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) := by
  let _ : UniformContinuousConstSMul ℂ ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) :=
    uniformContinuousConstSMul_of_continuousConstSMul ℂ ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))
  exact UniformSpace.Completion.toComplₗᵢ

/-- **Compact-support factor tensor followed by completion.** Let `X,Y` be topological Borel
spaces and `μ,ν` regular measures. For compact-support functions, let `A :
C_c(X,ℂ)⊗C_c(Y,ℂ) → T` be the tensor of their L² inclusions followed by completion.
`compactSupportFactorTensorCompletion μ ν=A`, sending `f⊗g` to the completed tensor `i_μ
f⊗i_ν g`. -/
def compactSupportFactorTensorCompletion :
    C_c(X, ℂ) ⊗[ℂ] C_c(Y, ℂ) →ₗ[ℂ]
      UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) :=
  (stockFactorTensorCompletionInclusion μ ν).toLinearMap.comp (compactSupportFactorTensor μ ν)

/-- **Completion value of a compact-support factor tensor.** Let `X,Y` be topological Borel
spaces and `μ,ν` regular measures. For compact-support functions, let `A :
C_c(X,ℂ)⊗C_c(Y,ℂ) → T` be the tensor of their L² inclusions followed by completion. for
algebraic `z`, `A(z)` is the completion inclusion of `compactSupportFactorTensor μ ν z`. -/
@[simp]
theorem compactSupportFactorTensorCompletion_apply (z : C_c(X, ℂ) ⊗[ℂ] C_c(Y, ℂ)) :
    compactSupportFactorTensorCompletion μ ν z =
      (compactSupportFactorTensor μ ν z :
        UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) := rfl

/-- **Norm retained by the factor-tensor completion inclusion.** Let `X,Y` be topological
Borel spaces and `μ,ν` regular measures. For compact-support functions, let `A :
C_c(X,ℂ)⊗C_c(Y,ℂ) → T` be the tensor of their L² inclusions followed by completion. for
algebraic compact-support `z`, `‖A(z)‖=‖compactSupportFactorTensor μ ν z‖`. -/
theorem norm_compactSupportFactorTensorCompletion (z : C_c(X, ℂ) ⊗[ℂ] C_c(Y, ℂ)) :
    ‖compactSupportFactorTensorCompletion μ ν z‖ = ‖compactSupportFactorTensor μ ν z‖ :=
  (stockFactorTensorCompletionInclusion μ ν).norm_map (compactSupportFactorTensor μ ν z)

end FactorCore

section FullCompletion

variable {X : Type uX} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable {Y : Type uY} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]
variable (μ : Measure X) (ν : Measure Y) [μ.Regular] [ν.Regular]

/-- **Dense compact-support factor tensors in the Hilbert completion.** Let `X,Y` be locally
compact Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. the map `A` has dense range in `T`. -/
theorem denseRange_compactSupportFactorTensorCompletion :
    DenseRange (compactSupportFactorTensorCompletion μ ν) := by
  let s : Set (Lp ℂ 2 μ) := Set.range (compactSupportInclusion (H := ℂ) μ)
  let t : Set (Lp ℂ 2 ν) := Set.range (compactSupportInclusion (H := ℂ) ν)
  have hs : Dense (Submodule.span ℂ s : Set (Lp ℂ 2 μ)) := by
    intro ξ
    exact (closure_mono Submodule.subset_span) (denseRange_compactSupportInclusion μ ξ)
  have ht : Dense (Submodule.span ℂ t : Set (Lp ℂ 2 ν)) := by
    intro η
    exact (closure_mono Submodule.subset_span) (denseRange_compactSupportInclusion ν η)
  let P : Set (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) :=
    {z | ∃ x ∈ s, ∃ y ∈ t,
      z = (x ⊗ₜ[ℂ] y : UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)))}
  have hP : Dense (Submodule.span ℂ P :
      Set (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)))) :=
    TensorProduct.dense_span_completed_tmul s t hs ht
  have hSpan : Submodule.span ℂ P ≤ (compactSupportFactorTensorCompletion μ ν).range := by
    apply Submodule.span_le.mpr
    rintro z ⟨x, ⟨f, rfl⟩, y, ⟨g, rfl⟩, rfl⟩
    refine ⟨f ⊗ₜ[ℂ] g, ?_⟩
    rw [compactSupportFactorTensorCompletion_apply, compactSupportFactorTensor,
      TensorProduct.map_tmul]
  intro z
  exact (closure_mono hSpan) (hP z)

/-- **Borel product structure underlying the full tensor extension target.** For topological
`X,Y`, the product carrier uses `borel(X×Y)`. -/
local instance instFullTensorProductBorelMeasurableSpace : MeasurableSpace (X × Y) := borel (X × Y)
local instance instFullTensorProductBorelSpace : BorelSpace (X × Y) := ⟨rfl⟩

/-- **Normed additive group of the completed factor tensor.** Let `X,Y` be measurable spaces
with measures `μ,ν`, and `T=Completion(Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)` with its Hilbert tensor
norm. the returned normed-group structure has the addition, negation and Hilbert tensor
norm of `T`. -/
@[instance_reducible]
def stockCompletedFactorTensorNormedAddCommGroup :
    NormedAddCommGroup (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) := inferInstance

/-- **Complex normed-space structure of the completed factor tensor.** Let `X,Y` be measurable
spaces with measures `μ,ν`, and `T=Completion(Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)` with its Hilbert
tensor norm. the scalar action on `T` extends the tensor action and satisfies `‖c •
z‖=|c|‖z‖`. -/
@[instance_reducible]
def stockCompletedFactorTensorNormedSpace :
    NormedSpace ℂ (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) where
  norm_smul_le := norm_smul_le

/-- **Inherited L² normed group of the Radon product space.** Let `X,Y` be locally compact
Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. `Lp ℂ 2 R` has its L² normed additive-group structure. -/
@[instance_reducible]
def stockRadonProductLpNormedAddCommGroup :
    NormedAddCommGroup (Lp ℂ 2 (Measure.radonProd μ ν)) := Lp.instNormedAddCommGroup

/-- **Inherited complex normed space of Radon product L².** Let `X,Y` be locally compact
Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. the L² scalar action on `Lp ℂ 2 R` satisfies `‖c •
f‖=|c|‖f‖`. -/
@[instance_reducible]
def stockRadonProductLpNormedSpace : NormedSpace ℂ (Lp ℂ 2 (Measure.radonProd μ ν)) :=
  Lp.instNormedSpace

/-- **Hilbert tensor completion additive norm structure.** Let `X,Y` be measurable spaces with
measures `μ,ν`, and `T=Completion(Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)` with its Hilbert tensor norm.
the additive norm structure on `T` is its Hilbert completion norm, with distance
`d(z,w)=‖z-w‖`. -/
local instance instNamedCompletedFactorTensorNormedAddCommGroup :
    NormedAddCommGroup (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) :=
  stockCompletedFactorTensorNormedAddCommGroup μ ν

/-- **Scalar norm compatibility of the tensor completion.** Let `X,Y` be measurable spaces
with measures `μ,ν`, and `T=Completion(Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)` with its Hilbert tensor
norm. the complex scalar action on `T` has the Hilbert norm relation `‖c • z‖=|c|‖z‖`. -/
local instance instNamedCompletedFactorTensorNormedSpace :
    NormedSpace ℂ (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) :=
  stockCompletedFactorTensorNormedSpace μ ν

/-- **Additive L² norm structure of the Radon target.** Let `X,Y` be locally compact Hausdorff
Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on `borel(X×Y)`,
`i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)`,
`A(z)` for the algebraic factor tensor inclusion into `T`, and `F(f⊗g)=i_R((x,y) ↦
f(x)g(y))`. the target `Lp ℂ 2 R` has its inherited additive norm and metric
`d(f,g)=‖f-g‖₂`. -/
local instance instNamedRadonProductLpNormedAddCommGroup :
    NormedAddCommGroup (Lp ℂ 2 (Measure.radonProd μ ν)) := stockRadonProductLpNormedAddCommGroup μ ν

/-- **Complex scalar norm compatibility of the Radon L² target.** Let `X,Y` be locally compact
Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. the target's scalar action satisfies `‖c • f‖₂=|c|‖f‖₂`. -/
local instance instNamedRadonProductLpNormedSpace :
    NormedSpace ℂ (Lp ℂ 2 (Measure.radonProd μ ν)) :=
  stockRadonProductLpNormedSpace μ ν

/-- **Underlying seminorm structure of the completed Hilbert tensor.** Let `X,Y` be measurable
spaces with measures `μ,ν`, and `T=Completion(Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)` with its Hilbert
tensor norm. the seminormed-group part of the completion's normed group uses the same norm
and distance on `T`. -/
local instance instFactoryCompletedFactorTensorSeminormedAddCommGroup :
    SeminormedAddCommGroup (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) :=
  (stockCompletedFactorTensorNormedAddCommGroup μ ν).toSeminormedAddCommGroup

/-- **Underlying seminorm structure of the Radon L² target.** Let `X,Y` be locally compact
Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. the seminormed-group part of `Lp ℂ 2 R` retains its L²
norm and metric. -/
local instance instFactoryRadonProductLpSeminormedAddCommGroup :
    SeminormedAddCommGroup (Lp ℂ 2 (Measure.radonProd μ ν)) :=
  (stockRadonProductLpNormedAddCommGroup μ ν).toSeminormedAddCommGroup

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
  [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y] [BorelSpace Y] [μ.Regular] [ν.Regular] in
/-- **Norm and uniform-completion topologies agree on the Hilbert tensor.** Let `X,Y` be
measurable spaces with measures `μ,ν`, and `T=Completion(Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)` with its
Hilbert tensor norm. the topology induced by the Hilbert completion norm on `T` equals its
uniform-completion topology, without factor topological or regularity assumptions. -/
theorem stockCompletedFactorTensorNormTopology_eq :
    @UniformSpace.toTopologicalSpace
      (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)))
      (@PseudoMetricSpace.toUniformSpace
        (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)))
        (@SeminormedAddCommGroup.toPseudoMetricSpace
          (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)))
          (stockCompletedFactorTensorNormedAddCommGroup μ ν).toSeminormedAddCommGroup)) =
      (UniformSpace.Completion.uniformSpace ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))).toTopologicalSpace := by
  let m : PseudoMetricSpace (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) :=
    (stockCompletedFactorTensorNormedAddCommGroup μ ν).toSeminormedAddCommGroup.toPseudoMetricSpace
  have hUniform : m.toUniformSpace =
      UniformSpace.Completion.uniformSpace ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) := by
    apply UniformSpace.ext
    exact (@PseudoMetricSpace.uniformity_dist _ m).trans
      (UniformSpace.Completion.uniformity_dist (α := (Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))).symm
  exact congrArg (fun w : UniformSpace (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) =>
    @UniformSpace.toTopologicalSpace
      (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) w) hUniform

/-- **Compact-support tensor density for the completion norm topology.** Let `X,Y` be locally
compact Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. the map `A` has dense range when `T` is equipped with its
Hilbert norm-induced topology. -/
theorem denseRange_compactSupportFactorTensorCompletion_normed :
    @DenseRange (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)))
      (@UniformSpace.toTopologicalSpace
        (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)))
        (@PseudoMetricSpace.toUniformSpace
          (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)))
          (@SeminormedAddCommGroup.toPseudoMetricSpace
            (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)))
            (stockCompletedFactorTensorNormedAddCommGroup μ ν).toSeminormedAddCommGroup)))
      (C_c(X, ℂ) ⊗[ℂ] C_c(Y, ℂ)) (compactSupportFactorTensorCompletion μ ν) := by
  rw [stockCompletedFactorTensorNormTopology_eq μ ν]
  exact denseRange_compactSupportFactorTensorCompletion μ ν

/-- **Radon product and factor completion have equal finite-tensor norms.** Let `X,Y` be
locally compact Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν`
on `borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ
⊗[ℂ] Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. for every algebraic compact-support tensor `z`,
`‖F(z)‖=‖A(z)‖`. -/
theorem norm_compactSupportTensorToLp_completion (z : C_c(X, ℂ) ⊗[ℂ] C_c(Y, ℂ)) :
    ‖compactSupportTensorToLp μ ν z‖ = ‖compactSupportFactorTensorCompletion μ ν z‖ :=
  (norm_compactSupportTensorToLp μ ν z).trans (norm_compactSupportFactorTensorCompletion μ ν z).symm

/-- **Finite tensor product map has a bounded factor-completion estimate.** Let `X,Y` be
locally compact Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν`
on `borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ
⊗[ℂ] Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. there exists `C∈ℝ` with `‖F(z)‖≤C‖A(z)‖` for every
algebraic compact-support tensor; the norm equality permits `C=1`. -/
theorem bound_compactSupportTensorToLp_completion :
    ∃ C : ℝ, ∀ z : C_c(X, ℂ) ⊗[ℂ] C_c(Y, ℂ),
      ‖compactSupportTensorToLp μ ν z‖ ≤ C * ‖compactSupportFactorTensorCompletion μ ν z‖ := by
  refine ⟨1, ?_⟩
  intro z
  exact (norm_compactSupportTensorToLp_completion μ ν z).le.trans_eq
    (one_mul ‖compactSupportFactorTensorCompletion μ ν z‖).symm

/-- **Continuous extension of finite products to the full Hilbert tensor.** Let `X,Y` be
locally compact Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν`
on `borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ
⊗[ℂ] Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. `radonProductTensorExtension μ ν : T →L[ℂ] Lp ℂ 2 R` is
the extension `E` characterized by `E(A(z))=F(z)` on the dense compact-support tensor
core. -/
def radonProductTensorExtension :
    UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) →L[ℂ]
      Lp ℂ 2 (Measure.radonProd μ ν) :=
  LinearMap.extendOfNorm
    (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := C_c(X, ℂ) ⊗[ℂ] C_c(Y, ℂ))
    (Eₗ := UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)))
    (F := Lp ℂ 2 (Measure.radonProd μ ν))
    (compactSupportTensorToLp μ ν) (compactSupportFactorTensorCompletion μ ν)

/-- **Core agreement of the Radon tensor continuous extension.** Let `X,Y` be locally compact
Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. for algebraic compact-support `z`,
`radonProductTensorExtension μ ν (A(z))=F(z)`. -/
theorem radonProductTensorExtension_apply_core (z : C_c(X, ℂ) ⊗[ℂ] C_c(Y, ℂ)) :
    radonProductTensorExtension μ ν (compactSupportFactorTensorCompletion μ ν z) =
      compactSupportTensorToLp μ ν z := by
  have hDense := denseRange_compactSupportFactorTensorCompletion_normed μ ν
  have hBound := bound_compactSupportTensorToLp_completion μ ν
  have hExtension := LinearMap.extendOfNorm_eq
    (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := C_c(X, ℂ) ⊗[ℂ] C_c(Y, ℂ))
    (Eₗ := UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)))
    (F := Lp ℂ 2 (Measure.radonProd μ ν))
    (f := compactSupportTensorToLp μ ν)
    (e := compactSupportFactorTensorCompletion μ ν)
  exact hExtension hDense hBound z

/-- **Norm preservation of the full Radon tensor extension.** Let `X,Y` be locally compact
Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. for every `z∈T`, `‖radonProductTensorExtension μ ν
z‖=‖z‖`. -/
theorem norm_radonProductTensorExtension
    (z : UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) :
    ‖radonProductTensorExtension μ ν z‖ = ‖z‖ := by
  have hCore (x : UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)))
      (hx : x ∈ Set.range (compactSupportFactorTensorCompletion μ ν)) :
      ‖radonProductTensorExtension μ ν x‖ = ‖x‖ := by
    obtain ⟨t, rfl⟩ := hx
    exact (congrArg norm (radonProductTensorExtension_apply_core μ ν t)).trans
      (norm_compactSupportTensorToLp_completion μ ν t)
  exact (denseRange_compactSupportFactorTensorCompletion μ ν).induction hCore
    (isClosed_eq (radonProductTensorExtension μ ν).continuous.norm continuous_norm) z

/-- **Linear isometry of the completed factor tensor into Radon L².** Let `X,Y` be locally
compact Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. `radonProductTensorEmbedding μ ν : T →ₗᵢ[ℂ] Lp ℂ 2 R` has
the same function as the continuous extension `E`. -/
def radonProductTensorEmbedding :
    UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) →ₗᵢ[ℂ]
      Lp ℂ 2 (Measure.radonProd μ ν) where
  toLinearMap := (radonProductTensorExtension μ ν).toLinearMap
  norm_map' := norm_radonProductTensorExtension μ ν

/-- **Algebraic core value of the full tensor embedding.** Let `X,Y` be locally compact
Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. for algebraic compact-support `z`,
`radonProductTensorEmbedding μ ν (A(z))=F(z)`. -/
theorem radonProductTensorEmbedding_apply_core (z : C_c(X, ℂ) ⊗[ℂ] C_c(Y, ℂ)) :
    radonProductTensorEmbedding μ ν (compactSupportFactorTensorCompletion μ ν z) =
      compactSupportTensorToLp μ ν z :=
  radonProductTensorExtension_apply_core μ ν z

/-- **Compact-support pure tensor value of the Radon embedding.** Let `X,Y` be locally compact
Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. `radonProductTensorEmbedding μ ν (i_μ f⊗i_ν g)=i_R(f⊠g)`. -/
@[simp]
theorem radonProductTensorEmbedding_tmul (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) :
    radonProductTensorEmbedding μ ν
        (((compactSupportInclusion μ f) ⊗ₜ[ℂ] (compactSupportInclusion ν g) :
          (Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) :
            UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) =
      compactSupportInclusion (Measure.radonProd μ ν)
        (CompactlySupportedContinuousMap.mulProd f g) := by
  simpa only [compactSupportFactorTensorCompletion_apply, compactSupportFactorTensor,
    TensorProduct.map_tmul, compactSupportTensorToLp_tmul] using
    radonProductTensorEmbedding_apply_core μ ν (f ⊗ₜ[ℂ] g)

/-- **Almost-everywhere pure product of the completed tensor embedding.** Let `X,Y` be locally
compact Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. the embedded completed tensor `i_μ f⊗i_ν g` has value
`f(x)g(y)` for `R`-almost every `(x,y)`. -/
theorem radonProductTensorEmbedding_tmul_ae (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) :
    radonProductTensorEmbedding μ ν
        (((compactSupportInclusion μ f) ⊗ₜ[ℂ] (compactSupportInclusion ν g) :
          (Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) :
            UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) =ᵐ[Measure.radonProd μ ν]
      fun z => f z.1 * g z.2 := by
  rw [radonProductTensorEmbedding_tmul]
  exact compactSupportInclusion_ae_eq (Measure.radonProd μ ν)
    (CompactlySupportedContinuousMap.mulProd f g)

/-- **Inner product preserved by the full Radon tensor embedding.** Let `X,Y` be locally
compact Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. for `z,w∈T`, `⟨radonProductTensorEmbedding μ ν
z,radonProductTensorEmbedding μ ν w⟩=⟨z,w⟩`. -/
theorem radonProductTensorEmbedding_inner
    (z w : UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) :
    inner ℂ (radonProductTensorEmbedding μ ν z) (radonProductTensorEmbedding μ ν w) = inner ℂ z w :=
  (radonProductTensorEmbedding μ ν).inner_map_map z w

end FullCompletion

end

end MeasureTheory.HaarL2
