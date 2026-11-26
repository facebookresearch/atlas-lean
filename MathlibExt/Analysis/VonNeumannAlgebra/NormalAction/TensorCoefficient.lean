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

public import MathlibExt.MeasureTheory.Function.L2Space.RightTensorProduct
public import MathlibExt.Analysis.VonNeumannAlgebra.NormalAction.RegularCoefficientAlgebra

/-!
# Regular coefficients on the Hilbert-first tensor model

Let `α` be a normal action and `μ` a regular measure on the locally compact Borel group. On
`T=Completion(H ⊗[ℂ] Lp ℂ 2 μ)`, the unitary `U : T ≃ Lp H 2 μ` has pure value `U(ξ⊗f) =ᵐ[μ] (s
↦ f(s) • ξ)`.

Transporting the regular coefficient gives `Q_x=U⁻¹P_xU`, a unital complex star representation
with `‖Q_x‖≤‖x‖`. In L² coordinates it has the almost-everywhere inverse-action formula. Haar
invariance is not required for these tensor coefficients.

Here `=ᵐ[μ]` denotes equality of measurable representatives μ-almost everywhere, not point
evaluation of an L² class. Operator identities are equalities of bounded operators.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory MeasureTheory.HaarL2 Filter
open scoped TensorProduct ENNReal Topology CompactlySupported InnerProductSpace CStarAlgebra

namespace VonNeumannAlgebra.NormalAction

noncomputable section

universe uG uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (μ : Measure G) [μ.Regular]

/-- **Regular coefficient conjugated onto the Hilbert-first tensor.** Let `G` be a group with
a topology, `H` a complete complex Hilbert space, `M⊆B(H)` a concrete von Neumann algebra,
and `α` a normal action with norm-continuous inverse predual orbits. Assume `G` is a
topological group. Assume `G` is locally compact with its Borel measurable structure, and
`μ` is a regular measure. On `L=Lp H 2 μ`, put `P_x ξ =ᵐ[μ] (s ↦ α_(s⁻¹)(x)ξ(s))`. Haar
invariance is not assumed. Let `T=Completion(H ⊗[ℂ] Lp ℂ 2 μ)` and `U : T ≃ₗᵢ[ℂ] L` be
`tensorToLpRight μ`, with `U(ξ⊗f) =ᵐ[μ] (s ↦ f(s) • ξ)`. Set `Q_x=U⁻¹ P_x U`.
`regularCoefficientTensor μ α x=Q_x : T →L[ℂ] T`.

Here `=ᵐ[μ]` denotes equality of measurable representatives μ-almost everywhere, not point
evaluation of an L² class. Operator identities are equalities of bounded operators. -/
def regularCoefficientTensor (α : NormalAction G M) (x : M) :
    UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
      UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) :=
  (L2.tensorToLpRight (𝕜 := ℂ) (H := H) μ).symm.conjStarAlgEquiv (regularCoefficient μ α x)

/-- **Tensor regular coefficient star homomorphism.** Let `G` be a group with a topology, `H`
a complete complex Hilbert space, `M⊆B(H)` a concrete von Neumann algebra, and `α` a
normal action with norm-continuous inverse predual orbits. Assume `G` is a topological
group. Assume `G` is locally compact with its Borel measurable structure, and `μ` is a
regular measure. On `L=Lp H 2 μ`, put `P_x ξ =ᵐ[μ] (s ↦ α_(s⁻¹)(x)ξ(s))`. Haar invariance
is not assumed. Let `T=Completion(H ⊗[ℂ] Lp ℂ 2 μ)` and `U : T ≃ₗᵢ[ℂ] L` be
`tensorToLpRight μ`, with `U(ξ⊗f) =ᵐ[μ] (s ↦ f(s) • ξ)`. Set `Q_x=U⁻¹ P_x U`.
`regularCoefficientTensorHom μ α : M →⋆ₐ[ℂ] B(T)` sends `x` to `Q_x=U⁻¹P_xU`.

Here `=ᵐ[μ]` denotes equality of measurable representatives μ-almost everywhere, not point
evaluation of an L² class. Operator identities are equalities of bounded operators. -/
def regularCoefficientTensorHom (α : NormalAction G M) :
    M →⋆ₐ[ℂ] (UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
      UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) :=
  (L2.tensorToLpRight (𝕜 := ℂ) (H := H) μ).symm.conjStarAlgEquiv.toStarAlgHom.comp
    (regularCoefficientHom μ α)

/-- **Operator value of the tensor coefficient homomorphism.** Let `G` be a group with a
topology, `H` a complete complex Hilbert space, `M⊆B(H)` a concrete von Neumann algebra,
and `α` a normal action with norm-continuous inverse predual orbits. Assume `G` is a
topological group. Assume `G` is locally compact with its Borel measurable structure, and
`μ` is a regular measure. On `L=Lp H 2 μ`, put `P_x ξ =ᵐ[μ] (s ↦ α_(s⁻¹)(x)ξ(s))`. Haar
invariance is not assumed. Let `T=Completion(H ⊗[ℂ] Lp ℂ 2 μ)` and `U : T ≃ₗᵢ[ℂ] L` be
`tensorToLpRight μ`, with `U(ξ⊗f) =ᵐ[μ] (s ↦ f(s) • ξ)`. Set `Q_x=U⁻¹ P_x U`. for `x∈M`,
`regularCoefficientTensorHom μ α x=regularCoefficientTensor μ α x=Q_x`.

Here `=ᵐ[μ]` denotes equality of measurable representatives μ-almost everywhere, not point
evaluation of an L² class. Operator identities are equalities of bounded operators. -/
@[simp]
theorem regularCoefficientTensorHom_apply (α : NormalAction G M) (x : M) :
    regularCoefficientTensorHom μ α x = regularCoefficientTensor μ α x :=
  rfl

/-- **Operator norm of the Hilbert-first tensor coefficient.** Let `G` be a group with a
topology, `H` a complete complex Hilbert space, `M⊆B(H)` a concrete von Neumann algebra,
and `α` a normal action with norm-continuous inverse predual orbits. Assume `G` is a
topological group. Assume `G` is locally compact with its Borel measurable structure, and
`μ` is a regular measure. On `L=Lp H 2 μ`, put `P_x ξ =ᵐ[μ] (s ↦ α_(s⁻¹)(x)ξ(s))`. Haar
invariance is not assumed. Let `T=Completion(H ⊗[ℂ] Lp ℂ 2 μ)` and `U : T ≃ₗᵢ[ℂ] L` be
`tensorToLpRight μ`, with `U(ξ⊗f) =ᵐ[μ] (s ↦ f(s) • ξ)`. Set `Q_x=U⁻¹ P_x U`. for `x∈M`,
`‖Q_x‖≤‖x‖`.

Here `=ᵐ[μ]` denotes equality of measurable representatives μ-almost everywhere, not point
evaluation of an L² class. Operator identities are equalities of bounded operators. -/
theorem norm_regularCoefficientTensor_le (α : NormalAction G M) (x : M) :
    ‖regularCoefficientTensor μ α x‖ ≤ ‖x‖ := by
  let E := L2.tensorToLpRight (𝕜 := ℂ) (H := H) μ
  apply (regularCoefficientTensor μ α x).opNorm_le_bound (norm_nonneg x)
  intro z
  change ‖E.symm (regularCoefficient μ α x (E z))‖ ≤ ‖x‖ * ‖z‖
  rw [E.symm.norm_map]
  simpa only [E.norm_map] using regularCoefficient_norm_apply_le μ α x (E z)

/-- **L² representative of a tensor coefficient value.** Let `G` be a group with a topology,
`H` a complete complex Hilbert space, `M⊆B(H)` a concrete von Neumann algebra, and `α` a
normal action with norm-continuous inverse predual orbits. Assume `G` is a topological
group. Assume `G` is locally compact with its Borel measurable structure, and `μ` is a
regular measure. On `L=Lp H 2 μ`, put `P_x ξ =ᵐ[μ] (s ↦ α_(s⁻¹)(x)ξ(s))`. Haar invariance
is not assumed. Let `T=Completion(H ⊗[ℂ] Lp ℂ 2 μ)` and `U : T ≃ₗᵢ[ℂ] L` be
`tensorToLpRight μ`, with `U(ξ⊗f) =ᵐ[μ] (s ↦ f(s) • ξ)`. Set `Q_x=U⁻¹ P_x U`. for `z∈T`,
`U(Q_x z)(s)=α_(s⁻¹)(x)(U z(s))` for `μ`-almost every `s`.

Here `=ᵐ[μ]` denotes equality of measurable representatives μ-almost everywhere, not point
evaluation of an L² class. Operator identities are equalities of bounded operators. -/
theorem regularCoefficientTensor_ae_eq (α : NormalAction G M) (x : M)
    (z : UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) :
    L2.tensorToLpRight μ (regularCoefficientTensor μ α x z) =ᵐ[μ]
      fun s => (α s⁻¹ x : H →L[ℂ] H) (L2.tensorToLpRight μ z s) := by
  let E := L2.tensorToLpRight (𝕜 := ℂ) (H := H) μ
  change E (E.symm (regularCoefficient μ α x (E z))) =ᵐ[μ] _
  rw [E.apply_symm_apply]
  exact regularCoefficient_ae_eq μ α x (E z)

/-- **Pure compact-support tensor formula of the regular coefficient.** Let `G` be a group
with a topology, `H` a complete complex Hilbert space, `M⊆B(H)` a concrete von Neumann
algebra, and `α` a normal action with norm-continuous inverse predual orbits. Assume `G`
is a topological group. Assume `G` is locally compact with its Borel measurable structure,
and `μ` is a regular measure. On `L=Lp H 2 μ`, put `P_x ξ =ᵐ[μ] (s ↦ α_(s⁻¹)(x)ξ(s))`.
Haar invariance is not assumed. Let `T=Completion(H ⊗[ℂ] Lp ℂ 2 μ)` and `U : T ≃ₗᵢ[ℂ] L`
be `tensorToLpRight μ`, with `U(ξ⊗f) =ᵐ[μ] (s ↦ f(s) • ξ)`. Set `Q_x=U⁻¹ P_x U`. for
`f∈C_c(G,ℂ)` with L² inclusion `i_μ` and `ξ∈H`, `U(Q_x(ξ⊗i_μ f))(s)=α_(s⁻¹)(x)(f(s) • ξ)`
almost everywhere.

Here `=ᵐ[μ]` denotes equality of measurable representatives μ-almost everywhere, not point
evaluation of an L² class. Operator identities are equalities of bounded operators. -/
theorem regularCoefficientTensor_apply_compactSupport_tmul_ae (α : NormalAction G M) (x : M)
    (f : C_c(G, ℂ)) (ξ : H) :
    L2.tensorToLpRight μ
        (regularCoefficientTensor μ α x
          ((ξ ⊗ₜ[ℂ] compactSupportInclusion (H := ℂ) μ f : H ⊗[ℂ] (Lp ℂ 2 μ)) :
            UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)))) =ᵐ[μ]
      fun s => (α s⁻¹ x : H →L[ℂ] H) (f s • ξ) := by
  have hpure := L2.tensorToLpRight_tmul_ae (𝕜 := ℂ) μ ξ (compactSupportInclusion (H := ℂ) μ f)
  have hscalar := compactSupportInclusion_ae_eq (H := ℂ) μ f
  filter_upwards [regularCoefficientTensor_ae_eq μ α x
    ((ξ ⊗ₜ[ℂ] compactSupportInclusion (H := ℂ) μ f : H ⊗[ℂ] (Lp ℂ 2 μ)) :
      UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))), hpure, hscalar] with s hcoeff hvector hscalar
  rw [hcoeff, hvector, hscalar]

end

end VonNeumannAlgebra.NormalAction
