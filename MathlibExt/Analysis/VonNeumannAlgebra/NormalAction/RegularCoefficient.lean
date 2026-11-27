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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalAction.Continuity
public import MathlibExt.Analysis.InnerProductSpace.Group.HaarL2.PointwiseOperator
public import MathlibExt.Analysis.InnerProductSpace.Group.HaarRegularRepresentation
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Inverse-action coefficient operators on regular-measure L²

For a normal action `α` on `M⊆B(H)`, the coefficient field is `x_s=α_(s⁻¹)(x)`. Its vector
action is jointly continuous and satisfies `‖x_s‖≤‖x‖`. It acts on compact-support continuous
vectors by `f(s) ↦ x_s f(s)`.

For a locally compact group with Borel structure and regular measure `μ`, this extends to the
bounded operator `P_x` on `Lp H 2 μ` with `(P_x ξ)(s)=x_s ξ(s)` almost everywhere and
`‖P_xξ‖≤‖x‖‖ξ‖`. The separated L² completion of `C_c(G,H)` gives the same action on its dense
images. The measure need not be Haar.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory MeasureTheory.HaarL2 Filter
open scoped ENNReal Topology CompactlySupported InnerProductSpace CStarAlgebra

namespace VonNeumannAlgebra
namespace NormalAction

noncomputable section

universe uG uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

omit [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- **Joint continuity of the inverse-action coefficient field.** Let `G` be a group with a
topology, `H` a complete complex Hilbert space, `M⊆B(H)` a concrete von Neumann algebra,
and `α` a normal action with norm-continuous inverse predual orbits. Assume `G` is a
topological group. for `x∈M`, the map `(s,ξ) ↦ (α_(s⁻¹)(x) : B(H))ξ` is continuous from
`G×H` to `H`. Local compactness and a measure are not required. -/
theorem continuous_regularCoefficientField (α : NormalAction G M) (x : M) :
    Continuous fun p : G × H => (α p.1⁻¹ x : H →L[ℂ] H) p.2 :=
  (continuous_vector_action α x).comp
    ((continuous_inv.comp continuous_fst).prodMk continuous_snd)

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- **Uniform coefficient norm of a normal automorphism orbit.** Let `G` be a group with a
topology, `H` a complete complex Hilbert space, `M⊆B(H)` a concrete von Neumann algebra,
and `α` a normal action with norm-continuous inverse predual orbits. for `x∈M` and `s∈G`,
`‖(α_(s⁻¹)(x) : B(H))‖≤‖x‖`. Continuity of group operations is not needed for this bound. -/
theorem regularCoefficientField_norm_le (α : NormalAction G M) (x : M) (s : G) :
    ‖(α s⁻¹ x : H →L[ℂ] H)‖ ≤ ‖x‖ := by
  change ‖α s⁻¹ x‖ ≤ ‖x‖
  exact (StarAlgEquiv.norm_map (α s⁻¹).toStarAlgEquiv x).le

omit [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- **Inverse-action coefficient on compact-support vectors.** Let `G` be a group with a
topology, `H` a complete complex Hilbert space, `M⊆B(H)` a concrete von Neumann algebra,
and `α` a normal action with norm-continuous inverse predual orbits. Assume `G` is a
topological group. for `x∈M`, `regularCoefficientCompactSupport α x : C_c(G,H) →ₗ[ℂ]
C_c(G,H)` sends `f(s)` to `α_(s⁻¹)(x)f(s)`. No measure or local compactness is required
here. -/
def regularCoefficientCompactSupport (α : NormalAction G M) (x : M) :
    C_c(G, H) →ₗ[ℂ] C_c(G, H) :=
  pointwiseCompactSupport (fun s => (α s⁻¹ x : H →L[ℂ] H))
    (continuous_regularCoefficientField α x)

omit [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- **Pointwise compact-support regular coefficient formula.** Let `G` be a group with a
topology, `H` a complete complex Hilbert space, `M⊆B(H)` a concrete von Neumann algebra,
and `α` a normal action with norm-continuous inverse predual orbits. Assume `G` is a
topological group. for `x∈M`, `f∈C_c(G,H)` and `s∈G`, `regularCoefficientCompactSupport α
x f s=α_(s⁻¹)(x)f(s)`. -/
@[simp]
theorem regularCoefficientCompactSupport_apply (α : NormalAction G M) (x : M)
    (f : C_c(G, H)) (s : G) :
    regularCoefficientCompactSupport α x f s = (α s⁻¹ x : H →L[ℂ] H) (f s) :=
  rfl

variable (μ : Measure G) [μ.Regular]

omit [LocallyCompactSpace G] in
/-- **L² bound of the compact-support coefficient action.** Let `G` be a group with a
topology, `H` a complete complex Hilbert space, `M⊆B(H)` a concrete von Neumann algebra,
and `α` a normal action with norm-continuous inverse predual orbits. Assume `G` is a
topological group. Give `G` its Borel structure and let `μ` be a regular measure. Write
`i_μ : C_c(G,H) → Lp H 2 μ` for the compact-support inclusion. for `x∈M` and `f∈C_c(G,H)`,
`‖i_μ(regularCoefficientCompactSupport α x f)‖≤‖x‖‖i_μ(f)‖`. Local compactness is not
assumed in this estimate. -/
theorem regularCoefficientCompactSupport_l2Bound (α : NormalAction G M) (x : M)
    (f : C_c(G, H)) :
    ‖compactSupportInclusion μ (regularCoefficientCompactSupport α x f)‖ ≤
      ‖x‖ * ‖compactSupportInclusion μ f‖ :=
  pointwiseCompactSupport_l2Bound (fun s => (α s⁻¹ x : H →L[ℂ] H))
    (continuous_regularCoefficientField α x) μ ‖x‖ (regularCoefficientField_norm_le α x) f

omit [LocallyCompactSpace G] in
/-- **Coefficient extension from the separated compact-support completion.** Let `G` be a
group with a topology, `H` a complete complex Hilbert space, `M⊆B(H)` a concrete von
Neumann algebra, and `α` a normal action with norm-continuous inverse predual orbits.
Assume `G` is a topological group. Give `G` its Borel structure and let `μ` be a regular
measure. Write `i_μ : C_c(G,H) → Lp H 2 μ` for the compact-support inclusion. let `C_μ` be
the completion of `C_c(G,H)` after quotienting by the zero L²-seminorm vectors.
`regularCoefficientSourceMap μ α x : C_μ →L[ℂ] Lp H 2 μ` sends the dense image of `f` to
`i_μ(s ↦ α_(s⁻¹)(x)f(s))`. -/
def regularCoefficientSourceMap (α : NormalAction G M) (x : M) :
    CompletionCore (H := H) μ →L[ℂ] Lp H 2 μ :=
  pointwiseSourceMap (fun s => (α s⁻¹ x : H →L[ℂ] H))
    (continuous_regularCoefficientField α x) μ ‖x‖ (regularCoefficientField_norm_le α x)

omit [LocallyCompactSpace G] in
/-- **Dense compact-support value of the source completion map.** Let `G` be a group with a
topology, `H` a complete complex Hilbert space, `M⊆B(H)` a concrete von Neumann algebra,
and `α` a normal action with norm-continuous inverse predual orbits. Assume `G` is a
topological group. Give `G` its Borel structure and let `μ` be a regular measure. Write
`i_μ : C_c(G,H) → Lp H 2 μ` for the compact-support inclusion. for `C_μ` the separated L²
completion and its inclusion `j_μ`, `regularCoefficientSourceMap μ α x (j_μ
f)=i_μ(regularCoefficientCompactSupport α x f)`. -/
theorem regularCoefficientSourceMap_apply (α : NormalAction G M) (x : M) (f : C_c(G, H)) :
    regularCoefficientSourceMap μ α x (toCompletion μ f) =
      compactSupportInclusion μ (regularCoefficientCompactSupport α x f) :=
  pointwiseSourceMap_apply (fun s => (α s⁻¹ x : H →L[ℂ] H))
    (continuous_regularCoefficientField α x) μ ‖x‖ (regularCoefficientField_norm_le α x) f

/-- **Bounded regular coefficient on full L².** Let `G` be a group with a topology, `H` a
complete complex Hilbert space, `M⊆B(H)` a concrete von Neumann algebra, and `α` a normal
action with norm-continuous inverse predual orbits. Assume `G` is a topological group.
Assume `G` is locally compact with its Borel measurable structure, and `μ` is a regular
measure. On `L=Lp H 2 μ`, put `P_x ξ =ᵐ[μ] (s ↦ α_(s⁻¹)(x)ξ(s))`. Haar invariance is not
assumed. `regularCoefficient μ α x=P_x : L →L[ℂ] L` is the operator with almost-everywhere
formula `P_x ξ =ᵐ[μ] (s ↦ α_(s⁻¹)(x)ξ(s))`.

Here `=ᵐ[μ]` denotes equality of measurable representatives μ-almost everywhere, not point
evaluation of an L² class. Operator identities are equalities of bounded operators. -/
def regularCoefficient (α : NormalAction G M) (x : M) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  pointwiseOperator (fun s => (α s⁻¹ x : H →L[ℂ] H))
    (continuous_regularCoefficientField α x) μ ‖x‖ (regularCoefficientField_norm_le α x)

/-- **Regular coefficient preserves the compact-support inclusion formula.** Let `G` be a
group with a topology, `H` a complete complex Hilbert space, `M⊆B(H)` a concrete von
Neumann algebra, and `α` a normal action with norm-continuous inverse predual orbits.
Assume `G` is a topological group. Assume `G` is locally compact with its Borel measurable
structure, and `μ` is a regular measure. On `L=Lp H 2 μ`, put `P_x ξ =ᵐ[μ] (s ↦
α_(s⁻¹)(x)ξ(s))`. Haar invariance is not assumed. for `f∈C_c(G,H)`, `P_x(i_μ f)=i_μ(s ↦
α_(s⁻¹)(x)f(s))`, where `i_μ` is the L² inclusion.

Here `=ᵐ[μ]` denotes equality of measurable representatives μ-almost everywhere, not point
evaluation of an L² class. Operator identities are equalities of bounded operators. -/
theorem regularCoefficient_apply_compactSupport (α : NormalAction G M) (x : M)
    (f : C_c(G, H)) :
    regularCoefficient μ α x (compactSupportInclusion μ f) =
      compactSupportInclusion μ (regularCoefficientCompactSupport α x f) :=
  pointwiseOperator_apply_compactSupport (fun s => (α s⁻¹ x : H →L[ℂ] H))
    (continuous_regularCoefficientField α x) μ ‖x‖ (regularCoefficientField_norm_le α x) f

/-- **Almost-everywhere representative of every regular coefficient value.** Let `G` be a
group with a topology, `H` a complete complex Hilbert space, `M⊆B(H)` a concrete von
Neumann algebra, and `α` a normal action with norm-continuous inverse predual orbits.
Assume `G` is a topological group. Assume `G` is locally compact with its Borel measurable
structure, and `μ` is a regular measure. On `L=Lp H 2 μ`, put `P_x ξ =ᵐ[μ] (s ↦
α_(s⁻¹)(x)ξ(s))`. Haar invariance is not assumed. for `x∈M` and `ξ∈L`, `regularCoefficient
μ α x ξ =ᵐ[μ] (s ↦ α_(s⁻¹)(x)ξ(s))`.

Here `=ᵐ[μ]` denotes equality of measurable representatives μ-almost everywhere, not point
evaluation of an L² class. Operator identities are equalities of bounded operators. -/
theorem regularCoefficient_ae_eq (α : NormalAction G M) (x : M) (ξ : Lp H 2 μ) :
    regularCoefficient μ α x ξ =ᵐ[μ] fun s : G => (α s⁻¹ x : H →L[ℂ] H) (ξ s) :=
  pointwiseOperator_ae_eq (fun s => (α s⁻¹ x : H →L[ℂ] H))
    (continuous_regularCoefficientField α x) μ ‖x‖ (regularCoefficientField_norm_le α x) ξ

/-- **Vector norm bound of a regular coefficient operator.** Let `G` be a group with a
topology, `H` a complete complex Hilbert space, `M⊆B(H)` a concrete von Neumann algebra,
and `α` a normal action with norm-continuous inverse predual orbits. Assume `G` is a
topological group. Assume `G` is locally compact with its Borel measurable structure, and
`μ` is a regular measure. On `L=Lp H 2 μ`, put `P_x ξ =ᵐ[μ] (s ↦ α_(s⁻¹)(x)ξ(s))`. Haar
invariance is not assumed. for `x∈M` and `ξ∈L`, `‖P_xξ‖≤‖x‖‖ξ‖`.

Here `=ᵐ[μ]` denotes equality of measurable representatives μ-almost everywhere, not point
evaluation of an L² class. Operator identities are equalities of bounded operators. -/
theorem regularCoefficient_norm_apply_le (α : NormalAction G M) (x : M) (ξ : Lp H 2 μ) :
    ‖regularCoefficient μ α x ξ‖ ≤ ‖x‖ * ‖ξ‖ :=
  pointwiseOperator_norm_apply_le (fun s => (α s⁻¹ x : H →L[ℂ] H))
    (continuous_regularCoefficientField α x) μ ‖x‖ (regularCoefficientField_norm_le α x) ξ

/-- **Coefficient operator on the separated compact-support Hilbert completion.** Let `G` be a
group with a topology, `H` a complete complex Hilbert space, `M⊆B(H)` a concrete von
Neumann algebra, and `α` a normal action with norm-continuous inverse predual orbits.
Assume `G` is a topological group. Assume `G` is locally compact with its Borel measurable
structure, and `μ` is a regular measure. On `L=Lp H 2 μ`, put `P_x ξ =ᵐ[μ] (s ↦
α_(s⁻¹)(x)ξ(s))`. Haar invariance is not assumed. let `C_μ` be the separated L² completion
of `C_c(G,H)` and `J : C_μ ≃ₗᵢ[ℂ] L` its L² identification. Then
`regularCoefficientOriginal μ α x=J⁻¹ P_x J`.

Here `=ᵐ[μ]` denotes equality of measurable representatives μ-almost everywhere, not point
evaluation of an L² class. Operator identities are equalities of bounded operators. -/
def regularCoefficientOriginal (α : NormalAction G M) (x : M) :
    CompletionCore (H := H) μ →L[ℂ] CompletionCore (H := H) μ :=
  (completionToLp (H := H) μ).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((regularCoefficient μ α x).comp
      (completionToLp (H := H) μ).toLinearIsometry.toContinuousLinearMap)

/-- **Dense value of the coefficient operator on its compact-support completion.** Let `G` be
a group with a topology, `H` a complete complex Hilbert space, `M⊆B(H)` a concrete von
Neumann algebra, and `α` a normal action with norm-continuous inverse predual orbits.
Assume `G` is a topological group. Assume `G` is locally compact with its Borel measurable
structure, and `μ` is a regular measure. On `L=Lp H 2 μ`, put `P_x ξ =ᵐ[μ] (s ↦
α_(s⁻¹)(x)ξ(s))`. Haar invariance is not assumed. for `C_μ` the separated L² completion
with dense map `j_μ`, `regularCoefficientOriginal μ α x (j_μ
f)=j_μ(regularCoefficientCompactSupport α x f)` for `f∈C_c(G,H)`.

Here `=ᵐ[μ]` denotes equality of measurable representatives μ-almost everywhere, not point
evaluation of an L² class. Operator identities are equalities of bounded operators. -/
theorem regularCoefficientOriginal_apply (α : NormalAction G M) (x : M) (f : C_c(G, H)) :
    regularCoefficientOriginal μ α x (toCompletion μ f) =
      toCompletion μ (regularCoefficientCompactSupport α x f) := by
  change (completionToLp (H := H) μ).symm
      (regularCoefficient μ α x ((completionToLp (H := H) μ) (toCompletion μ f))) = _
  rw [completionToLp_apply, regularCoefficient_apply_compactSupport,
    ← completionToLp_apply μ (regularCoefficientCompactSupport α x f),
    LinearIsometryEquiv.symm_apply_apply]

end

end NormalAction
end VonNeumannAlgebra
