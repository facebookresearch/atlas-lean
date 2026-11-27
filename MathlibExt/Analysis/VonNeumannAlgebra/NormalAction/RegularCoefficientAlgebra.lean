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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalAction.RegularCoefficient
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Star-algebra laws and Haar covariance of regular coefficients

For a normal action on `M`, the regular-measure coefficient operators `P_x ξ =ᵐ[μ] (s ↦
α_(s⁻¹)(x)ξ(s))` satisfy `P_(x+y)=P_x+P_y`, `P_(cx)=cP_x`, `P_(xy)=P_xP_y`, `P_1=I` and
`P_(x*)=P_x*`. Thus `x ↦ P_x` is a unital complex star homomorphism on full `Lp H 2 μ`.

For a regular Haar measure, left translations additionally satisfy `λ_g P_x λ_g*=P_(α_g(x))`.
Haar invariance is needed for this covariance, but not for the preceding algebra laws.

Here `=ᵐ[μ]` denotes equality of measurable representatives μ-almost everywhere, not point
evaluation of an L² class. Operator identities are equalities of bounded operators.
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
variable (μ : Measure G) [μ.Regular]

/-- **Additivity of regular coefficient operators.** Let `G` be a group with a topology, `H` a
complete complex Hilbert space, `M⊆B(H)` a concrete von Neumann algebra, and `α` a normal
action with norm-continuous inverse predual orbits. Assume `G` is a topological group.
Assume `G` is locally compact with its Borel measurable structure, and `μ` is a regular
measure. On `L=Lp H 2 μ`, put `P_x ξ =ᵐ[μ] (s ↦ α_(s⁻¹)(x)ξ(s))`. Haar invariance is not
assumed. for `x,y∈M`, `P_(x+y)=P_x+P_y`.

Here `=ᵐ[μ]` denotes equality of measurable representatives μ-almost everywhere, not point
evaluation of an L² class. Operator identities are equalities of bounded operators. -/
theorem regularCoefficient_add (α : NormalAction G M) (x y : M) :
    regularCoefficient μ α (x + y) = regularCoefficient μ α x + regularCoefficient μ α y := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [regularCoefficient_ae_eq μ α (x + y) ξ,
    regularCoefficient_ae_eq μ α x ξ, regularCoefficient_ae_eq μ α y ξ,
    Lp.coeFn_add (regularCoefficient μ α x ξ) (regularCoefficient μ α y ξ)] with s h₁ h₂ h₃ h₄
  change regularCoefficient μ α (x + y) ξ s =
    (regularCoefficient μ α x ξ + regularCoefficient μ α y ξ) s
  rw [h₁, h₄]
  change (α s⁻¹ (x + y) : H →L[ℂ] H) (ξ s) =
    regularCoefficient μ α x ξ s + regularCoefficient μ α y ξ s
  rw [h₂, h₃, map_add]
  rfl

/-- **Complex scaling of regular coefficient operators.** Let `G` be a group with a topology,
`H` a complete complex Hilbert space, `M⊆B(H)` a concrete von Neumann algebra, and `α` a
normal action with norm-continuous inverse predual orbits. Assume `G` is a topological
group. Assume `G` is locally compact with its Borel measurable structure, and `μ` is a
regular measure. On `L=Lp H 2 μ`, put `P_x ξ =ᵐ[μ] (s ↦ α_(s⁻¹)(x)ξ(s))`. Haar invariance
is not assumed. for `c∈ℂ`, `x∈M`, `P_(c • x)=c • P_x`.

Here `=ᵐ[μ]` denotes equality of measurable representatives μ-almost everywhere, not point
evaluation of an L² class. Operator identities are equalities of bounded operators. -/
theorem regularCoefficient_smul (α : NormalAction G M) (c : ℂ) (x : M) :
    regularCoefficient μ α (c • x) = c • regularCoefficient μ α x := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [regularCoefficient_ae_eq μ α (c • x) ξ,
    regularCoefficient_ae_eq μ α x ξ,
    Lp.coeFn_smul c (regularCoefficient μ α x ξ)] with s h₁ h₂ h₃
  change regularCoefficient μ α (c • x) ξ s = (c • regularCoefficient μ α x ξ) s
  rw [h₁, h₃]
  change (α s⁻¹ (c • x) : H →L[ℂ] H) (ξ s) = c • regularCoefficient μ α x ξ s
  rw [h₂, map_smul]
  rfl

/-- **Multiplication of regular coefficient operators.** Let `G` be a group with a topology,
`H` a complete complex Hilbert space, `M⊆B(H)` a concrete von Neumann algebra, and `α` a
normal action with norm-continuous inverse predual orbits. Assume `G` is a topological
group. Assume `G` is locally compact with its Borel measurable structure, and `μ` is a
regular measure. On `L=Lp H 2 μ`, put `P_x ξ =ᵐ[μ] (s ↦ α_(s⁻¹)(x)ξ(s))`. Haar invariance
is not assumed. for `x,y∈M`, `P_(xy)=P_x P_y`.

Here `=ᵐ[μ]` denotes equality of measurable representatives μ-almost everywhere, not point
evaluation of an L² class. Operator identities are equalities of bounded operators. -/
theorem regularCoefficient_mul (α : NormalAction G M) (x y : M) :
    regularCoefficient μ α (x * y) = regularCoefficient μ α x * regularCoefficient μ α y := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [regularCoefficient_ae_eq μ α (x * y) ξ,
    regularCoefficient_ae_eq μ α x (regularCoefficient μ α y ξ),
    regularCoefficient_ae_eq μ α y ξ] with s h₁ h₂ h₃
  change regularCoefficient μ α (x * y) ξ s =
    regularCoefficient μ α x (regularCoefficient μ α y ξ) s
  rw [h₁, h₂, h₃, map_mul]
  rfl

/-- **Unit coefficient is the L² identity.** Let `G` be a group with a topology, `H` a
complete complex Hilbert space, `M⊆B(H)` a concrete von Neumann algebra, and `α` a normal
action with norm-continuous inverse predual orbits. Assume `G` is a topological group.
Assume `G` is locally compact with its Borel measurable structure, and `μ` is a regular
measure. On `L=Lp H 2 μ`, put `P_x ξ =ᵐ[μ] (s ↦ α_(s⁻¹)(x)ξ(s))`. Haar invariance is not
assumed. `P_1=I_L`.

Here `=ᵐ[μ]` denotes equality of measurable representatives μ-almost everywhere, not point
evaluation of an L² class. Operator identities are equalities of bounded operators. -/
theorem regularCoefficient_one (α : NormalAction G M) :
    regularCoefficient μ α (1 : M) = 1 := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [regularCoefficient_ae_eq μ α (1 : M) ξ] with s hs
  change regularCoefficient μ α (1 : M) ξ s = ξ s
  rw [hs, map_one]
  rfl

/-- **Adjoint of a regular coefficient operator.** Let `G` be a group with a topology, `H` a
complete complex Hilbert space, `M⊆B(H)` a concrete von Neumann algebra, and `α` a normal
action with norm-continuous inverse predual orbits. Assume `G` is a topological group.
Assume `G` is locally compact with its Borel measurable structure, and `μ` is a regular
measure. On `L=Lp H 2 μ`, put `P_x ξ =ᵐ[μ] (s ↦ α_(s⁻¹)(x)ξ(s))`. Haar invariance is not
assumed. for `x∈M`, `P_(x*)=P_x*`.

Here `=ᵐ[μ]` denotes equality of measurable representatives μ-almost everywhere, not point
evaluation of an L² class. Operator identities are equalities of bounded operators. -/
theorem regularCoefficient_star (α : NormalAction G M) (x : M) :
    regularCoefficient μ α (star x) = star (regularCoefficient μ α x) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff
    (regularCoefficient μ α (star x)) (regularCoefficient μ α x)).mpr
  intro ξ η
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [regularCoefficient_ae_eq μ α (star x) ξ,
    regularCoefficient_ae_eq μ α x η] with s h₁ h₂
  rw [h₁, h₂, map_star]
  change ⟪star (α s⁻¹ x : H →L[ℂ] H) (ξ s), η s⟫_ℂ =
    ⟪ξ s, (α s⁻¹ x : H →L[ℂ] H) (η s)⟫_ℂ
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact ContinuousLinearMap.adjoint_inner_left (α s⁻¹ x : H →L[ℂ] H) (η s) (ξ s)

/-- **Adjoint pairing of compact-support regular coefficient vectors.** Let `G` be a group
with a topology, `H` a complete complex Hilbert space, `M⊆B(H)` a concrete von Neumann
algebra, and `α` a normal action with norm-continuous inverse predual orbits. Assume `G`
is a topological group. Assume `G` is locally compact with its Borel measurable structure,
and `μ` is a regular measure. On `L=Lp H 2 μ`, put `P_x ξ =ᵐ[μ] (s ↦ α_(s⁻¹)(x)ξ(s))`.
Haar invariance is not assumed. for `x∈M`, `f,g∈C_c(G,H)` and their L² inclusion `i_μ`,
`⟨P_x(i_μ f),i_μ g⟩=⟨i_μ f,P_(x*)(i_μ g)⟩`.

Here `=ᵐ[μ]` denotes equality of measurable representatives μ-almost everywhere, not point
evaluation of an L² class. Operator identities are equalities of bounded operators. -/
theorem regularCoefficient_inner_compactSupport (α : NormalAction G M) (x : M)
    (f g : C_c(G, H)) :
    ⟪regularCoefficient μ α x (compactSupportInclusion μ f), compactSupportInclusion μ g⟫_ℂ =
      ⟪compactSupportInclusion μ f,
        regularCoefficient μ α (star x) (compactSupportInclusion μ g)⟫_ℂ := by
  rw [regularCoefficient_star, ContinuousLinearMap.star_eq_adjoint]
  exact (ContinuousLinearMap.adjoint_inner_right (regularCoefficient μ α x)
    (compactSupportInclusion μ f) (compactSupportInclusion μ g)).symm

/-- **Unital star homomorphism of regular coefficients.** Let `G` be a group with a topology,
`H` a complete complex Hilbert space, `M⊆B(H)` a concrete von Neumann algebra, and `α` a
normal action with norm-continuous inverse predual orbits. Assume `G` is a topological
group. Assume `G` is locally compact with its Borel measurable structure, and `μ` is a
regular measure. On `L=Lp H 2 μ`, put `P_x ξ =ᵐ[μ] (s ↦ α_(s⁻¹)(x)ξ(s))`. Haar invariance
is not assumed. `regularCoefficientHom μ α : M →⋆ₐ[ℂ] B(L)` sends `x` to `P_x`.

Here `=ᵐ[μ]` denotes equality of measurable representatives μ-almost everywhere, not point
evaluation of an L² class. Operator identities are equalities of bounded operators. -/
def regularCoefficientHom (α : NormalAction G M) : M →⋆ₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ) where
  toFun := regularCoefficient μ α
  map_one' := regularCoefficient_one μ α
  map_mul' := regularCoefficient_mul μ α
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro ξ
    apply Lp.ext
    filter_upwards [regularCoefficient_ae_eq μ α (0 : M) ξ,
      Lp.coeFn_zero H 2 μ] with s h₁ h₂
    change regularCoefficient μ α (0 : M) ξ s = (0 : Lp H 2 μ) s
    rw [h₁, h₂, map_zero]
    rfl
  map_add' := regularCoefficient_add μ α
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one,
      regularCoefficient_smul, regularCoefficient_one]
  map_star' := regularCoefficient_star μ α

variable [μ.IsHaarMeasure]

/-- **Haar translation covariance of the regular coefficient homomorphism.** Let `G` be a
group with a topology, `H` a complete complex Hilbert space, `M⊆B(H)` a concrete von
Neumann algebra, and `α` a normal action with norm-continuous inverse predual orbits.
Assume `G` is a topological group. Assume `G` is locally compact with its Borel measurable
structure, and `μ` is a regular measure. On `L=Lp H 2 μ`, put `P_x ξ =ᵐ[μ] (s ↦
α_(s⁻¹)(x)ξ(s))`. Haar invariance is not assumed. Assume additionally that `μ` is a Haar
measure. for `λ_g ξ =ᵐ[μ] (s ↦ ξ(g⁻¹s))`, `λ_g P_x λ_g*=P_(α_g(x))` for every `g∈G`,
`x∈M`.

Here `=ᵐ[μ]` denotes equality of measurable representatives μ-almost everywhere, not point
evaluation of an L² class. Operator identities are equalities of bounded operators. -/
theorem regularCoefficient_covariance (α : NormalAction G M) (g : G) (x : M) :
    (StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H g :
        Lp H 2 μ →L[ℂ] Lp H 2 μ) * regularCoefficient μ α x *
      star (StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H g :
        Lp H 2 μ →L[ℂ] Lp H 2 μ) = regularCoefficient μ α (α g x) := by
  rw [StronglyContinuousUnitaryRepresentation.star_haarLeftRegular]
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  let L (h : G) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
    StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H h
  let η := L g⁻¹ ξ
  have houter := StronglyContinuousUnitaryRepresentation.haarLeftRegular_ae_eq G μ H g
    (regularCoefficient μ α x η)
  have hcoefficient := regularCoefficient_ae_eq μ α x η
  have hinner := StronglyContinuousUnitaryRepresentation.haarLeftRegular_ae_eq G μ H g⁻¹ ξ
  have hpres : MeasurePreserving (fun s : G => g⁻¹ * s) μ μ := measurePreserving_smul g⁻¹ μ
  have hquasi : QuasiMeasurePreserving (fun s : G => g⁻¹ * s) μ μ :=
    hpres.quasiMeasurePreserving
  have hcoefficient' := hquasi.ae_eq_comp hcoefficient
  have hinner' := hquasi.ae_eq_comp hinner
  filter_upwards [houter, hcoefficient', hinner', regularCoefficient_ae_eq μ α (α g x) ξ]
    with s h₁ h₂ h₃ h₄
  change L g (regularCoefficient μ α x (L g⁻¹ ξ)) s = regularCoefficient μ α (α g x) ξ s
  simp only [Function.comp_apply] at h₂ h₃
  rw [h₁, h₂, h₃, h₄]
  simp only [mul_inv_rev, inv_inv, mul_inv_cancel_left]
  rw [map_mul, NormalStarAlgEquiv.mul_apply]

end

end NormalAction
end VonNeumannAlgebra
