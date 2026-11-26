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
# Faithfulness of Haar regular coefficient maps

For a normal action `α` on a concrete von Neumann algebra and regular Haar measure `μ`, the
regular coefficient map `x ↦ P_x` on `Lp H 2 μ` is injective.

Its tensor transport `x ↦ Q_x` and normal map into `M ⊗̄ B(Lp ℂ 2 μ)` are likewise injective. No
faithfulness of the group action itself or nonzero Hilbert space is required.
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

/-- **Injective Haar regular coefficient star representation.** Let `G` be a group with a
topology, `H` a complete complex Hilbert space, `M⊆B(H)` a concrete von Neumann algebra,
and `α` a normal action with norm-continuous inverse predual orbits. Assume `G` is a
topological group. Assume `G` is locally compact with its Borel measurable structure, and
`μ` is a regular measure. On `L=Lp H 2 μ`, put `P_x ξ =ᵐ[μ] (s ↦ α_(s⁻¹)(x)ξ(s))`. Haar
invariance is not assumed. Assume additionally that `μ` is a Haar measure.
`regularCoefficientHom μ α : M → B(L)` is injective.

Here `=ᵐ[μ]` denotes equality of measurable representatives μ-almost everywhere, not point
evaluation of an L² class. Operator identities are equalities of bounded operators. -/
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

/-- **Injective Hilbert-first Haar tensor coefficient representation.** Let `G` be a group
with a topology, `H` a complete complex Hilbert space, `M⊆B(H)` a concrete von Neumann
algebra, and `α` a normal action with norm-continuous inverse predual orbits. Assume `G`
is a topological group. Assume `G` is locally compact with its Borel measurable structure,
and `μ` is a regular measure. On `L=Lp H 2 μ`, put `P_x ξ =ᵐ[μ] (s ↦ α_(s⁻¹)(x)ξ(s))`.
Haar invariance is not assumed. Let `T=Completion(H ⊗[ℂ] Lp ℂ 2 μ)` and `U : T ≃ₗᵢ[ℂ] L`
be `tensorToLpRight μ`, with `U(ξ⊗f) =ᵐ[μ] (s ↦ f(s) • ξ)`. Set `Q_x=U⁻¹ P_x U`. Assume
additionally that `μ` is a Haar measure. `regularCoefficientTensorHom μ α : M → B(T)` is
injective because it is the unitary transport of the faithful regular coefficient map.

Here `=ᵐ[μ]` denotes equality of measurable representatives μ-almost everywhere, not point
evaluation of an L² class. Operator identities are equalities of bounded operators. -/
theorem regularCoefficientTensor_injective (α : NormalAction G M) :
    Function.Injective (regularCoefficientTensorHom μ α) := by
  let Φ := L2.tensorToLpRight (𝕜 := ℂ) (H := H) μ
  intro x y hxy
  apply regularCoefficient_injective μ α
  have hConj : Φ.symm.conjStarAlgEquiv (regularCoefficientHom μ α x) =
      Φ.symm.conjStarAlgEquiv (regularCoefficientHom μ α y) := hxy
  exact Φ.symm.conjStarAlgEquiv.injective hConj

/-- **Faithful normal Haar coefficient map in its spatial ambient.** Let `G` be a group with a
topology, `H` a complete complex Hilbert space, `M⊆B(H)` a concrete von Neumann algebra,
and `α` a normal action with norm-continuous inverse predual orbits. Assume `G` is a
topological group. Assume `G` is locally compact with its Borel measurable structure, and
`μ` is a regular measure. On `L=Lp H 2 μ`, put `P_x ξ =ᵐ[μ] (s ↦ α_(s⁻¹)(x)ξ(s))`. Haar
invariance is not assumed. Let `T=Completion(H ⊗[ℂ] Lp ℂ 2 μ)` and `U : T ≃ₗᵢ[ℂ] L` be
`tensorToLpRight μ`, with `U(ξ⊗f) =ᵐ[μ] (s ↦ f(s) • ξ)`. Set `Q_x=U⁻¹ P_x U`. Assume
additionally that `μ` is a Haar measure. the normal homomorphism
`regularCoefficientSpatialNormalHom μ α : M → M ⊗̄ B(Lp ℂ 2 μ)` is injective.

Here `=ᵐ[μ]` denotes equality of measurable representatives μ-almost everywhere, not point
evaluation of an L² class. Operator identities are equalities of bounded operators. -/
theorem regularCoefficientSpatialNormalHom_injective (α : NormalAction G M) :
    Function.Injective (regularCoefficientSpatialNormalHom μ α) := by
  intro x y hxy
  apply regularCoefficientTensor_injective μ α
  exact congrArg (fun z : spatialTensorProduct M (⊤ : VonNeumannAlgebra (Lp ℂ 2 μ)) =>
    (z : UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
      UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)))) hxy

end

end VonNeumannAlgebra.NormalAction
