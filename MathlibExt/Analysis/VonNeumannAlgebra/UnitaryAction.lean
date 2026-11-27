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

public import MathlibExt.Analysis.VonNeumannAlgebra.UnitaryConjugation
public import MathlibExt.Analysis.VonNeumannAlgebra.NormalAction
public import MathlibExt.Analysis.CStarAlgebra.PointNormAction.CovariantRepresentation
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Normal action of a strongly continuous normalizing representation

Let `G` be a group with a topology, `H` a complete complex Hilbert space and `ρ : G → U(H)`
strongly continuous. Suppose each `ρ_g` normalizes a concrete von Neumann algebra `M`, so `ρ_g M
ρ_g*=M`.

Conjugation gives the normal action `α_g(x)=ρ_g x ρ_g*`. Its inverse predual action takes the
vector functional `ω_(ξ,η)` to `ω_(ρ_g ξ,ρ_g η)`. These vector orbits and then all
normal-functional orbits are norm-continuous in `M_*`. Continuity of the group operations is not
an additional hypothesis.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace CStarAlgebra UniformConvergence

namespace VonNeumannAlgebra

noncomputable section

universe uG uH

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (M : VonNeumannAlgebra H) (ρ : StronglyContinuousUnitaryRepresentation G H)
variable (hEq : ∀ g : G,
  (fun T : H →L[ℂ] H => (ρ g : H →L[ℂ] H) * T * star (ρ g : H →L[ℂ] H)) ''
    (M : Set (H →L[ℂ] H)) = (M : Set (H →L[ℂ] H)))

/-- **Normal-automorphism homomorphism of a unitary representation.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. Let `M_*` be their norm-closed complex
span in the continuous dual `M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`,
induced by `x ↦ φ(x)` for `φ ∈ M_*`. Let `G` be a group with a topology and `ρ : G → U(H)`
a strongly continuous unitary representation satisfying `ρ_g M ρ_g*=M` for every `g`.
`unitaryConjugationNormalHom M ρ : G → Aut_normal(M)` is `g ↦ (x ↦ ρ_g x ρ_g*)`. -/
def unitaryConjugationNormalHom : G →* NormalStarAlgEquiv M M where
  toFun g := unitaryConjugationNormalEquivOfEq M (ρ g) (hEq g)
  map_one' := by
    apply NormalStarAlgEquiv.ext
    apply StarAlgEquiv.ext
    intro x
    apply Subtype.ext
    change (unitaryConjugationNormalEquivOfEq M (ρ 1) (hEq 1) x : H →L[ℂ] H) =
      (x : H →L[ℂ] H)
    rw [unitaryConjugationNormalEquivOfEq_apply]
    have hU := ρ.toMonoidHom.map_one
    change ρ 1 = (1 : unitary (H →L[ℂ] H)) at hU
    rw [hU]
    simp only [Submonoid.coe_one, star_one, one_mul, mul_one]
  map_mul' g h := by
    apply NormalStarAlgEquiv.ext
    apply StarAlgEquiv.ext
    intro x
    apply Subtype.ext
    change (unitaryConjugationNormalEquivOfEq M (ρ (g * h)) (hEq (g * h)) x : H →L[ℂ] H) =
      (unitaryConjugationNormalEquivOfEq M (ρ g) (hEq g)
        (unitaryConjugationNormalEquivOfEq M (ρ h) (hEq h) x) : H →L[ℂ] H)
    simp only [unitaryConjugationNormalEquivOfEq_apply]
    have hU := ρ.toMonoidHom.map_mul g h
    change ρ (g * h) = ρ g * ρ h at hU
    rw [hU]
    simp only [Submonoid.coe_mul, star_mul, mul_assoc]

/-- **Operator value of the representation's normal automorphism.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. Let `M_*` be their norm-closed complex
span in the continuous dual `M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`,
induced by `x ↦ φ(x)` for `φ ∈ M_*`. Let `G` be a group with a topology and `ρ : G → U(H)`
a strongly continuous unitary representation satisfying `ρ_g M ρ_g*=M` for every `g`. for
`g ∈ G` and `x ∈ M`, `unitaryConjugationNormalHom M ρ g x` has bounded-operator value `ρ_g
x ρ_g*`. -/
@[simp]
theorem unitaryConjugationNormalHom_apply (g : G) (x : M) :
    (unitaryConjugationNormalHom M ρ hEq g x : H →L[ℂ] H) =
      (ρ g : H →L[ℂ] H) * (x : H →L[ℂ] H) * star (ρ g : H →L[ℂ] H) :=
  rfl

/-- **Covariant predual action on a vector functional.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its
vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. Let `G` be a group with a topology and `ρ : G → U(H)` a strongly continuous unitary
representation satisfying `ρ_g M ρ_g*=M` for every `g`. for `g ∈ G` and `ξ,η ∈ H`,
inverse-automorphism pullback sends `ω_(ξ,η)` to `ω_(ρ_g ξ,ρ_g η)`, that is,
`ω_(ξ,η)∘α_g⁻¹=ω_(ρ_g ξ,ρ_g η)`. -/
theorem unitaryConjugation_predual_vectorFunctional (g : G) (ξ η : H) :
    (NormalStarAlgEquiv.predualActionHom M (unitaryConjugationNormalHom M ρ hEq g)
      ⟨vectorFunctional M ξ η, vectorFunctional_mem_normalFunctionalSpace M ξ η⟩ : StrongDual ℂ M) =
      vectorFunctional M ((ρ g : H →L[ℂ] H) ξ) ((ρ g : H →L[ℂ] H) η) := by
  let α := unitaryConjugationNormalHom M ρ hEq
  have hinv : (α g).symm = α g⁻¹ := by
    change (α g)⁻¹ = α g⁻¹
    exact (α.map_inv g).symm
  apply ContinuousLinearMap.ext
  intro x
  rw [NormalStarAlgEquiv.predualActionHom_apply, hinv]
  simp only [vectorFunctional_apply]
  change ⟪ξ, (unitaryConjugationNormalHom M ρ hEq g⁻¹ x : H →L[ℂ] H) η⟫_ℂ =
    ⟪(ρ g : H →L[ℂ] H) ξ, (x : H →L[ℂ] H) ((ρ g : H →L[ℂ] H) η)⟫_ℂ
  rw [unitaryConjugationNormalHom_apply]
  have hU := ρ.toMonoidHom.map_inv g
  change ρ g⁻¹ = star (ρ g) at hU
  rw [hU]
  simp only [Unitary.coe_star, star_star]
  change ⟪ξ, (star (ρ g) : H →L[ℂ] H)
      ((x : H →L[ℂ] H) ((ρ g : H →L[ℂ] H) η))⟫_ℂ =
    ⟪(ρ g : H →L[ℂ] H) ξ, (x : H →L[ℂ] H) ((ρ g : H →L[ℂ] H) η)⟫_ℂ
  calc
    _ = ⟪(star (star (ρ g)) : H →L[ℂ] H) ξ,
        (x : H →L[ℂ] H) ((ρ g : H →L[ℂ] H) η)⟫_ℂ :=
      (ContinuousLinearMap.adjoint_inner_left (star (ρ g) : H →L[ℂ] H)
        ((x : H →L[ℂ] H) ((ρ g : H →L[ℂ] H) η)) ξ).symm
    _ = _ := by rw [star_star]

/-- **Norm continuity of the unitary action on normal functionals.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. Let `M_*` be their norm-closed complex
span in the continuous dual `M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`,
induced by `x ↦ φ(x)` for `φ ∈ M_*`. Let `G` be a group with a topology and `ρ : G → U(H)`
a strongly continuous unitary representation satisfying `ρ_g M ρ_g*=M` for every `g`. for
every `φ ∈ M_*`, the inverse orbit `g ↦ φ∘(x ↦ ρ_g x ρ_g*)⁻¹` is continuous in the Banach
norm of `M_*`. -/
theorem unitaryConjugation_predual_continuous (φ : normalFunctionalSpace M) :
    Continuous fun g : G =>
      NormalStarAlgEquiv.predualActionHom M (unitaryConjugationNormalHom M ρ hEq g) φ := by
  let α := unitaryConjugationNormalHom M ρ hEq
  let A : G → StrongDual ℂ M →L[ℂ] StrongDual ℂ M := fun g =>
    (ContinuousLinearMap.compL ℂ M M ℂ).flip (α g).symm.toNormalStarAlgHom.toContinuousLinearMap
  have hbound (g : G) (ψ : StrongDual ℂ M) : ‖A g ψ‖ ≤ ‖ψ‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg ψ)
    intro x
    change ‖ψ ((α g).symm x)‖ ≤ ‖ψ‖ * ‖x‖
    calc
      _ ≤ ‖ψ‖ * ‖(α g).symm x‖ := ψ.le_opNorm _
      _ ≤ ‖ψ‖ * ‖x‖ := mul_le_mul_of_nonneg_left
        (NonUnitalStarAlgHom.norm_apply_le (α g).symm.toNormalStarAlgHom.toStarAlgHom x)
        (norm_nonneg ψ)
  have hLip (g : G) : LipschitzWith 1 (A g) := by
    apply LipschitzWith.mk_one
    intro ψ θ
    simp only [dist_eq_norm]
    rw [← map_sub]
    exact hbound g (ψ - θ)
  let P : Submodule ℂ (StrongDual ℂ M) :=
    { carrier := {ψ | Continuous fun g : G => A g ψ}
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, map_zero]
        exact continuous_const
      add_mem' := by
        intro ψ θ hψ hθ
        have hcψ : Continuous fun g : G => A g ψ := hψ
        have hcθ : Continuous fun g : G => A g θ := hθ
        simp only [Set.mem_ofPred_eq]
        have hfun : (fun g : G => A g (ψ + θ)) =
            (fun g : G => A g ψ) + (fun g : G => A g θ) := by
          funext g
          rw [Pi.add_apply]
          exact map_add (A g) ψ θ
        rw [hfun]
        exact hcψ.add hcθ
      smul_mem' := by
        intro c ψ hψ
        have hcψ : Continuous fun g : G => A g ψ := hψ
        simp only [Set.mem_ofPred_eq]
        have hfun : (fun g : G => A g (c • ψ)) =
            (fun _ : G => c) • (fun g : G => A g ψ) := by
          funext g
          rw [Pi.smul_apply']
          exact map_smul (A g) c ψ
        rw [hfun]
        exact (continuous_const : Continuous fun _ : G => c).smul hcψ }
  have hOrbitLip : LipschitzWith 1
      (fun ψ : StrongDual ℂ M => UniformFun.ofFun (fun g : G => A g ψ)) :=
    UniformFun.lipschitzWith_ofFun_iff.mpr hLip
  have hPclosed : IsClosed (P : Set (StrongDual ℂ M)) := by
    change IsClosed ((fun ψ : StrongDual ℂ M => UniformFun.ofFun (fun g : G => A g ψ)) ⁻¹'
      {f : G →ᵤ StrongDual ℂ M | Continuous (UniformFun.toFun f)})
    exact (UniformFun.isClosed_setOfPred_continuous (α := G) (β := StrongDual ℂ M)).preimage
      hOrbitLip.continuous
  let R₀ : M →ₗ[ℂ] (H →L[ℂ] H) := LinearMap.ofClass M.toStarSubalgebra.subtype
  let R : M →L[ℂ] (H →L[ℂ] H) := R₀.mkContinuous 1 (by
    intro x
    change ‖(x : H →L[ℂ] H)‖ ≤ 1 * ‖x‖
    rw [one_mul]
    exact le_rfl)
  let E : H →L[ℂ] (H →L[ℂ] H) →L[ℂ] H := ContinuousLinearMap.apply ℂ H
  let J : H →L[ℂ] M →L[ℂ] H := (E.flip.comp R).flip
  let B : H →L⋆[ℂ] H →L[ℂ] StrongDual ℂ M :=
    ContinuousLinearMap.bilinearComp (ContinuousLinearMap.compL ℂ M H ℂ) (innerSL ℂ) J
  have hR (x : M) : R x = (x : H →L[ℂ] H) := by
    dsimp only [R]
    rw [LinearMap.mkContinuous_apply]
    rfl
  have hE (ξ : H) (T : H →L[ℂ] H) : E ξ T = T ξ := by
    dsimp only [E]
    exact ContinuousLinearMap.apply_apply ξ T
  have hJ (ξ : H) (x : M) : J ξ x = (R x) ξ := by
    dsimp only [J]
    rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply]
    exact hE ξ (R x)
  have hEval (ξ η : H) (x : M) : B ξ η x = ⟪ξ, (x : H →L[ℂ] H) η⟫_ℂ := by
    calc
      B ξ η x = innerSL ℂ ξ (J η x) := by
        simp only [B, ContinuousLinearMap.bilinearComp_apply,
          ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply]
      _ = ⟪ξ, (R x) η⟫_ℂ := by rw [hJ, innerSL_apply_apply]
      _ = ⟪ξ, (x : H →L[ℂ] H) η⟫_ℂ := by rw [hR]
  have hB (ξ η : H) : B ξ η = vectorFunctional M ξ η := by
    apply ContinuousLinearMap.ext
    intro x
    exact (hEval ξ η x).trans (vectorFunctional_apply M ξ η x).symm
  have hvec (ξ η : H) : vectorFunctional M ξ η ∈ P := by
    change Continuous fun g : G => A g (vectorFunctional M ξ η)
    have he (g : G) : A g (vectorFunctional M ξ η) =
        B ((ρ g : H →L[ℂ] H) ξ) ((ρ g : H →L[ℂ] H) η) := by
      have h := unitaryConjugation_predual_vectorFunctional M ρ hEq g ξ η
      change A g (vectorFunctional M ξ η) =
        vectorFunctional M ((ρ g : H →L[ℂ] H) ξ) ((ρ g : H →L[ℂ] H) η) at h
      exact h.trans (hB ((ρ g : H →L[ℂ] H) ξ) ((ρ g : H →L[ℂ] H) η)).symm
    have hfun : (fun g : G => A g (vectorFunctional M ξ η)) =
        (fun g : G => B ((ρ g : H →L[ℂ] H) ξ) ((ρ g : H →L[ℂ] H) η)) := by
      funext g
      exact he g
    rw [hfun]
    exact (B.continuous.comp (ρ.continuous_orbit ξ)).clm_apply (ρ.continuous_orbit η)
  have hAll := normalFunctionalSpace_le M hPclosed hvec
  apply continuous_induced_rng.2
  change Continuous fun g : G => A g (φ : StrongDual ℂ M)
  exact hAll φ.property

/-- **Normal action induced by unitary normalization.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its
vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. Let `G` be a group with a topology and `ρ : G → U(H)` a strongly continuous unitary
representation satisfying `ρ_g M ρ_g*=M` for every `g`. `unitaryConjugationNormalAction M
ρ : NormalAction G M` has primal action `α_g(x)=ρ_g x ρ_g*` and norm-continuous predual
action `φ ↦ φ∘α_g⁻¹`. -/
def unitaryConjugationNormalAction : NormalAction G M where
  toMonoidHom := unitaryConjugationNormalHom M ρ hEq
  continuous_predual_orbit := unitaryConjugation_predual_continuous M ρ hEq

end

end VonNeumannAlgebra
