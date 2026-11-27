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

public import MathlibExt.Analysis.VonNeumannAlgebra.Ultraweak
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Predual pullback and ultraweak continuity of star conjugation

For a concrete von Neumann algebra `M` and fixed `x ∈ M`, the bounded linear conjugation map is
`a ↦ x* a x`. Precomposition preserves the normal-functional Banach space `M_*` and gives the
bounded map `ψ ↦ (a ↦ ψ(x* a x))` on `M_*`.

On vector functionals, both vectors are multiplied by `x`. Consequently the conjugation map on
`M` is ultraweakly continuous. The coefficient `x` need not be unitary or invertible.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Predual pullback of a fixed star conjugation.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its
vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. for `x ∈ M`, `normalFunctionalConjugationPullback M x : M_* →L[ℂ] M_*` sends `ψ` to
the functional `a ↦ ψ(x* a x)`. -/
def normalFunctionalConjugationPullback (M : VonNeumannAlgebra H) (x : M) :
    normalFunctionalSpace M →L[ℂ] normalFunctionalSpace M := by
  let C : M →L[ℂ] M := ContinuousLinearMap.mulLeftRight ℂ M (star x) x
  let B : StrongDual ℂ M →L[ℂ] StrongDual ℂ M := (ContinuousLinearMap.compL ℂ M M ℂ).flip C
  let P : Submodule ℂ (StrongDual ℂ M) := (normalFunctionalSpace M).comap B.toLinearMap
  have hP : IsClosed (P : Set (StrongDual ℂ M)) := by
    change IsClosed (B ⁻¹' (normalFunctionalSpace M : Set (StrongDual ℂ M)))
    exact (normalFunctionalSpace_isClosed M).preimage B.continuous
  have hvec : ∀ ξ η : H, vectorFunctional M ξ η ∈ P := by
    intro ξ η
    change B (vectorFunctional M ξ η) ∈ normalFunctionalSpace M
    have hshift : B (vectorFunctional M ξ η) =
        vectorFunctional M ((x : H →L[ℂ] H) ξ) ((x : H →L[ℂ] H) η) := by
      apply ContinuousLinearMap.ext
      intro a
      change vectorFunctional M ξ η (star x * a * x) =
        vectorFunctional M ((x : H →L[ℂ] H) ξ) ((x : H →L[ℂ] H) η) a
      rw [vectorFunctional_apply, vectorFunctional_apply]
      change ⟪ξ, (star (x : H →L[ℂ] H) * (a : H →L[ℂ] H) * (x : H →L[ℂ] H)) η⟫_ℂ =
        ⟪(x : H →L[ℂ] H) ξ, (a : H →L[ℂ] H) ((x : H →L[ℂ] H) η)⟫_ℂ
      rw [mul_apply_eq_comp, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_right]
    rw [hshift]
    exact vectorFunctional_mem_normalFunctionalSpace M
      ((x : H →L[ℂ] H) ξ) ((x : H →L[ℂ] H) η)
  have hle : normalFunctionalSpace M ≤ P := normalFunctionalSpace_le M hP hvec
  let T := B.comp (normalFunctionalSpace M).subtypeL
  exact T.codRestrict (normalFunctionalSpace M) fun ψ => hle ψ.property

/-- **Value of the star-conjugation predual pullback.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its
vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. for `x,a ∈ M` and `ψ ∈ M_*`, `(normalFunctionalConjugationPullback M x ψ)(a)=ψ(x* a
x)`. -/
theorem normalFunctionalConjugationPullback_apply (M : VonNeumannAlgebra H) (x : M)
    (ψ : normalFunctionalSpace M) (a : M) :
    (normalFunctionalConjugationPullback M x ψ : StrongDual ℂ M) a =
      (ψ : StrongDual ℂ M) (star x * a * x) :=
  rfl

/-- **Ultraweak continuity of fixed star conjugation.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its
vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. for any fixed `x ∈ M`, the map `a ↦ x* a x` is ultraweakly continuous on `M`,
without unitarity or invertibility of `x`. -/
theorem ultraweak_starConjugation_continuous (M : VonNeumannAlgebra H) (x : M) :
    Continuous (fun a : Ultraweak M =>
      (ultraweakLinearEquiv M).symm (star x * ultraweakLinearEquiv M a * x)) := by
  apply (ultraweak_continuous_iff M).2
  intro ψ
  let ψx : normalFunctionalSpace M := normalFunctionalConjugationPullback M x ψ
  have hcontinuous := ultraweak_eval_continuous M ψx
  change Continuous (fun a : Ultraweak M =>
    (normalFunctionalConjugationPullback M x ψ : StrongDual ℂ M) (ultraweakLinearEquiv M a)) at hcontinuous
  change Continuous (fun a : Ultraweak M =>
    (ψ : StrongDual ℂ M) (star x * ultraweakLinearEquiv M a * x))
  simpa only [normalFunctionalConjugationPullback_apply] using hcontinuous

end

end VonNeumannAlgebra
