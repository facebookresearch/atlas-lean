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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalFunctional
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Isometric predual realization by normal vector functionals

For a concrete von Neumann algebra `M ⊆ B(H)` on a complete complex Hilbert space, let `M_*` be
the norm-closed complex span of vector functionals `ω_(ξ,η)(x)=⟨ξ,xη⟩`. Evaluation defines `J_M
: M → (M_*)*`, `J_M(x)(φ)=φ(x)`.

This map is a surjective linear isometry. A bounded functional `F` on `M_*` is represented by an
operator `T_F ∈ M` with `⟨ξ,T_F η⟩=F(ω_(ξ,η))` and `‖T_F‖≤‖F‖`.

Composing the inverse evaluation with the algebra involution gives the conjugate-linear
isometric equivalence `(M_*)* ≃ M` that witnesses the abstract W-star-algebra predual property.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace CStarAlgebra

namespace VonNeumannAlgebra

open MathlibExt.Analysis.CStarAlgebra

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Inherited normed additive group of normal functionals.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. the norm and additive operations on `M_*` are the restrictions of the
continuous-dual operator norm and operations on `M*`. -/
noncomputable instance normalFunctionalSpaceNormedAddCommGroup (M : VonNeumannAlgebra H) :
    NormedAddCommGroup (normalFunctionalSpace M) :=
  Submodule.normedAddCommGroup (𝕜 := ℂ) (E := StrongDual ℂ M) (normalFunctionalSpace M)

/-- **Inherited complex normed space of normal functionals.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. `M_*` is a complex normed space with the scalar action and operator norm inherited
from `M*`. -/
noncomputable instance normalFunctionalSpaceNormedSpace (M : VonNeumannAlgebra H) :
    NormedSpace ℂ (normalFunctionalSpace M) :=
  Submodule.normedSpace (𝕜 := ℂ) (R := ℂ) (E := StrongDual ℂ M) (normalFunctionalSpace M)

/-- **Vector coefficient as a normal-functional element.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. for `ξ,η ∈ H`, `normalVectorFunctional M ξ η` is the element `ω_(ξ,η)` of `M_*`,
with evaluation `x ↦ ⟨ξ,xη⟩`. -/
noncomputable def normalVectorFunctional (M : VonNeumannAlgebra H) (ξ η : H) :
    normalFunctionalSpace M :=
  ⟨vectorFunctional M ξ η, vectorFunctional_mem_normalFunctionalSpace M ξ η⟩

/-- **Bounded evaluation into the dual of normal functionals.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. `normalFunctionalEvaluation M : M →L[ℂ] (M_*)*` is `J_M(x)(φ)=φ(x)`. -/
noncomputable def normalFunctionalEvaluation (M : VonNeumannAlgebra H) :
    M →L[ℂ] StrongDual ℂ (normalFunctionalSpace M) :=
  let ev : M → StrongDual ℂ (normalFunctionalSpace M) := fun x =>
    let l : normalFunctionalSpace M →ₗ[ℂ] ℂ :=
      { toFun := fun φ => (φ : StrongDual ℂ M) x
        map_add' := by
          intro φ ψ
          change ((φ : StrongDual ℂ M) + (ψ : StrongDual ℂ M)) x =
            (φ : StrongDual ℂ M) x + (ψ : StrongDual ℂ M) x
          rw [add_apply]
        map_smul' := by
          intro c φ
          change (c • (φ : StrongDual ℂ M)) x =
            (RingHom.id ℂ) c • (φ : StrongDual ℂ M) x
          simp only [smul_apply, RingHom.id_apply] }
    l.mkContinuous ‖x‖ (by
      intro φ
      change ‖(φ : StrongDual ℂ M) x‖ ≤ ‖x‖ * ‖φ‖
      calc
        ‖(φ : StrongDual ℂ M) x‖ ≤ ‖φ‖ * ‖x‖ := (φ : StrongDual ℂ M).le_opNorm x
        _ = ‖x‖ * ‖φ‖ := mul_comm _ _)
  let f : M →ₗ[ℂ] StrongDual ℂ (normalFunctionalSpace M) :=
    { toFun := ev
      map_add' := by
        intro x y
        apply ContinuousLinearMap.ext
        intro φ
        change (φ : StrongDual ℂ M) (x + y) =
          (φ : StrongDual ℂ M) x + (φ : StrongDual ℂ M) y
        exact map_add (φ : StrongDual ℂ M) x y
      map_smul' := by
        intro c x
        apply ContinuousLinearMap.ext
        intro φ
        change (φ : StrongDual ℂ M) (c • x) =
          (RingHom.id ℂ) c • (φ : StrongDual ℂ M) x
        simp only [map_smul, RingHom.id_apply] }
  f.mkContinuous 1 (by
    intro x
    change ‖ev x‖ ≤ 1 * ‖x‖
    rw [one_mul]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x)
    intro φ
    change ‖(φ : StrongDual ℂ M) x‖ ≤ ‖x‖ * ‖φ‖
    calc
      ‖(φ : StrongDual ℂ M) x‖ ≤ ‖φ‖ * ‖x‖ := (φ : StrongDual ℂ M).le_opNorm x
      _ = ‖x‖ * ‖φ‖ := mul_comm _ _)

/-- **Value of normal-functional evaluation.** Let `H` be a complete complex Hilbert space and
`M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector
functionals. Let `M_*` be their norm-closed complex span in the continuous dual `M*`. for
`x ∈ M` and `φ ∈ M_*`, `normalFunctionalEvaluation M x φ=φ(x)`. -/
@[simp]
theorem normalFunctionalEvaluation_apply (M : VonNeumannAlgebra H) (x : M)
    (φ : normalFunctionalSpace M) :
    normalFunctionalEvaluation M x φ = (φ : StrongDual ℂ M) x :=
  rfl

/-- **Injectivity of evaluation against normal functionals.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. the map `J_M : x ↦ (φ ↦ φ(x))` is injective on `M`. -/
theorem normalFunctionalEvaluation_injective (M : VonNeumannAlgebra H) :
    Function.Injective (normalFunctionalEvaluation M) := by
  intro x y h
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro η
  apply ext_inner_left ℂ
  intro ξ
  have hc := congrArg
    (fun F : StrongDual ℂ (normalFunctionalSpace M) => F (normalVectorFunctional M ξ η)) h
  change vectorFunctional M ξ η x = vectorFunctional M ξ η y at hc
  simpa only [vectorFunctional_apply] using hc

/-- **Norm bound for a normal vector-functional element.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. for `ξ,η ∈ H`, `‖normalVectorFunctional M ξ η‖≤‖ξ‖‖η‖`. -/
private theorem normalVectorFunctional_norm_le (M : VonNeumannAlgebra H) (ξ η : H) :
    ‖normalVectorFunctional M ξ η‖ ≤ ‖ξ‖ * ‖η‖ :=
  norm_vectorFunctional_le M ξ η

/-- **Addition in the first vector-functional argument.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. for `ξ,ζ,η ∈ H`, `ω_(ξ+ζ,η)=ω_(ξ,η)+ω_(ζ,η)` as elements of `M_*`. -/
private theorem normalVectorFunctional_add_left (M : VonNeumannAlgebra H) (ξ ζ η : H) :
    normalVectorFunctional M (ξ + ζ) η =
      normalVectorFunctional M ξ η + normalVectorFunctional M ζ η := by
  apply Subtype.ext
  change vectorFunctional M (ξ + ζ) η = vectorFunctional M ξ η + vectorFunctional M ζ η
  simpa only [vectorFunctional] using
    representationCoefficient_add_right (A := M) M.toStarSubalgebra.subtype η ξ ζ

/-- **Conjugate scalar in the first vector-functional argument.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. Let `M_*` be their norm-closed complex
span in the continuous dual `M*`. for `c : ℂ`, `ξ,η ∈ H`, `ω_(cξ,η)=conj(c) ω_(ξ,η)` in
`M_*`. -/
private theorem normalVectorFunctional_smul_left (M : VonNeumannAlgebra H)
    (c : ℂ) (ξ η : H) :
    normalVectorFunctional M (c • ξ) η = star c • normalVectorFunctional M ξ η := by
  apply Subtype.ext
  change vectorFunctional M (c • ξ) η = star c • vectorFunctional M ξ η
  simpa only [vectorFunctional] using
    representationCoefficient_smul_right (A := M) M.toStarSubalgebra.subtype c η ξ

/-- **Addition in the second vector-functional argument.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. for `ξ,η,ζ ∈ H`, `ω_(ξ,η+ζ)=ω_(ξ,η)+ω_(ξ,ζ)` in `M_*`. -/
private theorem normalVectorFunctional_add_right (M : VonNeumannAlgebra H) (ξ η ζ : H) :
    normalVectorFunctional M ξ (η + ζ) =
      normalVectorFunctional M ξ η + normalVectorFunctional M ξ ζ := by
  apply Subtype.ext
  change vectorFunctional M ξ (η + ζ) = vectorFunctional M ξ η + vectorFunctional M ξ ζ
  simpa only [vectorFunctional] using
    representationCoefficient_add_left (A := M) M.toStarSubalgebra.subtype η ζ ξ

/-- **Linear scalar in the second vector-functional argument.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. for `c : ℂ`, `ξ,η ∈ H`, `ω_(ξ,cη)=c ω_(ξ,η)` in `M_*`. -/
private theorem normalVectorFunctional_smul_right (M : VonNeumannAlgebra H)
    (c : ℂ) (ξ η : H) :
    normalVectorFunctional M ξ (c • η) = c • normalVectorFunctional M ξ η := by
  apply Subtype.ext
  change vectorFunctional M ξ (c • η) = c • vectorFunctional M ξ η
  simpa only [vectorFunctional] using
    representationCoefficient_smul_left (A := M) M.toStarSubalgebra.subtype c η ξ

/-- **Fixed-vector Riesz functional of a normal predual dual element.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. Let `M_*` be their norm-closed complex
span in the continuous dual `M*`. Let `F ∈ (M_*)*` be a bounded complex-linear functional
on the normal-functional space. for `η ∈ H`, `predualRieszForm M F η ∈ H*` is the linear
functional `ξ ↦ conj(F(ω_(ξ,η)))`. -/
private noncomputable def predualRieszForm (M : VonNeumannAlgebra H)
    (F : StrongDual ℂ (normalFunctionalSpace M)) (η : H) : StrongDual ℂ H :=
  let f : H →ₗ[ℂ] ℂ :=
    { toFun := fun ξ => star (F (normalVectorFunctional M ξ η))
      map_add' := by
        intro ξ ζ
        simp only [normalVectorFunctional_add_left, map_add, star_add]
      map_smul' := by
        intro c ξ
        simp only [normalVectorFunctional_smul_left, map_smul, star_smul, star_star, RingHom.id_apply] }
  f.mkContinuous (‖F‖ * ‖η‖) (by
    intro ξ
    calc
      ‖star (F (normalVectorFunctional M ξ η))‖ = ‖F (normalVectorFunctional M ξ η)‖ := norm_star _
      _ ≤ ‖F‖ * ‖normalVectorFunctional M ξ η‖ := F.le_opNorm _
      _ ≤ ‖F‖ * (‖ξ‖ * ‖η‖) :=
        mul_le_mul_of_nonneg_left (normalVectorFunctional_norm_le M ξ η) (norm_nonneg F)
      _ = (‖F‖ * ‖η‖) * ‖ξ‖ := by ring)

/-- **Norm bound for the fixed-vector Riesz functional.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Let `F ∈ (M_*)*` be a bounded complex-linear functional on the normal-functional
space. for `η ∈ H`, `‖predualRieszForm M F η‖≤‖F‖‖η‖`. -/
private theorem predualRieszForm_norm_le (M : VonNeumannAlgebra H)
    (F : StrongDual ℂ (normalFunctionalSpace M)) (η : H) :
    ‖predualRieszForm M F η‖ ≤ ‖F‖ * ‖η‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg F) (norm_nonneg η))
  intro ξ
  change ‖star (F (normalVectorFunctional M ξ η))‖ ≤ (‖F‖ * ‖η‖) * ‖ξ‖
  calc
    ‖star (F (normalVectorFunctional M ξ η))‖ = ‖F (normalVectorFunctional M ξ η)‖ := norm_star _
    _ ≤ ‖F‖ * ‖normalVectorFunctional M ξ η‖ := F.le_opNorm _
    _ ≤ ‖F‖ * (‖ξ‖ * ‖η‖) :=
      mul_le_mul_of_nonneg_left (normalVectorFunctional_norm_le M ξ η) (norm_nonneg F)
    _ = (‖F‖ * ‖η‖) * ‖ξ‖ := by ring

/-- **Bounded conjugate-linear family of Riesz functionals.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Let `F ∈ (M_*)*` be a bounded complex-linear functional on the normal-functional
space. `predualRieszFormMap M F : H →L⋆[ℂ] H*` sends `η` to the functional `ξ ↦
conj(F(ω_(ξ,η)))`. -/
private noncomputable def predualRieszFormMap (M : VonNeumannAlgebra H)
    (F : StrongDual ℂ (normalFunctionalSpace M)) : H →L⋆[ℂ] StrongDual ℂ H :=
  let f : H →ₗ⋆[ℂ] StrongDual ℂ H :=
    { toFun := predualRieszForm M F
      map_add' := by
        intro η ζ
        apply ContinuousLinearMap.ext
        intro ξ
        change star (F (normalVectorFunctional M ξ (η + ζ))) =
          star (F (normalVectorFunctional M ξ η)) + star (F (normalVectorFunctional M ξ ζ))
        simp only [normalVectorFunctional_add_right, map_add, star_add]
      map_smul' := by
        intro c η
        apply ContinuousLinearMap.ext
        intro ξ
        change star (F (normalVectorFunctional M ξ (c • η))) =
          star c • star (F (normalVectorFunctional M ξ η))
        simp only [normalVectorFunctional_smul_right, map_smul, star_smul] }
  f.mkContinuous ‖F‖ (predualRieszForm_norm_le M F)

/-- **Hilbert operator represented by a functional on normal functionals.** Let `H` be a
complete complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. Let `M_*` be their norm-closed complex
span in the continuous dual `M*`. Let `F ∈ (M_*)*` be a bounded complex-linear functional
on the normal-functional space. `reconstructedOperator M F : H →L[ℂ] H` is the bounded
operator `T_F` characterized by `⟨ξ,T_F η⟩=F(ω_(ξ,η))` for all `ξ,η ∈ H`. -/
private noncomputable def reconstructedOperator (M : VonNeumannAlgebra H)
    (F : StrongDual ℂ (normalFunctionalSpace M)) : H →L[ℂ] H :=
  InnerProductSpace.continuousLinearMapOfBilin (predualRieszFormMap M F)

/-- **Vector coefficients of the predual reconstruction.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Let `F ∈ (M_*)*` be a bounded complex-linear functional on the normal-functional
space. for `ξ,η ∈ H`, `⟨ξ,reconstructedOperator M F η⟩=F(normalVectorFunctional M ξ η)`. -/
private theorem reconstructedOperator_inner (M : VonNeumannAlgebra H)
    (F : StrongDual ℂ (normalFunctionalSpace M)) (ξ η : H) :
    ⟪ξ, reconstructedOperator M F η⟫_ℂ = F (normalVectorFunctional M ξ η) := by
  have h := InnerProductSpace.continuousLinearMapOfBilin_apply (predualRieszFormMap M F) η ξ
  have hs := congrArg (star : ℂ → ℂ) h
  change star ⟪reconstructedOperator M F η, ξ⟫_ℂ =
    star (star (F (normalVectorFunctional M ξ η))) at hs
  have hscalar : star ⟪reconstructedOperator M F η, ξ⟫_ℂ =
      ⟪ξ, reconstructedOperator M F η⟫_ℂ := by
    simpa only [starRingEnd_apply] using
      (inner_conj_symm (𝕜 := ℂ) ξ (reconstructedOperator M F η))
  exact hscalar.symm.trans (by simpa only [star_star] using hs)

/-- **Operator-norm bound of the predual reconstruction.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Let `F ∈ (M_*)*` be a bounded complex-linear functional on the normal-functional
space. `‖reconstructedOperator M F‖≤‖F‖`, with the operator norm and continuous-dual norm
respectively. -/
private theorem norm_reconstructedOperator_le (M : VonNeumannAlgebra H)
    (F : StrongDual ℂ (normalFunctionalSpace M)) : ‖reconstructedOperator M F‖ ≤ ‖F‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg F)
  intro η
  calc
    ‖reconstructedOperator M F η‖ = ‖predualRieszFormMap M F η‖ :=
      (InnerProductSpace.toDual ℂ H).symm.norm_map _
    _ ≤ ‖F‖ * ‖η‖ := predualRieszForm_norm_le M F η

/-- **Commutant operator balancing in vector functionals.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. if `S ∈ B(H)` commutes with every element of `M`, then `ω_(S*ξ,η)=ω_(ξ,Sη)` in `M_*`
for all `ξ,η ∈ H`. -/
private theorem normalVectorFunctional_commutant (M : VonNeumannAlgebra H)
    (S : H →L[ℂ] H) (hS : S ∈ Set.centralizer (M : Set (H →L[ℂ] H))) (ξ η : H) :
    normalVectorFunctional M ((star S) ξ) η = normalVectorFunctional M ξ (S η) := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  change vectorFunctional M ((star S) ξ) η x = vectorFunctional M ξ (S η) x
  rw [vectorFunctional_apply, vectorFunctional_apply]
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  have hcomm := hS (x : H →L[ℂ] H) x.property
  change ⟪ξ, (S * (x : H →L[ℂ] H)) η⟫_ℂ = ⟪ξ, ((x : H →L[ℂ] H) * S) η⟫_ℂ
  rw [hcomm]

/-- **Predual reconstruction belongs to the concrete algebra.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Let `F ∈ (M_*)*` be a bounded complex-linear functional on the normal-functional
space. the bounded operator `reconstructedOperator M F` belongs to `M`. -/
private theorem reconstructedOperator_mem (M : VonNeumannAlgebra H)
    (F : StrongDual ℂ (normalFunctionalSpace M)) : reconstructedOperator M F ∈ M := by
  change reconstructedOperator M F ∈ (M : Set (H →L[ℂ] H))
  rw [← M.centralizer_centralizer]
  intro S hS
  apply ContinuousLinearMap.ext
  intro η
  apply ext_inner_left ℂ
  intro ξ
  change ⟪ξ, S (reconstructedOperator M F η)⟫_ℂ =
    ⟪ξ, reconstructedOperator M F (S η)⟫_ℂ
  calc
    ⟪ξ, S (reconstructedOperator M F η)⟫_ℂ =
        ⟪(star S) ξ, reconstructedOperator M F η⟫_ℂ := by
      simpa only [ContinuousLinearMap.star_eq_adjoint] using
        (ContinuousLinearMap.adjoint_inner_left S (reconstructedOperator M F η) ξ).symm
    _ = F (normalVectorFunctional M ((star S) ξ) η) := reconstructedOperator_inner M F _ _
    _ = F (normalVectorFunctional M ξ (S η)) :=
      congrArg F (normalVectorFunctional_commutant M S hS ξ η)
    _ = ⟪ξ, reconstructedOperator M F (S η)⟫_ℂ := (reconstructedOperator_inner M F _ _).symm

/-- **Dual functionals determined by vector-functional values.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. bounded complex-linear functionals `F,G ∈ (M_*)*` are equal if
`F(ω_(ξ,η))=G(ω_(ξ,η))` for every `ξ,η ∈ H`. -/
private theorem normalFunctionalDual_ext (M : VonNeumannAlgebra H)
    (f g : StrongDual ℂ (normalFunctionalSpace M))
    (hvec : ∀ ξ η : H, f (normalVectorFunctional M ξ η) = g (normalVectorFunctional M ξ η)) :
    f = g := by
  let K : Submodule ℂ (normalFunctionalSpace M) := (f - g).ker
  let Q : Submodule ℂ (StrongDual ℂ M) := K.map (normalFunctionalSpace M).subtype
  have hQ : IsClosed (Q : Set (StrongDual ℂ M)) := by
    change IsClosed (((↑) : normalFunctionalSpace M → StrongDual ℂ M) ''
      (K : Set (normalFunctionalSpace M)))
    exact (normalFunctionalSpace_isClosed M).isClosedMap_subtype_val _ (f - g).isClosed_ker
  have hPQ : normalFunctionalSpace M ≤ Q := normalFunctionalSpace_le M hQ (by
    intro ξ η
    change ∃ z : normalFunctionalSpace M,
      z ∈ K ∧ (normalFunctionalSpace M).subtype z = vectorFunctional M ξ η
    refine ⟨normalVectorFunctional M ξ η, ?_, rfl⟩
    change (f - g) (normalVectorFunctional M ξ η) = 0
    rw [sub_apply]
    exact sub_eq_zero.mpr (hvec ξ η))
  apply ContinuousLinearMap.ext
  intro φ
  have hm := hPQ φ.property
  change ∃ z : normalFunctionalSpace M,
    z ∈ K ∧ (normalFunctionalSpace M).subtype z = (φ : StrongDual ℂ M) at hm
  rcases hm with ⟨z, hz, hval⟩
  have heq : z = φ := Subtype.ext hval
  change (f - g) z = 0 at hz
  rw [sub_apply, heq] at hz
  exact sub_eq_zero.mp hz

/-- **Norm-controlled operator representing a normal-predual functional.** Let `H` be a
complete complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. Let `M_*` be their norm-closed complex
span in the continuous dual `M*`. Let `F ∈ (M_*)*` be a bounded complex-linear functional
on the normal-functional space. there exists `x ∈ M` with `normalFunctionalEvaluation M
x=F` and `‖x‖≤‖F‖`. -/
theorem normalFunctionalEvaluation_surjective_norm (M : VonNeumannAlgebra H)
    (F : StrongDual ℂ (normalFunctionalSpace M)) :
    ∃ x : M, normalFunctionalEvaluation M x = F ∧ ‖x‖ ≤ ‖F‖ := by
  let x : M := ⟨reconstructedOperator M F, reconstructedOperator_mem M F⟩
  refine ⟨x, ?_, ?_⟩
  · apply normalFunctionalDual_ext M
    intro ξ η
    change vectorFunctional M ξ η x = F (normalVectorFunctional M ξ η)
    rw [vectorFunctional_apply]
    exact reconstructedOperator_inner M F ξ η
  · exact norm_reconstructedOperator_le M F

/-- **Surjectivity of normal-functional evaluation.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its
vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. every bounded complex-linear functional on `M_*` is evaluation at an element of `M`;
thus `normalFunctionalEvaluation M` is surjective. -/
theorem normalFunctionalEvaluation_surjective (M : VonNeumannAlgebra H) :
    Function.Surjective (normalFunctionalEvaluation M) := by
  intro F
  obtain ⟨x, hx, _⟩ := normalFunctionalEvaluation_surjective_norm M F
  exact ⟨x, hx⟩

/-- **Operator norm bounds the normal evaluation norm.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its
vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. for `x ∈ M`, `‖normalFunctionalEvaluation M x‖≤‖x‖`. -/
private theorem normalFunctionalEvaluation_norm_le (M : VonNeumannAlgebra H) (x : M) :
    ‖normalFunctionalEvaluation M x‖ ≤ ‖x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x)
  intro φ
  change ‖(φ : StrongDual ℂ M) x‖ ≤ ‖x‖ * ‖φ‖
  calc
    ‖(φ : StrongDual ℂ M) x‖ ≤ ‖φ‖ * ‖x‖ := (φ : StrongDual ℂ M).le_opNorm x
    _ = ‖x‖ * ‖φ‖ := mul_comm _ _

/-- **Isometric normal-functional evaluation.** Let `H` be a complete complex Hilbert space
and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector
functionals. Let `M_*` be their norm-closed complex span in the continuous dual `M*`. for
`x ∈ M`, `‖normalFunctionalEvaluation M x‖=‖x‖`, with the inherited operator norm on `M`. -/
theorem normalFunctionalEvaluation_norm (M : VonNeumannAlgebra H) (x : M) :
    ‖normalFunctionalEvaluation M x‖ = ‖x‖ := by
  obtain ⟨y, hy, hnorm⟩ :=
    normalFunctionalEvaluation_surjective_norm M (normalFunctionalEvaluation M x)
  have hyx : y = x := normalFunctionalEvaluation_injective M hy
  apply le_antisymm (normalFunctionalEvaluation_norm_le M x)
  simpa only [hyx] using hnorm

/-- **Linear isometric equivalence with the normal-predual dual.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. Let `M_*` be their norm-closed complex
span in the continuous dual `M*`. `normalFunctionalEvaluationEquiv M : M ≃ₗᵢ[ℂ] (M_*)*` is
`x ↦ (φ ↦ φ(x))`. -/
noncomputable def normalFunctionalEvaluationEquiv (M : VonNeumannAlgebra H) :
    M ≃ₗᵢ[ℂ] StrongDual ℂ (normalFunctionalSpace M) :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (normalFunctionalEvaluation M).toLinearMap
      norm_map' := normalFunctionalEvaluation_norm M }
    (normalFunctionalEvaluation_surjective M)

/-- **Pairing of the isometric predual evaluation equivalence.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. for `x ∈ M` and `φ ∈ M_*`, `(normalFunctionalEvaluationEquiv M x)(φ)=φ(x)`. -/
@[simp]
theorem normalFunctionalEvaluationEquiv_apply (M : VonNeumannAlgebra H) (x : M)
    (φ : normalFunctionalSpace M) :
    normalFunctionalEvaluationEquiv M x φ = (φ : StrongDual ℂ M) x :=
  rfl

/-- **Existence of the evaluation isometric dual realization.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. there is a linear isometric equivalence `e : M ≃ₗᵢ[ℂ] (M_*)*` satisfying
`e(x)(φ)=φ(x)` for every `x ∈ M`, `φ ∈ M_*`. -/
theorem normalFunctionalEvaluation_isometricEquivalence (M : VonNeumannAlgebra H) :
    ∃ e : M ≃ₗᵢ[ℂ] StrongDual ℂ (normalFunctionalSpace M),
      ∀ x : M, ∀ φ : normalFunctionalSpace M, e x φ = (φ : StrongDual ℂ M) x :=
  ⟨normalFunctionalEvaluationEquiv M, fun _ _ => rfl⟩

/-- **Conjugate-linear predual equivalence from the algebra involution.** Let `H` be a
complete complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. Let `M_*` be their norm-closed complex
span in the continuous dual `M*`. `normalFunctionalPredualConjugateEquiv M : (M_*)*
≃ₗᵢ⋆[ℂ] M` sends `F` to `(J_M⁻¹ F)*`, where `J_M(x)(φ)=φ(x)`. -/
noncomputable def normalFunctionalPredualConjugateEquiv (M : VonNeumannAlgebra H) :
    StrongDual ℂ (normalFunctionalSpace M) ≃ₗᵢ⋆[ℂ] M where
  toLinearEquiv := (normalFunctionalEvaluationEquiv M).symm.toLinearEquiv.trans
    (starLinearEquiv ℂ : M ≃ₗ⋆[ℂ] M)
  norm_map' := by
    intro F
    change ‖star ((normalFunctionalEvaluationEquiv M).symm F)‖ = ‖F‖
    rw [norm_star]
    exact (normalFunctionalEvaluationEquiv M).symm.norm_map F

/-- **W-star-algebra structure from the normal-functional Banach space.** Let `H` be a
complete complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. Let `M_*` be their norm-closed complex
span in the continuous dual `M*`. `M_*` witnesses the predual property of `M`: it is a
complex Banach space whose continuous dual is conjugate-linearly isometrically equivalent
to `M` via `F ↦ (J_M⁻¹F)*`. -/
noncomputable instance normalFunctionalInstWStarAlgebra (M : VonNeumannAlgebra H) : WStarAlgebra M where
  exists_predual :=
    ⟨normalFunctionalSpace M, inferInstance, inferInstance, inferInstance,
      ⟨normalFunctionalPredualConjugateEquiv M⟩⟩

end VonNeumannAlgebra
