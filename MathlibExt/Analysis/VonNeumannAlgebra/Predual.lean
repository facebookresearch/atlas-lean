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
# The actual normal functional space is a concrete predual

Evaluation identifies the original concrete von Neumann algebra with the
continuous dual of its norm-closed vector-functional span. For a functional
on that span, Fréchet–Riesz constructs the bounded operator having its actual
vector coefficients. Commutation with the original commutant places this
operator in the original algebra. Continuity extends coefficient agreement
to the complete closed span.

The pairing and norm are the original functional evaluation and operator
norm. The stock involution supplies the conjugate-linear convention of the
existing abstract `WStarAlgebra` predicate.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace CStarAlgebra

namespace VonNeumannAlgebra

open MathlibExt.Analysis.CStarAlgebra

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The normal-functional carrier has the original restricted normed additive-group structure. -/
noncomputable instance normalFunctionalSpaceNormedAddCommGroup (M : VonNeumannAlgebra H) :
    NormedAddCommGroup (normalFunctionalSpace M) :=
  Submodule.normedAddCommGroup (𝕜 := ℂ) (E := StrongDual ℂ M) (normalFunctionalSpace M)

/-- The normal-functional carrier has the original restricted complex normed-space structure. -/
noncomputable instance normalFunctionalSpaceNormedSpace (M : VonNeumannAlgebra H) :
    NormedSpace ℂ (normalFunctionalSpace M) :=
  Submodule.normedSpace (𝕜 := ℂ) (R := ℂ) (E := StrongDual ℂ M) (normalFunctionalSpace M)

/-- An actual vector coefficient viewed in the canonical closed normal-functional space. -/
noncomputable def normalVectorFunctional (M : VonNeumannAlgebra H) (ξ η : H) :
    normalFunctionalSpace M :=
  ⟨vectorFunctional M ξ η, vectorFunctional_mem_normalFunctionalSpace M ξ η⟩

/-- Evaluation restricted to the actual closed normal-functional space. -/
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

/-- The restricted evaluation pairing is ordinary evaluation in the original dual. -/
@[simp]
theorem normalFunctionalEvaluation_apply (M : VonNeumannAlgebra H) (x : M)
    (φ : normalFunctionalSpace M) :
    normalFunctionalEvaluation M x φ = (φ : StrongDual ℂ M) x :=
  rfl

/-- Vector coefficients determine every original operator in the concrete algebra. -/
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

/-- The normal vector coefficient has its inherited continuous-dual norm bound. -/
private theorem normalVectorFunctional_norm_le (M : VonNeumannAlgebra H) (ξ η : H) :
    ‖normalVectorFunctional M ξ η‖ ≤ ‖ξ‖ * ‖η‖ :=
  norm_vectorFunctional_le M ξ η

/-- Normal vector coefficients are additive in the first Hilbert argument. -/
private theorem normalVectorFunctional_add_left (M : VonNeumannAlgebra H) (ξ ζ η : H) :
    normalVectorFunctional M (ξ + ζ) η =
      normalVectorFunctional M ξ η + normalVectorFunctional M ζ η := by
  apply Subtype.ext
  change vectorFunctional M (ξ + ζ) η = vectorFunctional M ξ η + vectorFunctional M ζ η
  simpa only [vectorFunctional] using
    representationCoefficient_add_right (A := M) M.toStarSubalgebra.subtype η ξ ζ

/-- Normal vector coefficients are conjugate-linear in the first Hilbert argument. -/
private theorem normalVectorFunctional_smul_left (M : VonNeumannAlgebra H)
    (c : ℂ) (ξ η : H) :
    normalVectorFunctional M (c • ξ) η = star c • normalVectorFunctional M ξ η := by
  apply Subtype.ext
  change vectorFunctional M (c • ξ) η = star c • vectorFunctional M ξ η
  simpa only [vectorFunctional] using
    representationCoefficient_smul_right (A := M) M.toStarSubalgebra.subtype c η ξ

/-- Normal vector coefficients are additive in the second Hilbert argument. -/
private theorem normalVectorFunctional_add_right (M : VonNeumannAlgebra H) (ξ η ζ : H) :
    normalVectorFunctional M ξ (η + ζ) =
      normalVectorFunctional M ξ η + normalVectorFunctional M ξ ζ := by
  apply Subtype.ext
  change vectorFunctional M ξ (η + ζ) = vectorFunctional M ξ η + vectorFunctional M ξ ζ
  simpa only [vectorFunctional] using
    representationCoefficient_add_left (A := M) M.toStarSubalgebra.subtype η ζ ξ

/-- Normal vector coefficients are linear in the second Hilbert argument. -/
private theorem normalVectorFunctional_smul_right (M : VonNeumannAlgebra H)
    (c : ℂ) (ξ η : H) :
    normalVectorFunctional M ξ (c • η) = c • normalVectorFunctional M ξ η := by
  apply Subtype.ext
  change vectorFunctional M ξ (c • η) = c • vectorFunctional M ξ η
  simpa only [vectorFunctional] using
    representationCoefficient_smul_left (A := M) M.toStarSubalgebra.subtype c η ξ

/-- Riesz receives the actual conjugated coefficient functional at a fixed second vector. -/
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

/-- The fixed-vector Riesz functional retains the actual product norm bound. -/
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

/-- The actual bounded sesquilinear family supplied to the stock Riesz construction. -/
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

/-- The stock Riesz representation reconstructs the actual bounded Hilbert operator. -/
private noncomputable def reconstructedOperator (M : VonNeumannAlgebra H)
    (F : StrongDual ℂ (normalFunctionalSpace M)) : H →L[ℂ] H :=
  InnerProductSpace.continuousLinearMapOfBilin (predualRieszFormMap M F)

/-- The reconstructed operator has exactly the supplied normal vector coefficients. -/
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

/-- The actual reconstructed operator is bounded by the original functional norm. -/
private theorem norm_reconstructedOperator_le (M : VonNeumannAlgebra H)
    (F : StrongDual ℂ (normalFunctionalSpace M)) : ‖reconstructedOperator M F‖ ≤ ‖F‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg F)
  intro η
  calc
    ‖reconstructedOperator M F η‖ = ‖predualRieszFormMap M F η‖ :=
      (InnerProductSpace.toDual ℂ H).symm.norm_map _
    _ ≤ ‖F‖ * ‖η‖ := predualRieszForm_norm_le M F η

/-- The original commutant transports both vector arguments of every coefficient. -/
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

/-- Commutation with the original commutant places the reconstruction in the original algebra. -/
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

/-- Continuous functionals on the actual closed span are determined by its vector coefficients. -/
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

/-- Every actual functional on the closed normal span is evaluation at an original norm-bounded operator. -/
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

/-- The original evaluation map is onto the actual normal-functional continuous dual. -/
theorem normalFunctionalEvaluation_surjective (M : VonNeumannAlgebra H) :
    Function.Surjective (normalFunctionalEvaluation M) := by
  intro F
  obtain ⟨x, hx, _⟩ := normalFunctionalEvaluation_surjective_norm M F
  exact ⟨x, hx⟩

/-- Evaluation has the original operator-norm upper bound. -/
private theorem normalFunctionalEvaluation_norm_le (M : VonNeumannAlgebra H) (x : M) :
    ‖normalFunctionalEvaluation M x‖ ≤ ‖x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x)
  intro φ
  change ‖(φ : StrongDual ℂ M) x‖ ≤ ‖x‖ * ‖φ‖
  calc
    ‖(φ : StrongDual ℂ M) x‖ ≤ ‖φ‖ * ‖x‖ := (φ : StrongDual ℂ M).le_opNorm x
    _ = ‖x‖ * ‖φ‖ := mul_comm _ _

/-- Actual evaluation preserves the original operator norm, including the zero Hilbert space. -/
theorem normalFunctionalEvaluation_norm (M : VonNeumannAlgebra H) (x : M) :
    ‖normalFunctionalEvaluation M x‖ = ‖x‖ := by
  obtain ⟨y, hy, hnorm⟩ :=
    normalFunctionalEvaluation_surjective_norm M (normalFunctionalEvaluation M x)
  have hyx : y = x := normalFunctionalEvaluation_injective M hy
  apply le_antisymm (normalFunctionalEvaluation_norm_le M x)
  simpa only [hyx] using hnorm

/-- The canonical linear isometric equivalence uses the actual evaluation map and its proved surjectivity. -/
noncomputable def normalFunctionalEvaluationEquiv (M : VonNeumannAlgebra H) :
    M ≃ₗᵢ[ℂ] StrongDual ℂ (normalFunctionalSpace M) :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (normalFunctionalEvaluation M).toLinearMap
      norm_map' := normalFunctionalEvaluation_norm M }
    (normalFunctionalEvaluation_surjective M)

/-- The canonical isometric equivalence retains ordinary evaluation of the original functionals. -/
@[simp]
theorem normalFunctionalEvaluationEquiv_apply (M : VonNeumannAlgebra H) (x : M)
    (φ : normalFunctionalSpace M) :
    normalFunctionalEvaluationEquiv M x φ = (φ : StrongDual ℂ M) x :=
  rfl

/-- The original concrete algebra is the actual continuous dual of its normal functional space. -/
theorem normalFunctionalEvaluation_isometricEquivalence (M : VonNeumannAlgebra H) :
    ∃ e : M ≃ₗᵢ[ℂ] StrongDual ℂ (normalFunctionalSpace M),
      ∀ x : M, ∀ φ : normalFunctionalSpace M, e x φ = (φ : StrongDual ℂ M) x :=
  ⟨normalFunctionalEvaluationEquiv M, fun _ _ => rfl⟩

/-- The original involution supplies the conjugate-linear convention of the stock predual predicate. -/
noncomputable def normalFunctionalPredualConjugateEquiv (M : VonNeumannAlgebra H) :
    StrongDual ℂ (normalFunctionalSpace M) ≃ₗᵢ⋆[ℂ] M where
  toLinearEquiv := (normalFunctionalEvaluationEquiv M).symm.toLinearEquiv.trans
    (starLinearEquiv ℂ : M ≃ₗ⋆[ℂ] M)
  norm_map' := by
    intro F
    change ‖star ((normalFunctionalEvaluationEquiv M).symm F)‖ = ‖F‖
    rw [norm_star]
    exact (normalFunctionalEvaluationEquiv M).symm.norm_map F

/-- The explicit original normal-functional Banach space witnesses the existing abstract von Neumann predicate. -/
noncomputable instance normalFunctionalInstWStarAlgebra (M : VonNeumannAlgebra H) : WStarAlgebra M where
  exists_predual :=
    ⟨normalFunctionalSpace M, inferInstance, inferInstance, inferInstance,
      ⟨normalFunctionalPredualConjugateEquiv M⟩⟩

end VonNeumannAlgebra
