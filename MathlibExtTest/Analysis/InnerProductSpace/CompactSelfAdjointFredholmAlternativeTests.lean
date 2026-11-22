/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointFredholmAlternative
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

@[expose] public section

open Function Set Filter Topology
open MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointFredholmAlternative

namespace MathlibExtTest.Analysis.InnerProductSpace.CompactSelfAdjointFredholmAlternative

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The Fredholm alternative on an abstract compact self-adjoint operator. -/
example {T : H →L[𝕜] H} (hT : IsCompactOperator (T : H → H)) (hsa : IsSelfAdjoint T)
    {μ : 𝕜} (hμ : μ ≠ 0) :
    LinearMap.range (μ • (ContinuousLinearMap.id 𝕜 H) - T).toLinearMap =
      (LinearMap.ker (μ • (ContinuousLinearMap.id 𝕜 H) - T).toLinearMap).orthogonal ∧
    (Function.Bijective (μ • (ContinuousLinearMap.id 𝕜 H) - T) ∨
      (LinearMap.ker (μ • (ContinuousLinearMap.id 𝕜 H) - T).toLinearMap ≠ ⊥ ∧
       FiniteDimensional 𝕜
         (LinearMap.ker (μ • (ContinuousLinearMap.id 𝕜 H) - T).toLinearMap))) :=
  fredholm_alternative_of_isCompactOperator_isSelfAdjoint hT hsa hμ

/-- Closed range on an abstract compact self-adjoint operator. -/
example {T : H →L[𝕜] H} (hT : IsCompactOperator (T : H → H)) (hsa : IsSelfAdjoint T)
    {μ : 𝕜} (hμ : μ ≠ 0) :
    IsClosed (LinearMap.range (μ • (ContinuousLinearMap.id 𝕜 H) - T).toLinearMap : Set H) :=
  isClosed_range_smul_id_sub_of_isCompactOperator_isSelfAdjoint hT hsa hμ

/-- The `T - μ • 1` form on an abstract compact self-adjoint operator. -/
example {T : H →L[𝕜] H} (hT : IsCompactOperator (T : H → H)) (hsa : IsSelfAdjoint T)
    {μ : 𝕜} (hμ : μ ≠ 0) :
    LinearMap.range (T - μ • (ContinuousLinearMap.id 𝕜 H)).toLinearMap =
      (LinearMap.ker (T - μ • (ContinuousLinearMap.id 𝕜 H)).toLinearMap).orthogonal ∧
    (Function.Bijective (T - μ • (ContinuousLinearMap.id 𝕜 H)) ∨
      (LinearMap.ker (T - μ • (ContinuousLinearMap.id 𝕜 H)).toLinearMap ≠ ⊥ ∧
       FiniteDimensional 𝕜
         (LinearMap.ker (T - μ • (ContinuousLinearMap.id 𝕜 H)).toLinearMap))) :=
  fredholm_alternative_sub_of_isCompactOperator_isSelfAdjoint hT hsa hμ

/-- Bijective branch, concrete: for the zero operator on `Fin 2 → ℝ` and
`μ = 1`, the operator `1 • 1 - 0 = 1` is bijective, and its range is `⊤`. -/
example :
    Function.Bijective ((1 : ℝ) • (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) -
      (0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))) ∧
    LinearMap.range (((1 : ℝ) • (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) -
      (0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))).toLinearMap) =
      ⊤ := by
  have h := fredholm_alternative_of_isCompactOperator_isSelfAdjoint
    (T := (0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)))
    isCompactOperator_zero (IsSelfAdjoint.zero _) (μ := (1 : ℝ)) one_ne_zero
  obtain ⟨hrange, hbij | hker⟩ := h
  · refine ⟨hbij, ?_⟩
    rw [hrange, LinearMap.ker_eq_bot.mpr hbij.injective, Submodule.bot_orthogonal_eq_top]
  · exfalso
    obtain ⟨hne, _⟩ := hker
    have hinj : Function.Injective
        (((1 : ℝ) • (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) -
          (0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))) :
          EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) := by
      intro a b hab
      simpa using hab
    exact hne (LinearMap.ker_eq_bot.mpr hinj)

/-- Eigenvalue branch, concrete: for the identity operator on
`EuclideanSpace ℝ (Fin 2)` and `μ = 1`, the operator `1 • 1 - 1 = 0` is not
bijective, its kernel is `⊤` (nontrivial), and that kernel is
finite-dimensional. -/
example :
    ¬ Function.Bijective ((1 : ℝ) • (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) -
      (1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))) ∧
    LinearMap.ker ((1 : ℝ) • (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) -
      (1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))).toLinearMap ≠ ⊥ ∧
    FiniteDimensional ℝ
      (LinearMap.ker ((1 : ℝ) • (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) -
      (1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))).toLinearMap) := by
  have h1compact : IsCompactOperator
      ((1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
        EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) := by
    have h := (isCompactOperator_id_iff_finiteDimensional (𝕜 := ℝ)
      (E := EuclideanSpace ℝ (Fin 2))).mpr inferInstance
    simpa using h
  have h := fredholm_alternative_of_isCompactOperator_isSelfAdjoint
    (T := (1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)))
    h1compact (IsSelfAdjoint.one _) (μ := (1 : ℝ)) one_ne_zero
  obtain ⟨hrange, hbij | hker⟩ := h
  · exfalso
    -- `1 • 1 - 1 = 0` kills the first basis vector, so it is not injective.
    have hkill : ((1 : ℝ) • (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) -
        (1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)))
        (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) = 0 := by
      simp
    have h0 : ((1 : ℝ) • (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) -
        (1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)))
        (0 : EuclideanSpace ℝ (Fin 2)) = 0 := map_zero _
    have heq : EuclideanSpace.single (0 : Fin 2) (1 : ℝ) =
        (0 : EuclideanSpace ℝ (Fin 2)) :=
      hbij.injective (by rw [hkill, h0])
    have hne : EuclideanSpace.single (0 : Fin 2) (1 : ℝ) ≠ 0 := by
      intro h
      exact one_ne_zero ((PiLp.single_eq_zero_iff (2 : ENNReal) (0 : Fin 2)).mp h)
    exact hne heq
  · obtain ⟨hne, hfin⟩ := hker
    refine ⟨?_, hne, hfin⟩
    intro hb
    exact hne (LinearMap.ker_eq_bot.mpr hb.injective)

/-- The kernel-of-`μ • 1 - T` equals the eigenspace, on an abstract operator. -/
example {T : H →L[𝕜] H} (μ : 𝕜) :
    LinearMap.ker (μ • (ContinuousLinearMap.id 𝕜 H) - T).toLinearMap =
      Module.End.eigenspace (T.toLinearMap) μ :=
  ker_smul_id_sub_eq_eigenspace T μ

-- The Fredholm alternative depends only on the standard axioms.
#print axioms fredholm_alternative_of_isCompactOperator_isSelfAdjoint
#print axioms isClosed_range_smul_id_sub_of_isCompactOperator_isSelfAdjoint
#print axioms fredholm_alternative_sub_of_isCompactOperator_isSelfAdjoint

end MathlibExtTest.Analysis.InnerProductSpace.CompactSelfAdjointFredholmAlternative
