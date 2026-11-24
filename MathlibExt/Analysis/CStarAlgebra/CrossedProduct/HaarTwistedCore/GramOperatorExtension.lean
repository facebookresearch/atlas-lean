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

public import MathlibExt.Analysis.CStarAlgebra.SeminormGramDomain
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.FiniteHilbertGramCoefficient
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.SeminormGramGroupActions
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Actual coefficient and group operators from the original Haar-core Gram span

Finite formal sums evaluate to the actual source operator values. Their range
is the original-source Gram domain, with its inherited Hilbert norm. The
proved finite coefficient bound and group Gram identity make the corresponding
transformed sums vanish on the actual evaluation kernel.

The stock kernel quotient and range construction descends those actual sums
to the Gram domain. The stock dense extension then constructs the bounded
coefficient operators and isometric group operators on the actual essential
Hilbert space. Their values on every original generator are retained.

No descended operator, norm, isometry or nondegenerate model is an input.
Covariance, group composition, strong continuity and the integrated identity
remain separate required constructions.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators InnerProductSpace

namespace HaarTwistedCore

noncomputable section

universe uG uA uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] [μ.Regular]
  (α : PointNormCStarAction G A)

attribute [local instance] CStarSeminorm.nonUnitalCompletionCStarAlgebra

variable (p : CStarSeminorm (Carrier μ α)) (H : Type uH)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (ρ : p.NonUnitalCompletion →⋆ₙₐ[ℂ] (H →L[ℂ] H))

/-- Evaluate each finite formal sum in the actual essential Hilbert space. -/
def gramEvaluation : ((Carrier μ α × ρ.essentialSpace) →₀ ℂ) →ₗ[ℂ] ρ.essentialSpace :=
  Finsupp.linearCombination ℂ fun z =>
    ρ.essentialRepresentation (p.toNonUnitalCompletion z.1) z.2

omit [μ.Regular] in
/-- The actual evaluation range is precisely the original-source Gram domain. -/
theorem gramEvaluation_range :
    (gramEvaluation μ α p H ρ).range = p.rawHilbertGramDomain H ρ := by
  exact Finsupp.range_linearCombination ℂ

omit [μ.Regular] in
/-- The actual finite-sum evaluation map is dense in the essential Hilbert space. -/
theorem denseRange_gramEvaluation : DenseRange (gramEvaluation μ α p H ρ) := by
  have hrange : Set.range (gramEvaluation μ α p H ρ) =
      (p.rawHilbertGramDomain H ρ : Set ρ.essentialSpace) := by
    change ((gramEvaluation μ α p H ρ).range : Set ρ.essentialSpace) = _
    rw [gramEvaluation_range]
  change Dense (Set.range (gramEvaluation μ α p H ρ))
  rw [hrange]
  exact p.dense_rawHilbertGramDomain H ρ

/-- Apply the original coefficient multiplication to each actual finite-sum generator. -/
def gramCoefficientTransform (a : A) :
    ((Carrier μ α × ρ.essentialSpace) →₀ ℂ) →ₗ[ℂ] ρ.essentialSpace :=
  Finsupp.linearCombination ℂ fun z =>
    ρ.essentialRepresentation (p.toNonUnitalCompletion (coefficientLeft μ α a z.1)) z.2

/-- Apply the original group translation to each actual finite-sum generator. -/
def gramGroupTransform (g : G) :
    ((Carrier μ α × ρ.essentialSpace) →₀ ℂ) →ₗ[ℂ] ρ.essentialSpace :=
  Finsupp.linearCombination ℂ fun z =>
    ρ.essentialRepresentation (p.toNonUnitalCompletion (groupLeft μ α g z.1)) z.2

omit [μ.Regular] in
/-- The proved finite Gram coefficient bound applies to every actual free finite sum. -/
theorem norm_gramCoefficientTransform_le (a : A)
    (x : (Carrier μ α × ρ.essentialSpace) →₀ ℂ) :
    ‖gramCoefficientTransform μ α p H ρ a x‖ ≤ ‖a‖ * ‖gramEvaluation μ α p H ρ x‖ := by
  simpa only [finiteHilbertGramCoefficient_inr, finiteHilbertGram,
    gramCoefficientTransform, gramEvaluation, Finsupp.linearCombination_apply, Finsupp.sum] using
    norm_finiteHilbertGramCoefficient_inr_le μ α p ρ.essentialRepresentation a x.support x
      (fun z => z.1) (fun z => z.2)

/-- The proved finite group Gram identity applies to every actual free finite sum. -/
theorem norm_gramGroupTransform (g : G)
    (x : (Carrier μ α × ρ.essentialSpace) →₀ ℂ) :
    ‖gramGroupTransform μ α p H ρ g x‖ = ‖gramEvaluation μ α p H ρ x‖ := by
  simpa only [gramGroupTransform, gramEvaluation, Finsupp.linearCombination_apply, Finsupp.sum] using
    norm_sum_completedRepresentation_groupLeft μ α p ρ.essentialSpace
      ρ.essentialRepresentation g x.support x (fun z => z.1) (fun z => z.2)

omit [μ.Regular] in
/-- The actual coefficient transform vanishes on the original finite-sum evaluation kernel. -/
theorem gramCoefficientTransform_kernel (a : A) :
    (gramEvaluation μ α p H ρ).ker ≤ (gramCoefficientTransform μ α p H ρ a).ker := by
  intro x hx
  change gramEvaluation μ α p H ρ x = 0 at hx
  change gramCoefficientTransform μ α p H ρ a x = 0
  have hbase : finiteHilbertGram μ α p ρ.essentialRepresentation x.support x
      (fun z => z.1) (fun z => z.2) = 0 := by
    simpa only [finiteHilbertGram, gramEvaluation,
      Finsupp.linearCombination_apply, Finsupp.sum] using hx
  have hzero := finiteHilbertGramCoefficient_inr_eq_zero_of_eq_zero μ α p
    ρ.essentialRepresentation a x.support x (fun z => z.1) (fun z => z.2) hbase
  simpa only [finiteHilbertGramCoefficient_inr, gramCoefficientTransform,
    Finsupp.linearCombination_apply, Finsupp.sum] using hzero

/-- The actual group transform has exactly the original finite-sum evaluation kernel. -/
theorem gramGroupTransform_kernel (g : G) :
    (gramGroupTransform μ α p H ρ g).ker = (gramEvaluation μ α p H ρ).ker := by
  ext x
  change gramGroupTransform μ α p H ρ g x = 0 ↔ gramEvaluation μ α p H ρ x = 0
  constructor
  · intro h
    apply norm_eq_zero.mp
    have hn := norm_gramGroupTransform μ α p H ρ g x
    rw [h, norm_zero] at hn
    exact hn.symm
  · intro h
    apply norm_eq_zero.mp
    exact (norm_gramGroupTransform μ α p H ρ g x).trans (by rw [h, norm_zero])

/-- The actual coefficient transform descended through the evaluation kernel to its Gram range. -/
def gramCoefficientOnDomain (a : A) :
    (gramEvaluation μ α p H ρ).range →L[ℂ] ρ.essentialSpace :=
  (gramCoefficientTransform μ α p H ρ a).compLeftInverse (gramEvaluation μ α p H ρ)

omit [μ.Regular] in
/-- The descended coefficient map retains each actual finite-sum value. -/
theorem gramCoefficientOnDomain_apply (a : A)
    (x : (Carrier μ α × ρ.essentialSpace) →₀ ℂ) :
    gramCoefficientOnDomain μ α p H ρ a
      ⟨gramEvaluation μ α p H ρ x, LinearMap.mem_range_self _ x⟩ =
        gramCoefficientTransform μ α p H ρ a x := by
  exact LinearMap.compLeftInverse_apply_of_bdd _ _
    ⟨‖a‖, norm_gramCoefficientTransform_le μ α p H ρ a⟩ x _ rfl

/-- The actual coefficient operator obtained by dense extension of the descended Gram action. -/
def gramCoefficientOperator (a : A) : ρ.essentialSpace →L[ℂ] ρ.essentialSpace :=
  (gramCoefficientTransform μ α p H ρ a).extendOfNorm (gramEvaluation μ α p H ρ)

omit [μ.Regular] in
/-- The extended coefficient operator retains the literal source coefficient action. -/
theorem gramCoefficientOperator_apply_generator (a : A) (f : Carrier μ α) (ξ : ρ.essentialSpace) :
    gramCoefficientOperator μ α p H ρ a
      (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ) =
        ρ.essentialRepresentation (p.toNonUnitalCompletion (coefficientLeft μ α a f)) ξ := by
  have h := LinearMap.extendOfNorm_eq (f := gramCoefficientTransform μ α p H ρ a)
    (e := gramEvaluation μ α p H ρ) (denseRange_gramEvaluation μ α p H ρ)
    ⟨‖a‖, norm_gramCoefficientTransform_le μ α p H ρ a⟩ (Finsupp.single (f, ξ) 1)
  simpa only [gramCoefficientOperator, gramCoefficientTransform, gramEvaluation,
    Finsupp.linearCombination_single, one_smul] using h

omit [μ.Regular] in
/-- The actual coefficient bound holds on every Hilbert vector after dense extension. -/
theorem norm_gramCoefficientOperator_apply_le (a : A) (ξ : ρ.essentialSpace) :
    ‖gramCoefficientOperator μ α p H ρ a ξ‖ ≤ ‖a‖ * ‖ξ‖ :=
  LinearMap.norm_extendOfNorm_apply_le (denseRange_gramEvaluation μ α p H ρ) ‖a‖
    (norm_gramCoefficientTransform_le μ α p H ρ a) ξ

omit [μ.Regular] in
/-- The actual extended coefficient operator has the original coefficient operator-norm bound. -/
theorem opNorm_gramCoefficientOperator_le (a : A) :
    ‖gramCoefficientOperator μ α p H ρ a‖ ≤ ‖a‖ :=
  LinearMap.opNorm_extendOfNorm_le (denseRange_gramEvaluation μ α p H ρ) (norm_nonneg a)
    (norm_gramCoefficientTransform_le μ α p H ρ a)

/-- The actual group transform descended through the evaluation kernel to its Gram range. -/
def gramGroupOnDomain (g : G) :
    (gramEvaluation μ α p H ρ).range →L[ℂ] ρ.essentialSpace :=
  (gramGroupTransform μ α p H ρ g).compLeftInverse (gramEvaluation μ α p H ρ)

/-- The descended group map retains the literal transform of every original finite source sum. -/
theorem gramGroupOnDomain_apply (g : G)
    (x : (Carrier μ α × ρ.essentialSpace) →₀ ℂ) :
    gramGroupOnDomain μ α p H ρ g
      ⟨gramEvaluation μ α p H ρ x, LinearMap.mem_range_self _ x⟩ =
        gramGroupTransform μ α p H ρ g x := by
  exact LinearMap.compLeftInverse_apply_of_bdd _ _
    ⟨1, fun z => by simpa only [one_mul] using (norm_gramGroupTransform μ α p H ρ g z).le⟩ x _ rfl

/-- The actual descended group map preserves the inherited norm of every Gram-domain vector. -/
theorem norm_gramGroupOnDomain_apply (g : G) (x : (gramEvaluation μ α p H ρ).range) :
    ‖gramGroupOnDomain μ α p H ρ g x‖ = ‖x‖ := by
  rcases x with ⟨y, ⟨z, hz⟩⟩
  subst y
  rw [gramGroupOnDomain_apply]
  exact norm_gramGroupTransform μ α p H ρ g z

/-- The actual group operator obtained from the proved finite Gram isometry and dense extension. -/
def gramGroupIsometry (g : G) : ρ.essentialSpace →ₗᵢ[ℂ] ρ.essentialSpace :=
  (gramGroupTransform μ α p H ρ g).extendOfIsometry
    (e := gramEvaluation μ α p H ρ) (denseRange_gramEvaluation μ α p H ρ)
    (norm_gramGroupTransform μ α p H ρ g)

/-- The actual group isometry viewed as a bounded linear operator. -/
def gramGroupOperator (g : G) : ρ.essentialSpace →L[ℂ] ρ.essentialSpace :=
  (gramGroupIsometry μ α p H ρ g).toContinuousLinearMap

/-- The extended group operator retains the literal original group translation of every generator. -/
theorem gramGroupOperator_apply_generator (g : G) (f : Carrier μ α) (ξ : ρ.essentialSpace) :
    gramGroupOperator μ α p H ρ g
      (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ) =
        ρ.essentialRepresentation (p.toNonUnitalCompletion (groupLeft μ α g f)) ξ := by
  change (gramGroupIsometry μ α p H ρ g).toContinuousLinearMap
    (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ) = _
  rw [gramGroupIsometry, LinearMap.toContinuousLinearMap_extendOfIsometry]
  have h := LinearMap.extendOfNorm_eq (f := gramGroupTransform μ α p H ρ g)
    (e := gramEvaluation μ α p H ρ) (denseRange_gramEvaluation μ α p H ρ)
    ⟨1, fun x => by simpa only [one_mul] using (norm_gramGroupTransform μ α p H ρ g x).le⟩
    (Finsupp.single (f, ξ) 1)
  simpa only [gramGroupTransform, gramEvaluation, Finsupp.linearCombination_single, one_smul] using h

/-- The actual extended group operator preserves the inherited Hilbert norm of every vector. -/
theorem norm_gramGroupOperator_apply (g : G) (ξ : ρ.essentialSpace) :
    ‖gramGroupOperator μ α p H ρ g ξ‖ = ‖ξ‖ :=
  (gramGroupIsometry μ α p H ρ g).norm_map ξ

end

end HaarTwistedCore
