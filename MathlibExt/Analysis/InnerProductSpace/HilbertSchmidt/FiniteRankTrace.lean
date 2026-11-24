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

public import Mathlib.Algebra.Module.LinearMap.FiniteRange
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Trace
public import MathlibExt.Analysis.InnerProductSpace.CompactOperator.FiniteRankClosure
public import MathlibExt.Analysis.Normed.Operator.FiniteRank
public import MathlibExt.Analysis.InnerProductSpace.Adjoint.OneSided

/-!
# Actual bounded finite-rank carriers and range trace

The original bounded finite-rank submodule specializes the scalar-general
canonical ContinuousLinearMap.finiteRankOperator, formerly used by Conway
Functional Analysis VI.3. Trace is stock finite-dimensional trace on the actual range,
with the original operator restricted to that range. The finite-rank inner
and square-root functions record the printed scalar formulas; no Hilbert
space/norm/completeness instance is selected from their source theorem.
On a complete Hilbert domain the carrier is exactly the existing rank-one
span, via the explicit equality below. The more general normed-space carrier
supports range trace and composition without requiring an inner product.
All proofs here are necessary constructor/value or carrier-identification facts.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace ContinuousLinearMap

universe uH uK uL

section NormedSpaces
variable {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable {K : Type uK} [NormedAddCommGroup K] [NormedSpace ℂ K]
variable {L : Type uL} [NormedAddCommGroup L] [NormedSpace ℂ L]

/-- Composing the actual finite-rank operator on the left retains its literal finite-rank value. -/
def finiteRankComposeLeft (R : K →L[ℂ] L) (T : finiteRankOperator (𝕜 := ℂ) (E := H) (F := K)) :
    finiteRankOperator (𝕜 := ℂ) (E := H) (F := L) :=
  ⟨R.comp T.val, by
    apply (mem_finiteRankOperator _).2
    change (R.toLinearMap.comp T.val.toLinearMap).HasFiniteRange
    exact ((mem_finiteRankOperator T.val).1 T.property).comp_left R.toLinearMap⟩

/-- The composed finite-rank subtype has the same original bounded operator. -/
theorem finiteRankComposeLeft_coe (R : K →L[ℂ] L) (T : finiteRankOperator (𝕜 := ℂ) (E := H) (F := K)) :
    (finiteRankComposeLeft R T : H →L[ℂ] L) = R.comp T.val := rfl

/-- The genuine finite-dimensional trace on the actual operator range. -/
def finiteRankRangeTrace (T : finiteRankOperator (𝕜 := ℂ) (E := H) (F := H)) : ℂ :=
  LinearMap.trace ℂ T.val.range
    (T.val.toLinearMap.rangeRestrict.domRestrict T.val.range)

end NormedSpaces

section HilbertSpaces
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace K] in
/-- On complete Hilbert domains the actual finite-range carrier is the existing rank-one span.
This identifies the original finite-rank trace DATA with the canonical compact-operator API. -/
theorem finiteRankOperator_eq_finiteRankSubmodule :
    finiteRankOperator (𝕜 := ℂ) (E := H) (F := K) =
      InnerProductSpace.finiteRankSubmodule (𝕜 := ℂ) (E := H) (F := K) := by
  classical
  apply le_antisymm
  · intro T hT
    let : IsNoetherian ℂ T.range :=
      ((mem_finiteRankOperator T).1 hT).hasNoetherianRange
    let : FiniteDimensional ℂ T.range := inferInstance
    let b : OrthonormalBasis (Fin (Module.finrank ℂ T.range)) ℂ T.range :=
      stdOrthonormalBasis ℂ T.range
    have hProjection : T.range.starProjection =
        ∑ i, InnerProductSpace.rankOne ℂ (b i : K) (b i : K) :=
      b.starProjection_eq_sum_rankOne
    have hFactor : T.range.starProjection.comp T = T := by
      apply ContinuousLinearMap.ext
      intro x
      exact T.range.starProjection_eq_self_iff.mpr ⟨x, rfl⟩
    have hSum : T = ∑ i, InnerProductSpace.rankOne ℂ (b i : K)
        ((ContinuousLinearMap.adjointOfCompleteSource T) (b i : K)) := by
      calc
        T = T.range.starProjection.comp T := hFactor.symm
        _ = (∑ i, InnerProductSpace.rankOne ℂ (b i : K) (b i : K)).comp T :=
          congrArg (fun P : K →L[ℂ] K => P.comp T) hProjection
        _ = ∑ i, (InnerProductSpace.rankOne ℂ (b i : K) (b i : K)).comp T := by
          ext x
          simp
        _ = ∑ i, InnerProductSpace.rankOne ℂ (b i : K)
            ((ContinuousLinearMap.adjointOfCompleteSource T) (b i : K)) := by
          apply Finset.sum_congr rfl
          intro i _hi
          ext x
          simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.rankOne_apply]
          rw [ContinuousLinearMap.adjointOfCompleteSource_inner_left]
    rw [hSum]
    exact Submodule.sum_mem _ fun i _ =>
      InnerProductSpace.rankOne_mem_finiteRankSubmodule (b i : K)
        ((ContinuousLinearMap.adjointOfCompleteSource T) (b i : K))
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, y⟩, rfl⟩
    apply (mem_finiteRankOperator _).2
    change (InnerProductSpace.rankOne ℂ x y).toLinearMap.HasFiniteRange
    have hSpan : (ContinuousLinearMap.toSpanSingleton ℂ x).toLinearMap.HasFiniteRange :=
      LinearMap.HasFiniteRange.of_finite_dom
    have hRank : (InnerProductSpace.rankOne ℂ x y).toLinearMap.HasFiniteRange := by
      rw [InnerProductSpace.rankOne_def', ContinuousLinearMap.toLinearMap_comp]
      exact hSpan.comp_right (innerSL ℂ y).toLinearMap
    exact hRank

omit [CompleteSpace K] in
/-- The printed finite-rank scalar inner product is the actual trace of adjoint S composed with T.
-/
def finiteRankHilbertSchmidtInner (S T : finiteRankOperator (𝕜 := ℂ) (E := H) (F := K)) : ℂ :=
  finiteRankRangeTrace (finiteRankComposeLeft (ContinuousLinearMap.adjointOfCompleteSource S.val) T)

omit [CompleteSpace K] in
/-- The printed square-root of the diagonal trace, with no assumed norm law or completed model. -/
def finiteRankHilbertSchmidtNorm (T : finiteRankOperator (𝕜 := ℂ) (E := H) (F := K)) : ℝ :=
  Real.sqrt (finiteRankHilbertSchmidtInner T T).re

omit [CompleteSpace K] in
/-- The finite-rank inner function retains the original adjoint/product trace exactly. -/
theorem finiteRankHilbertSchmidtInner_def (S T : finiteRankOperator (𝕜 := ℂ) (E := H) (F := K)) :
    finiteRankHilbertSchmidtInner S T =
      finiteRankRangeTrace (finiteRankComposeLeft (ContinuousLinearMap.adjointOfCompleteSource S.val) T) := rfl

/-- On two complete Hilbert spaces the generalized trace formula is the original adjoint formula. -/
theorem finiteRankHilbertSchmidtInner_eq_trace_adjoint
    (S T : finiteRankOperator (𝕜 := ℂ) (E := H) (F := K)) :
    finiteRankHilbertSchmidtInner S T =
      finiteRankRangeTrace (finiteRankComposeLeft S.val.adjoint T) := by
  rw [finiteRankHilbertSchmidtInner_def,
    ContinuousLinearMap.adjointOfCompleteSource_eq_adjoint]

end HilbertSpaces

end ContinuousLinearMap

end
