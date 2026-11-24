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

public import MathlibExt.Analysis.CStarAlgebra.Module.HilbertAmplification.ElementaryCompacts
public import MathlibExt.Analysis.InnerProductSpace.CompactOperator.BasisApproximation
public import MathlibExt.Analysis.InnerProductSpace.Operator.FiniteCoordinateExpansion

/-!
# Actual finite Hilbert-basis compressions of full-H compact operators

Reuse the stock finite projections of an arbitrary Hilbert basis. The
already proved compact-sandwich theorem supplies operator-norm convergence
of the diagonal finite-set net. Package those actual maps in the original
compact ideal, retaining their original matrix-entry rank-one values.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped BigOperators InnerProductSpace Topology

namespace CStarModule.HilbertAmplification

universe uH uI
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type uI} (b : HilbertBasis ι ℂ H)

/-- The actual two-sided finite projection compression as a linear map of the full compact ideal. -/
def compactCompression (s : Finset ι) :
    (compactEndomorphismClosedStarIdeal (H := H)).carrier →ₗ[ℂ]
      (compactEndomorphismClosedStarIdeal (H := H)).carrier where
  toFun k :=
    ⟨(b.toUnconditionalSchauderBasis.proj s).comp ((k : H →L[ℂ] H).comp (b.toUnconditionalSchauderBasis.proj s)),
      (k.property.comp_clm (b.toUnconditionalSchauderBasis.proj s)).clm_comp (b.toUnconditionalSchauderBasis.proj s)⟩
  map_add' k l := by
    apply Subtype.ext
    change (b.toUnconditionalSchauderBasis.proj s).comp
        (((k : H →L[ℂ] H) + (l : H →L[ℂ] H)).comp (b.toUnconditionalSchauderBasis.proj s)) = _
    rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
    rfl
  map_smul' c k := by
    apply Subtype.ext
    change (b.toUnconditionalSchauderBasis.proj s).comp
        ((c • (k : H →L[ℂ] H)).comp (b.toUnconditionalSchauderBasis.proj s)) = _
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    rfl

/-- Compact compression retains exactly the original operator composition. -/
@[simp]
theorem compactCompression_coe (s : Finset ι)
    (k : (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    (compactCompression b s k : H →L[ℂ] H) =
      (b.toUnconditionalSchauderBasis.proj s).comp ((k : H →L[ℂ] H).comp (b.toUnconditionalSchauderBasis.proj s)) := rfl

/-- The original compact operator norm bounds every finite compression. -/
theorem norm_compactCompression_le (s : Finset ι)
    (k : (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    ‖compactCompression b s k‖ ≤ ‖k‖ := by
  change ‖(b.toUnconditionalSchauderBasis.proj s).comp
      ((k : H →L[ℂ] H).comp (b.toUnconditionalSchauderBasis.proj s))‖ ≤ ‖(k : H →L[ℂ] H)‖
  exact HilbertBasis.norm_sandwich_le b b (k : H →L[ℂ] H) s s

/-- Forward the existing compact-sandwich convergence along the diagonal finite-subset net. -/
theorem compactCompression_tendsto
    (k : (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    Tendsto (fun s : Finset ι => compactCompression b s k) atTop (𝓝 k) := by
  classical
  have hdiag : Tendsto (fun s : Finset ι => (s, s)) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_id.prodMk tendsto_id
  have h := (b.tendsto_compact_sandwich b k.property).comp hdiag
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hεEvent := Metric.tendsto_nhds.mp h ε hε
  filter_upwards [hεEvent] with s hs
  change dist ((b.toUnconditionalSchauderBasis.proj s).comp
    ((k : H →L[ℂ] H).comp (b.toUnconditionalSchauderBasis.proj s))) (k : H →L[ℂ] H) < ε
  exact hs

/-- The actual compression has exactly its original finite-frame matrix-entry rank-one expansion. -/
theorem compactCompression_eq_sum (s : Finset ι)
    (k : (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    compactCompression b s k =
      ∑ i : s, ∑ j : s,
        inner ℂ (b (i : ι)) ((k : H →L[ℂ] H) (b (j : ι))) •
          hilbertCompactRankOne H (b (i : ι)) (b (j : ι)) := by
  have hcoe :
      (((∑ i : s, ∑ j : s,
        inner ℂ (b (i : ι)) ((k : H →L[ℂ] H) (b (j : ι))) •
          hilbertCompactRankOne H (b (i : ι)) (b (j : ι))) :
          (compactEndomorphismClosedStarIdeal (H := H)).carrier) : H →L[ℂ] H) =
        ∑ i : s, ∑ j : s,
          inner ℂ (b (i : ι)) ((k : H →L[ℂ] H) (b (j : ι))) •
            InnerProductSpace.rankOne ℂ (b (i : ι)) (b (j : ι)) := by
    change NonUnitalStarSubalgebraClass.subtype (R := ℂ)
        (compactEndomorphismClosedStarIdeal (H := H)).carrier
        (∑ i : s, ∑ j : s,
          inner ℂ (b (i : ι)) ((k : H →L[ℂ] H) (b (j : ι))) •
            hilbertCompactRankOne H (b (i : ι)) (b (j : ι))) = _
    simp only [map_sum, map_smul, NonUnitalStarSubalgebraClass.subtype_apply,
      hilbertCompactRankOne_coe]
  apply Subtype.ext
  rw [compactCompression_coe, hcoe]
  have hsum :
      (∑ j : s, ∑ i : s,
        inner ℂ (b (j : ι)) ((k : H →L[ℂ] H) (b (i : ι))) •
          InnerProductSpace.rankOne ℂ (b (j : ι)) (b (i : ι))) =
        ∑ j ∈ s, ∑ i ∈ s,
          inner ℂ (b j) ((k : H →L[ℂ] H) (b i)) •
            InnerProductSpace.rankOne ℂ (b j) (b i) := by
    calc
      _ = ∑ j : s, ∑ i ∈ s,
          inner ℂ (b (j : ι)) ((k : H →L[ℂ] H) (b i)) •
            InnerProductSpace.rankOne ℂ (b (j : ι)) (b i) := by
        apply Finset.sum_congr rfl
        intro j _
        exact Finset.sum_coe_sort s (fun i : ι =>
          inner ℂ (b (j : ι)) ((k : H →L[ℂ] H) (b i)) •
            InnerProductSpace.rankOne ℂ (b (j : ι)) (b i))
      _ = _ := Finset.sum_coe_sort s (fun j : ι => ∑ i ∈ s,
        inner ℂ (b j) ((k : H →L[ℂ] H) (b i)) •
          InnerProductSpace.rankOne ℂ (b j) (b i))
  exact (HilbertBasis.proj_comp_proj_eq_sum_rankOne b b (k : H →L[ℂ] H) s s).trans hsum.symm

end CStarModule.HilbertAmplification
