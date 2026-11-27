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

public import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.Basic
public import Mathlib.MeasureTheory.Measure.Complex
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-!
# Scalar coefficient measures of a PVM

For a strongly countably additive PVM `E` on a measurable space `X`, acting on a complete
complex Hilbert space `H`, its coefficient measure is `μ_(g,h)(s)=⟨h,E(s)g⟩`. It is
complex-linear in `g` and conjugate-linear in `h`, using the inner-product convention linear in
the second argument.

For measurable `s`, total variation satisfies `|μ_(g,h)|(s)≤‖E(s)g‖‖h‖`. In particular,
`|μ_(g,h)|(X)≤‖g‖‖h‖`, so every coefficient measure has finite variation.

These are the scalar coefficients and variation bounds of Conway, A Course in Functional
Analysis, second edition, Chapter IX, Lemma 1.9.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace NNReal

namespace MathlibExt.Analysis.InnerProductSpace
namespace ProjectionValuedMeasure

noncomputable section

universe u v

variable {X : Type u} {H : Type v}
variable [MeasurableSpace X]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Finite complex coefficient measure of a PVM.** Let `X` be a measurable space and `H` a
complete complex Hilbert space. Let `E : ProjectionValuedMeasure X H` be a strongly
countably additive PVM. for `g,h ∈ H`, `scalarMeasure E g h : ComplexMeasure X` has value
`μ_(g,h)(s)=⟨h,E(s)g⟩` on each set and is linear in `g`, conjugate-linear in `h`. -/
noncomputable def scalarMeasure (E : ProjectionValuedMeasure X H) (g h : H) :
    ComplexMeasure X :=
  VectorMeasure.mapRangeL (innerSL ℂ h) (E.applyVectorMeasure g)

@[simp]
theorem scalarMeasure_apply (E : ProjectionValuedMeasure X H) (g h : H) (s : Set X) :
    E.scalarMeasure g h s = ⟪h, E s g⟫_ℂ := by
  change (innerSL ℂ h) (E.applyVectorMeasure g s) = ⟪h, E s g⟫_ℂ
  rfl

theorem scalarMeasure_add_left (E : ProjectionValuedMeasure X H) (g₁ g₂ h : H) :
    E.scalarMeasure (g₁ + g₂) h = E.scalarMeasure g₁ h + E.scalarMeasure g₂ h := by
  apply VectorMeasure.ext
  intro s hs
  simp [scalarMeasure_apply, map_add, inner_add_right]

theorem scalarMeasure_smul_left (E : ProjectionValuedMeasure X H) (c : ℂ) (g h : H) :
    E.scalarMeasure (c • g) h = c • E.scalarMeasure g h := by
  apply VectorMeasure.ext
  intro s hs
  simp [scalarMeasure_apply, map_smul, inner_smul_right]

theorem scalarMeasure_add_right (E : ProjectionValuedMeasure X H) (g h₁ h₂ : H) :
    E.scalarMeasure g (h₁ + h₂) = E.scalarMeasure g h₁ + E.scalarMeasure g h₂ := by
  apply VectorMeasure.ext
  intro s hs
  simp [scalarMeasure_apply, inner_add_left]

theorem scalarMeasure_smul_right (E : ProjectionValuedMeasure X H) (c : ℂ) (g h : H) :
    E.scalarMeasure g (c • h) = star c • E.scalarMeasure g h := by
  apply VectorMeasure.ext
  intro s hs
  simp [scalarMeasure_apply, inner_smul_left]

omit [CompleteSpace H] in
private theorem norm_finsetSum_sq_eq
    {ι : Type*} (u : Finset ι) (v : ι → H)
    (hv : ∀ i ∈ u, ∀ j ∈ u, i ≠ j → ⟪v i, v j⟫_ℂ = 0) :
    ‖∑ i ∈ u, v i‖ * ‖∑ i ∈ u, v i‖ =
      ∑ i ∈ u, ‖v i‖ * ‖v i‖ := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | @insert a u ha ih =>
      have haorth : ⟪v a, ∑ i ∈ u, v i⟫_ℂ = 0 := by
        rw [inner_sum]
        apply Finset.sum_eq_zero
        intro i hi
        exact hv a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
          (fun hai ↦ ha (hai ▸ hi))
      rw [Finset.sum_insert ha,
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ haorth,
        ih (fun i hi j hj hij ↦ hv i (Finset.mem_insert_of_mem hi)
          j (Finset.mem_insert_of_mem hj) hij),
        Finset.sum_insert ha]

private theorem sum_norm_scalarMeasure_le
    (E : ProjectionValuedMeasure X H) (g h : H) {s : Set X} (hs : MeasurableSet s)
    (P : Finset (Set X)) (hPsub : ∀ t ∈ P, t ⊆ s)
    (hPdisj : (P : Set (Set X)).PairwiseDisjoint id)
    (hPmeas : ∀ t ∈ P, MeasurableSet t) :
    ∑ t ∈ P, ‖E.scalarMeasure g h t‖ ≤ ‖E s g‖ * ‖h‖ := by
  classical
  let μ : ComplexMeasure X := E.scalarMeasure g h
  choose c hc_norm hc_phase using fun t : Set X ↦ Complex.exists_norm_eq_mul_self (μ t)
  let v : Set X → H := fun t ↦ c t • E t g
  have horthE : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → ⟪E i g, E j g⟫_ℂ = 0 := by
    intro i hi j hj hij
    exact E.inner_apply_eq_zero_of_disjoint (hPmeas i hi) (hPmeas j hj)
      (hPdisj hi hj hij) g g
  have horthv : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → ⟪v i, v j⟫_ℂ = 0 := by
    intro i hi j hj hij
    simp only [v, inner_smul_left, inner_smul_right, horthE i hi j hj hij,
      mul_zero, starRingEnd_apply]
  have hnormsum : ‖∑ t ∈ P, v t‖ = ‖∑ t ∈ P, E t g‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [pow_two]
    rw [norm_finsetSum_sq_eq P v horthv,
      norm_finsetSum_sq_eq P (fun t ↦ E t g) horthE]
    apply Finset.sum_congr rfl
    intro t ht
    rw [norm_smul, hc_norm t, one_mul]
  let U : Set X := ⋃ t ∈ P, t
  have hUmeas : MeasurableSet U := by
    dsimp only [U]
    exact MeasurableSet.biUnion (Finset.countable_toSet P) (by simpa using hPmeas)
  have hUsub : U ⊆ s := by
    dsimp only [U]
    exact iUnion₂_subset fun t ht ↦ hPsub t ht
  have hsumE : ∑ t ∈ P, E t g = E U g := by
    have hsumOp := E.biUnion_finset P id hPmeas hPdisj
    have happ := congrArg (fun T : H →L[ℂ] H ↦ T g) hsumOp
    simpa only [U, sum_apply, id_eq] using happ.symm
  have hproj : E U g = E U (E s g) := by
    have hinter := E.inter U hUmeas s hs
    rw [Set.inter_eq_left.mpr hUsub] at hinter
    calc
      E U g = (E U * E s) g := congrArg (fun T : H →L[ℂ] H ↦ T g) hinter
      _ = E U (E s g) := rfl
  have hsumE_le : ‖∑ t ∈ P, E t g‖ ≤ ‖E s g‖ := by
    rw [hsumE, hproj]
    calc
      ‖E U (E s g)‖ ≤ ‖E U‖ * ‖E s g‖ := E U |>.le_opNorm _
      _ ≤ 1 * ‖E s g‖ := by
        gcongr
        exact IsStarProjection.norm_le _ (E.isStarProjection U)
      _ = ‖E s g‖ := one_mul _
  have hphase : ((∑ t ∈ P, ‖μ t‖ : ℝ) : ℂ) = ⟪h, ∑ t ∈ P, v t⟫_ℂ := by
    rw [inner_sum]
    push_cast
    apply Finset.sum_congr rfl
    intro t ht
    rw [show ⟪h, v t⟫_ℂ = c t * μ t by
      simp only [v, inner_smul_right, μ, scalarMeasure_apply]]
    exact hc_phase t
  calc
    ∑ t ∈ P, ‖E.scalarMeasure g h t‖ = ‖((∑ t ∈ P, ‖μ t‖ : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]
    _ = ‖⟪h, ∑ t ∈ P, v t⟫_ℂ‖ := congrArg norm hphase
    _ ≤ ‖h‖ * ‖∑ t ∈ P, v t‖ := norm_inner_le_norm _ _
    _ = ‖h‖ * ‖∑ t ∈ P, E t g‖ := by rw [hnormsum]
    _ ≤ ‖h‖ * ‖E s g‖ := mul_le_mul_of_nonneg_left hsumE_le (norm_nonneg _)
    _ = ‖E s g‖ * ‖h‖ := mul_comm _ _

/-- **Local total-variation bound for a spectral coefficient.** Let `X` be a measurable space
and `H` a complete complex Hilbert space. Let `E : ProjectionValuedMeasure X H` be a
strongly countably additive PVM. Write `μ_(g,h)(s)=⟨h,E(s)g⟩` for its scalar coefficient
measures. for measurable `s ⊆ X`, `|μ_(g,h)|(s)≤‖E(s)g‖*‖h‖`, with the finite nonnegative
bound embedded in `[0,∞]`. -/
theorem scalarMeasure_variation_le (E : ProjectionValuedMeasure X H) (g h : H)
    {s : Set X} (hs : MeasurableSet s) :
    (E.scalarMeasure g h).variation s ≤
      (((‖E s g‖₊ * ‖h‖₊ : ℝ≥0) : ℝ≥0∞)) := by
  let μ : ComplexMeasure X := E.scalarMeasure g h
  let C : ℝ≥0∞ := ((‖E s g‖₊ * ‖h‖₊ : ℝ≥0) : ℝ≥0∞)
  by_contra hle
  have hlt : C < μ.variation s := lt_of_not_ge hle
  obtain ⟨P, hPsub, hPdisj, hPmeas, hPsum⟩ :=
    VectorMeasure.exists_lt_sum_of_lt_variation μ hs hlt
  have hreal := sum_norm_scalarMeasure_le E g h hs P hPsub hPdisj hPmeas
  have hnnreal : ∑ t ∈ P, ‖μ t‖₊ ≤ ‖E s g‖₊ * ‖h‖₊ := by
    apply NNReal.coe_le_coe.mp
    simpa only [NNReal.coe_sum, coe_nnnorm, NNReal.coe_mul] using hreal
  have hennreal : ∑ t ∈ P, ‖μ t‖ₑ ≤ C := by
    have hcoe := ENNReal.coe_le_coe.mpr hnnreal
    simpa only [enorm_eq_nnnorm, ENNReal.ofNNReal_finsetSum, C] using hcoe
  exact (not_lt_of_ge hennreal) hPsum

/-- **Global total-variation bound for a spectral coefficient.** Let `X` be a measurable space
and `H` a complete complex Hilbert space. Let `E : ProjectionValuedMeasure X H` be a
strongly countably additive PVM. Write `μ_(g,h)(s)=⟨h,E(s)g⟩` for its scalar coefficient
measures. `|μ_(g,h)|(X)≤‖g‖*‖h‖` for every `g,h ∈ H`. -/
theorem scalarMeasure_variation_univ_le (E : ProjectionValuedMeasure X H) (g h : H) :
    (E.scalarMeasure g h).variation Set.univ ≤
      (((‖g‖₊ * ‖h‖₊ : ℝ≥0) : ℝ≥0∞)) := by
  simpa only [E.univ, one_apply_eq_self] using
    E.scalarMeasure_variation_le g h MeasurableSet.univ

/-- **Finite variation of PVM coefficient measures.** Let `X` be a measurable space and `H` a
complete complex Hilbert space. Let `E : ProjectionValuedMeasure X H` be a strongly
countably additive PVM. Write `μ_(g,h)(s)=⟨h,E(s)g⟩` for its scalar coefficient measures.
for `g,h ∈ H`, the positive measure `|μ_(g,h)|` is finite, with total mass at most
`‖g‖‖h‖`. -/
noncomputable instance instIsFiniteMeasureVariationScalarMeasure
    (E : ProjectionValuedMeasure X H) (g h : H) :
    IsFiniteMeasure (E.scalarMeasure g h).variation where
  measure_univ_lt_top :=
    (E.scalarMeasure_variation_univ_le g h).trans_lt (by finiteness)

theorem scalarMeasure_variation_univ_lt_top
    (E : ProjectionValuedMeasure X H) (g h : H) :
    (E.scalarMeasure g h).variation Set.univ < ∞ := by
  finiteness

/-- **Real-valued local variation estimate.** Let `X` be a measurable space and `H` a complete
complex Hilbert space. Let `E : ProjectionValuedMeasure X H` be a strongly countably
additive PVM. Write `μ_(g,h)(s)=⟨h,E(s)g⟩` for its scalar coefficient measures. for
measurable `s`, the real mass `|μ_(g,h)|.real(s)` is at most `‖E(s)g‖*‖h‖`. -/
theorem scalarMeasure_variation_real_le (E : ProjectionValuedMeasure X H) (g h : H)
    {s : Set X} (hs : MeasurableSet s) :
    (E.scalarMeasure g h).variation.real s ≤ ‖E s g‖ * ‖h‖ := by
  rw [measureReal_def]
  calc
    ((E.scalarMeasure g h).variation s).toReal ≤
        ((((‖E s g‖₊ * ‖h‖₊ : ℝ≥0) : ℝ≥0∞))).toReal :=
      ENNReal.toReal_mono (by finiteness) (E.scalarMeasure_variation_le g h hs)
    _ = ‖E s g‖ * ‖h‖ := by simp

/-- **Real total variation of a spectral coefficient.** Let `X` be a measurable space and `H`
a complete complex Hilbert space. Let `E : ProjectionValuedMeasure X H` be a strongly
countably additive PVM. Write `μ_(g,h)(s)=⟨h,E(s)g⟩` for its scalar coefficient measures.
the real total mass satisfies `|μ_(g,h)|.real(X)≤‖g‖*‖h‖`. -/
theorem scalarMeasure_variation_real_univ_le
    (E : ProjectionValuedMeasure X H) (g h : H) :
    (E.scalarMeasure g h).variation.real Set.univ ≤ ‖g‖ * ‖h‖ := by
  simpa only [E.univ, one_apply_eq_self] using
    E.scalarMeasure_variation_real_le g h MeasurableSet.univ

end

end ProjectionValuedMeasure
end MathlibExt.Analysis.InnerProductSpace
