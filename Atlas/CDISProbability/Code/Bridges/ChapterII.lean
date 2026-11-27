/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# CDIS Probabilités II: bridge statements

* id 33: the correlation coefficient `correlation`, which Mathlib does not define; the
  covariance is Mathlib's `cov[X, Y; P]`.
* id 34: Cauchy-Schwarz `|E(XY)| ≤ E|XY| ≤ √(E X² E Y²)`, with the equality case, which Mathlib
  does not state for random variables.
* id 42: two real random variables with densities `f_X`, `f_Y` are independent iff the pair
  `(X, Y)` has density `f_X(x) f_Y(y)` on `ℝ²`.
* id 44: independent square-integrable variables have zero covariance and correlation.

For id 42, Mathlib's `pdf.indepFun_iff_pdf_prod_eq_pdf_mul_pdf` assumes that the pair already has
a density. The course only assumes that `X` and `Y` do, so the faithful statement goes through
`indepFun_iff_map_prod_eq_prod_map_map` and `prod_withDensity` instead.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace CDIS

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Covariance

/-- CDIS P.II, id 33: the correlation coefficient `ρ(X, Y) = Cov(X, Y) / (√V(X) √V(Y))`,
meaningful when `V(X) > 0` and `V(Y) > 0`. -/
noncomputable def correlation (X Y : Ω → ℝ) (P : Measure Ω) : ℝ :=
  cov[X, Y; P] / (√(Var[X; P]) * √(Var[Y; P]))

omit [IsProbabilityMeasure P] in
/-- CDIS P.II, id 44: independent square-integrable random variables have
`Cov(X, Y) = 0` and `ρ(X, Y) = 0`. -/
theorem covariance_correlation_eq_zero_of_indepFun {X Y : Ω → ℝ} (h : IndepFun X Y P)
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P) : cov[X, Y; P] = 0 ∧ correlation X Y P = 0 := by
  have h0 := h.covariance_eq_zero hX hY
  exact ⟨h0, by simp [correlation, h0]⟩

end Covariance

section CauchySchwarz

omit [IsProbabilityMeasure P] in
/-- `E(XY)` is the inner product of `X` and `Y` in `L²`. -/
lemma inner_toLp_two {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    @inner ℝ _ _ (hX.toLp X) (hY.toLp Y) = ∫ ω, X ω * Y ω ∂P := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hX.coeFn_toLp, hY.coeFn_toLp] with ω h1 h2
  simp [h1, h2, mul_comm]

omit [IsProbabilityMeasure P] in
/-- `√(E(X²))` is the norm of `X` in `L²`. -/
lemma norm_toLp_two {X : Ω → ℝ} (hX : MemLp X 2 P) :
    ‖hX.toLp X‖ = √(∫ ω, X ω ^ 2 ∂P) := by
  rw [← Real.sqrt_sq (norm_nonneg _), ← real_inner_self_eq_norm_sq, inner_toLp_two hX hX]
  simp [sq]

omit [IsProbabilityMeasure P] in
/-- CDIS P.II, id 34 (Cauchy-Schwarz inequality): `|E(XY)| ≤ E(|XY|) ≤ √(E(X²) E(Y²))`, with
equality `|E(XY)| = √(E(X²) E(Y²))` iff `X` and `Y` are almost surely proportional. The course
attaches the equality case to the chain; it holds for this, the Cauchy-Schwarz, equality, while
`E(|XY|) = √(E(X²) E(Y²))` only makes `|X|` and `|Y|` proportional. -/
theorem cauchy_schwarz {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    |∫ ω, X ω * Y ω ∂P| ≤ ∫ ω, |X ω * Y ω| ∂P ∧
      ∫ ω, |X ω * Y ω| ∂P ≤ √((∫ ω, X ω ^ 2 ∂P) * ∫ ω, Y ω ^ 2 ∂P) ∧
      (|∫ ω, X ω * Y ω ∂P| = √((∫ ω, X ω ^ 2 ∂P) * ∫ ω, Y ω ^ 2 ∂P) ↔
        (∃ c : ℝ, X =ᵐ[P] fun ω ↦ c * Y ω) ∨ ∃ c : ℝ, Y =ᵐ[P] fun ω ↦ c * X ω) := by
  have hsq : ∀ {Z : Ω → ℝ}, √((∫ ω, X ω ^ 2 ∂P) * ∫ ω, Z ω ^ 2 ∂P) =
      √(∫ ω, X ω ^ 2 ∂P) * √(∫ ω, Z ω ^ 2 ∂P) :=
    Real.sqrt_mul (integral_nonneg fun _ ↦ sq_nonneg _) _
  refine ⟨?_, ?_, ?_⟩
  · simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun ω ↦ X ω * Y ω)
  · have h := real_inner_le_norm (hX.abs.toLp _) (hY.abs.toLp _)
    rw [inner_toLp_two, norm_toLp_two, norm_toLp_two] at h
    rw [hsq]
    simpa [abs_mul] using h
  · have htfae : ‖@inner ℝ _ _ (hX.toLp X) (hY.toLp Y)‖ = ‖hX.toLp X‖ * ‖hY.toLp Y‖ ↔
        hX.toLp X = 0 ∨ ∃ r : ℝ, hY.toLp Y = r • hX.toLp X :=
      (norm_inner_eq_norm_tfae (𝕜 := ℝ) _ _).out 1 3
    rw [hsq, ← norm_toLp_two hX, ← norm_toLp_two hY, ← inner_toLp_two hX hY,
      ← Real.norm_eq_abs, htfae]
    have hzero : hX.toLp X = 0 ↔ X =ᵐ[P] 0 := by
      rw [Lp.eq_zero_iff_ae_eq_zero]
      exact ⟨fun h ↦ hX.coeFn_toLp.symm.trans h, fun h ↦ hX.coeFn_toLp.trans h⟩
    have hmul : ∀ r : ℝ, hY.toLp Y = r • hX.toLp X ↔ Y =ᵐ[P] fun ω ↦ r * X ω := by
      intro r
      rw [← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
      rfl
    simp only [hzero, hmul]
    constructor
    · rintro (h | ⟨r, h⟩)
      · exact Or.inl ⟨0, h.trans (Eventually.of_forall fun ω ↦ by simp)⟩
      · exact Or.inr ⟨r, h⟩
    · rintro (⟨c, h⟩ | ⟨r, h⟩)
      · rcases eq_or_ne c 0 with rfl | hc
        · exact Or.inl (h.trans (Eventually.of_forall fun ω ↦ by simp))
        · refine Or.inr ⟨c⁻¹, ?_⟩
          filter_upwards [h] with ω hω
          rw [hω, inv_mul_cancel_left₀ hc]
      · exact Or.inr ⟨r, h⟩

end CauchySchwarz

section Independence

/-- CDIS P.II, id 42 (characterisation of independence by densities). -/
theorem indepFun_iff_map_eq_withDensity_mul {X Y : Ω → ℝ} (hX : Measurable X)
    (hY : Measurable Y) {fX fY : ℝ → ℝ≥0∞} (hfX : Measurable fX) (hfY : Measurable fY)
    (hlawX : P.map X = volume.withDensity fX) (hlawY : P.map Y = volume.withDensity fY) :
    IndepFun X Y P ↔
      P.map (fun ω ↦ (X ω, Y ω)) = volume.withDensity (fun z : ℝ × ℝ ↦ fX z.1 * fY z.2) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable, hlawX, hlawY,
    prod_withDensity hfX hfY, Measure.volume_eq_prod]

end Independence

end CDIS
