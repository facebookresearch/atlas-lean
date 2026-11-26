/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.TalagrandConcentration
public import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# Tests for Talagrand's concentration inequality around a median

The inequality applied to the Euclidean norm of a vector of independent bounded variables, to
every convex `1`-Lipschitz function of a uniform point of the cube `[0, 1]^n`, whose coordinates
are independent by construction, and to the first coordinate of a uniform point of
`[0, 1]^(N + 1)`, whose median `1 / 2` is computed, so that every hypothesis is checked on a
concrete example.
-/

@[expose] public section

namespace MathlibExtTest.Probability.TalagrandConcentration

open MeasureTheory ProbabilityTheory Real MathlibExt.Probability.TalagrandConcentrationWanted
open scoped unitInterval

/-- The Euclidean norm of a vector of independent variables bounded by `K` concentrates around
any of its medians at scale `K`, with constants that do not depend on the dimension. -/
example : ∃ C > 0, ∃ c > 0, ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω),
    IsProbabilityMeasure P → ∀ (n : ℕ) (X : Fin n → Ω → ℝ) (K : ℝ), 0 < K →
    (∀ i, Measurable (X i)) → iIndepFun X P → (∀ i ω, |X i ω| ≤ K) →
    ∀ m : ℝ, 1 / 2 ≤ P.real {ω | ‖(WithLp.toLp 2 fun i => X i ω : EuclideanSpace ℝ (Fin n))‖ ≤ m} →
      1 / 2 ≤ P.real {ω | m ≤ ‖(WithLp.toLp 2 fun i => X i ω : EuclideanSpace ℝ (Fin n))‖} →
    ∀ t : ℝ, 0 < t →
      P.real {ω | t * K ≤ |‖(WithLp.toLp 2 fun i => X i ω : EuclideanSpace ℝ (Fin n))‖ - m|} ≤
        C * exp (-c * t ^ 2) := by
  obtain ⟨C, hC, c, hc, h⟩ := talagrand_concentration_median
  exact ⟨C, hC, c, hc, fun Ω _ P hP n X K hK hXm hXi hXK =>
    h Ω _ P hP n X K hK hXm hXi hXK _ (convexOn_norm convex_univ) lipschitzWith_one_norm⟩

/-- For the uniform probability on the cube `[0, 1]^n`, the coordinates are independent and
bounded by `1`: a convex `1`-Lipschitz function of a uniform point deviates from a median by at
least `t` with probability at most `C exp(-c t²)`, whatever the dimension `n`. -/
example : ∃ C > 0, ∃ c > 0, ∀ (n : ℕ) (F : EuclideanSpace ℝ (Fin n) → ℝ),
    ConvexOn ℝ Set.univ F → LipschitzWith 1 F → ∀ m : ℝ,
    1 / 2 ≤ (Measure.pi fun _ => (volume : Measure I)).real
      {x | F (WithLp.toLp 2 fun i => (x i : ℝ)) ≤ m} →
    1 / 2 ≤ (Measure.pi fun _ => (volume : Measure I)).real
      {x | m ≤ F (WithLp.toLp 2 fun i => (x i : ℝ))} →
    ∀ t : ℝ, 0 < t →
      (Measure.pi fun _ => (volume : Measure I)).real
        {x | t ≤ |F (WithLp.toLp 2 fun i => (x i : ℝ)) - m|} ≤ C * exp (-c * t ^ 2) := by
  obtain ⟨C, hC, c, hc, h⟩ := talagrand_concentration_median
  refine ⟨C, hC, c, hc, fun n F hFc hFL m hm₁ hm₂ t ht => ?_⟩
  simpa only [mul_one] using h (Fin n → I) _ (Measure.pi fun _ => volume) inferInstance n
    (fun i x => (x i : ℝ)) 1 one_pos
    (fun i => measurable_subtype_coe.comp (measurable_pi_apply i))
    (iIndepFun_pi fun _ => measurable_subtype_coe.aemeasurable)
    (fun i x => abs_le.mpr ⟨by linarith [unitInterval.nonneg (x i)], unitInterval.le_one (x i)⟩)
    F hFc hFL m hm₁ hm₂ t ht

/-- The first coordinate of a vector of `EuclideanSpace ℝ (Fin (N + 1))`. -/
def firstCoord (N : ℕ) (v : EuclideanSpace ℝ (Fin (N + 1))) : ℝ := v 0

/-- The first coordinate is linear, hence convex. -/
theorem convexOn_firstCoord (N : ℕ) : ConvexOn ℝ Set.univ (firstCoord N) :=
  ⟨convex_univ, fun v _ w _ a b _ _ _ => by simp [firstCoord]⟩

/-- The first coordinate is `1`-Lipschitz for the Euclidean metric. -/
theorem lipschitzWith_firstCoord (N : ℕ) : LipschitzWith 1 (firstCoord N) :=
  LipschitzWith.of_dist_le_mul fun v w => by simpa [firstCoord] using PiLp.dist_apply_le v w 0

/-- `1 / 2` is a median of the first coordinate of a uniform point of `[0, 1]^(N + 1)`: the
half-cube `{x | x₀ ≤ 1 / 2}` has probability `1 / 2`. -/
theorem measureReal_firstCoord_le (N : ℕ) :
    (Measure.pi fun _ => (volume : Measure I)).real
      {x : Fin (N + 1) → I | firstCoord N (WithLp.toLp 2 fun i => (x i : ℝ)) ≤ 1 / 2} = 1 / 2 := by
  have hset : {x : Fin (N + 1) → I | firstCoord N (WithLp.toLp 2 fun i => (x i : ℝ)) ≤ 1 / 2} =
      Function.eval 0 ⁻¹' Set.Iic ⟨1 / 2, by norm_num, by norm_num⟩ := by
    ext x
    simp [firstCoord, ← Subtype.coe_le_coe]
  rw [hset, measureReal_def, (measurePreserving_eval (fun _ => (volume : Measure I)) 0)
    |>.measure_preimage measurableSet_Iic.nullMeasurableSet, unitInterval.volume_Iic,
    ENNReal.toReal_ofReal (by norm_num)]

/-- The other half of the median condition: the half-cube `{x | 1 / 2 ≤ x₀}` has probability
`1 / 2`. -/
theorem measureReal_le_firstCoord (N : ℕ) :
    (Measure.pi fun _ => (volume : Measure I)).real
      {x : Fin (N + 1) → I | 1 / 2 ≤ firstCoord N (WithLp.toLp 2 fun i => (x i : ℝ))} = 1 / 2 := by
  have hset : {x : Fin (N + 1) → I | 1 / 2 ≤ firstCoord N (WithLp.toLp 2 fun i => (x i : ℝ))} =
      Function.eval 0 ⁻¹' Set.Ici ⟨1 / 2, by norm_num, by norm_num⟩ := by
    ext x
    simp [firstCoord, ← Subtype.coe_le_coe]
  rw [hset, measureReal_def, (measurePreserving_eval (fun _ => (volume : Measure I)) 0)
    |>.measure_preimage measurableSet_Ici.nullMeasurableSet, unitInterval.volume_Ici,
    ENNReal.toReal_ofReal (by norm_num)]
  norm_num

/-- With every hypothesis checked: for a uniform point `x` of `[0, 1]^(N + 1)`, the first
coordinate deviates from its median `1 / 2` by at least `t` with probability at most
`C exp(-c t²)`, with the constants of the theorem. -/
example : ∃ C > 0, ∃ c > 0, ∀ (N : ℕ) (t : ℝ), 0 < t →
    (Measure.pi fun _ => (volume : Measure I)).real
      {x : Fin (N + 1) → I | t ≤ |firstCoord N (WithLp.toLp 2 fun i => (x i : ℝ)) - 1 / 2|} ≤
        C * exp (-c * t ^ 2) := by
  obtain ⟨C, hC, c, hc, h⟩ := talagrand_concentration_median
  refine ⟨C, hC, c, hc, fun N t ht => ?_⟩
  simpa only [mul_one] using h (Fin (N + 1) → I) _ (Measure.pi fun _ => volume) inferInstance
    (N + 1) (fun i x => (x i : ℝ)) 1 one_pos
    (fun i => measurable_subtype_coe.comp (measurable_pi_apply i))
    (iIndepFun_pi fun _ => measurable_subtype_coe.aemeasurable)
    (fun i x => abs_le.mpr ⟨by linarith [unitInterval.nonneg (x i)], unitInterval.le_one (x i)⟩)
    (firstCoord N) (convexOn_firstCoord N) (lipschitzWith_firstCoord N) (1 / 2)
    (measureReal_firstCoord_le N).ge (measureReal_le_firstCoord N).ge t ht

end MathlibExtTest.Probability.TalagrandConcentration
