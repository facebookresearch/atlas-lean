/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ConvexDistanceInequality
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Talagrand's concentration inequality around a median

Let `X₁, …, Xₙ` be independent real random variables bounded by `K` and let `F : ℝⁿ → ℝ` be
convex and `1`-Lipschitz for the Euclidean metric. Then `F(X)` concentrates around its median at
scale `K` with Gaussian tails: `P(|F(X) - m| ≥ λK) ≤ C exp(-cλ²)` for every median `m` of `F(X)`
and every `λ > 0`, with absolute constants `C, c > 0` that depend on neither `n`, `K`, `F` nor the
laws of the `Xᵢ` (`talagrand_concentration_median`, proved with `C = 4` and `c = 1 / 16`). Unlike
McDiarmid's inequality, the deviation scale `K` does not grow with `n`.

Tao states the theorem for complex variables and `F : ℂⁿ → ℝ`, identifying `ℂⁿ` with `ℝ²ⁿ`. The
statement below is the real case, which follows from the complex one by composing `F` with
`z ↦ Re z`. "For any `λ`" in the source means `λ > 0`: for `λ < 0` the event is certain while
the bound tends to `0`.

## Proof outline

The inequality is deduced from Talagrand's convex-distance inequality, in its tail form
`MathlibExt.Probability.ConvexDistanceWanted.measure_le_convexDistance_le`, for the product
probability `P^{⊗n}` on `Ωⁿ`.

* Under `P^{⊗n}`, the law of `Φ(ω) = (Xᵢ(ωᵢ))ᵢ` is the product of the laws of the `Xᵢ`, and so
  is the law of `X = (Xᵢ)ᵢ` under `P`, since the `Xᵢ` are independent: an event about `X` has
  the probability of the corresponding event about `Φ`.
* Let `A = {ω ∈ Ωⁿ | F(Φ(ω)) ≤ a}`. If `F(Φ(ω)) ≥ a + r`, the convex distance `f_c(A, ω)` is
  at least `r / (2K)`: for every point `v` of the convex hull of `U_A(ω)`, some `z` with
  `F(z) ≤ a` satisfies `|Φ(ω)ᵢ - zᵢ| ≤ 2K vᵢ` for every `i` (the vectors `v` with this property
  form a convex set, by convexity of `F`, and it contains `U_A(ω)`, since `|Xᵢ| ≤ K`), so
  `r ≤ F(Φ(ω)) - F(z) ≤ ‖Φ(ω) - z‖ ≤ 2K ‖v‖` as `F` is `1`-Lipschitz.
* The tail form of the convex-distance inequality then gives
  `P(F(X) ≤ a) · P(F(X) ≥ a + r) ≤ exp(-r² / (16K²))`. Taking `a = m` and `a = m - λK` with
  `r = λK`, and using that `P(F(X) ≤ m)` and `P(F(X) ≥ m)` are both at least `1 / 2`, bounds
  each of `P(F(X) ≥ m + λK)` and `P(F(X) ≤ m - λK)` by `2 exp(-λ² / 16)`, so that
  `P(|F(X) - m| ≥ λK) ≤ 4 exp(-λ² / 16)`.

## Implementation notes

The theorem keeps the full name it had in the wanted module, so its namespace still reads
`TalagrandConcentrationWanted`.

## References

* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS, 2012,
  Theorem 2.1.13, inequality `(2.18)`.
* M. Talagrand, *Concentration of measure and isoperimetric inequalities in product spaces*,
  Publ. Math. IHÉS 81 (1995), 73–205.
-/

@[expose] public section

namespace MathlibExt.Probability.TalagrandConcentrationWanted

open MeasureTheory ProbabilityTheory Real

/-- The geometric step: if `|Xᵢ| ≤ K`, `F` is convex and `1`-Lipschitz and
`F((Xᵢ(xᵢ))ᵢ) ≥ a + r`, the convex distance from `x` to the nonempty set
`A = {y | F((Xᵢ(yᵢ))ᵢ) ≤ a}` is at least `r / (2K)`. -/
private theorem div_le_convexDistance {Ω : Type*} {n : ℕ} {X : Fin n → Ω → ℝ} {K : ℝ}
    (hK : 0 < K) (hXK : ∀ i ω, |X i ω| ≤ K) {F : EuclideanSpace ℝ (Fin n) → ℝ}
    (hFc : ConvexOn ℝ Set.univ F) (hFL : LipschitzWith 1 F) {a r : ℝ}
    (hA : {y : Fin n → Ω | F (WithLp.toLp 2 fun i => X i (y i)) ≤ a}.Nonempty)
    {x : Fin n → Ω} (hx : a + r ≤ F (WithLp.toLp 2 fun i => X i (x i))) :
    r / (2 * K) ≤ ConvexDistance.convexDistance
      {y : Fin n → Ω | F (WithLp.toLp 2 fun i => X i (y i)) ≤ a} x := by
  set A := {y : Fin n → Ω | F (WithLp.toLp 2 fun i => X i (y i)) ≤ a}
  set p : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun i => X i (x i)
  -- The vectors `v` for which some point `z` of `{F ≤ a}` satisfies `|p i - z i| ≤ 2K v i`.
  set T : Set (EuclideanSpace ℝ (Fin n)) :=
    {v | ∃ z, F z ≤ a ∧ ∀ i, |p i - z i| ≤ 2 * K * v i}
  have hT : Convex ℝ T := by
    rintro v ⟨z, hz, hvz⟩ w ⟨z', hz', hwz'⟩ α β hα hβ hαβ
    refine ⟨α • z + β • z', ?_, fun i => ?_⟩
    · calc F (α • z + β • z') ≤ α • F z + β • F z' :=
            hFc.2 (Set.mem_univ _) (Set.mem_univ _) hα hβ hαβ
        _ ≤ α • a + β • a := by gcongr
        _ = a := by rw [smul_eq_mul, smul_eq_mul, ← add_mul, hαβ, one_mul]
    · have h : p i - (α • z + β • z') i = α * (p i - z i) + β * (p i - z' i) := by
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        linear_combination (p i) * hαβ.symm
      calc |p i - (α • z + β • z') i| = |α * (p i - z i) + β * (p i - z' i)| := by rw [h]
        _ ≤ |α * (p i - z i)| + |β * (p i - z' i)| := abs_add_le _ _
        _ = α * |p i - z i| + β * |p i - z' i| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hα, abs_of_nonneg hβ]
        _ ≤ α * (2 * K * v i) + β * (2 * K * w i) := by
            gcongr
            · exact hvz i
            · exact hwz' i
        _ = 2 * K * (α • v + β • w) i := by
            simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
            ring
  have hUT : ConvexDistance.convexSupport A x ⊆ T := by
    rintro s ⟨y, hy, hs01, hsy⟩
    refine ⟨WithLp.toLp 2 fun i => X i (y i), hy, fun i => ?_⟩
    rcases hs01 i with h0 | h1
    · simp [p, hsy i h0, h0]
    · rw [h1, mul_one]
      calc |p i - (WithLp.toLp 2 fun i => X i (y i)) i| = |X i (x i) - X i (y i)| := rfl
        _ ≤ |X i (x i)| + |X i (y i)| := abs_sub _ _
        _ ≤ K + K := add_le_add (hXK i (x i)) (hXK i (y i))
        _ = 2 * K := by ring
  have hne : (convexHull ℝ (ConvexDistance.convexSupport A x)).Nonempty :=
    (ConvexDistance.convexSupport_nonempty hA x).mono (subset_convexHull ℝ _)
  refine (Metric.le_infDist hne).mpr fun v hv => ?_
  obtain ⟨z, hz, hvz⟩ := convexHull_min hUT hT hv
  have h1 : r ≤ dist p z := by
    have h2 := hFL.dist_le_mul p z
    rw [NNReal.coe_one, one_mul, Real.dist_eq] at h2
    linarith [le_abs_self (F p - F z)]
  have h2 : dist p z ≤ 2 * K * ‖v‖ := by
    have hsq : dist p z ^ 2 ≤ (2 * K * ‖v‖) ^ 2 := by
      rw [PiLp.dist_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      calc dist (p i) (z i) ^ 2 = |p i - z i| ^ 2 := by rw [Real.dist_eq]
        _ ≤ (2 * K * v i) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hvz i) 2
        _ = (2 * K) ^ 2 * ‖v i‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs, mul_pow]
    exact (pow_le_pow_iff_left₀ dist_nonneg (by positivity) two_ne_zero).mp hsq
  rw [dist_zero_left, div_le_iff₀ (by positivity)]
  linarith

/-- The two-level form: under the hypotheses of `talagrand_concentration_median`, for every level
`a` and every `r ≥ 0`, `P(F(X) ≤ a) · P(F(X) ≥ a + r) ≤ exp(-(r / (2K))² / 4)`. -/
private theorem measureReal_mul_measureReal_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n : ℕ} {X : Fin n → Ω → ℝ} {K : ℝ} (hK : 0 < K)
    (hXm : ∀ i, Measurable (X i)) (hXi : iIndepFun X P) (hXK : ∀ i ω, |X i ω| ≤ K)
    {F : EuclideanSpace ℝ (Fin n) → ℝ} (hFc : ConvexOn ℝ Set.univ F) (hFL : LipschitzWith 1 F)
    (a : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    P.real {ω | F (WithLp.toLp 2 fun i => X i ω) ≤ a} *
      P.real {ω | a + r ≤ F (WithLp.toLp 2 fun i => X i ω)} ≤
        exp (-(r / (2 * K)) ^ 2 / 4) := by
  set G : (Fin n → ℝ) → ℝ := fun x => F (WithLp.toLp 2 x)
  have hGm : Measurable G := (hFL.continuous.comp (PiLp.continuous_toLp 2 _)).measurable
  set Q : Measure (Fin n → Ω) := Measure.pi fun _ => P
  set Φ : (Fin n → Ω) → (Fin n → ℝ) := fun y i => X i (y i)
  have hΦm : Measurable Φ := Measurable.of_eval fun i => (hXm i).comp (measurable_pi_apply i)
  have hXm' : Measurable fun ω i => X i ω := Measurable.of_eval hXm
  -- `Φ` has under `Q = P^{⊗n}` the law of `(X i)ᵢ` under `P`: both are the product of the laws.
  have hlaw : Q.map Φ = P.map (fun ω i => X i ω) := by
    rw [hXi.map_fun_eq_pi_map fun i => (hXm i).aemeasurable]
    exact Measure.pi_map_pi fun i => (hXm i).aemeasurable
  have htr : ∀ E : Set (Fin n → ℝ), MeasurableSet E →
      Q (Φ ⁻¹' E) = P ((fun ω i => X i ω) ⁻¹' E) := fun E hE => by
    rw [← Measure.map_apply hΦm hE, hlaw, Measure.map_apply hXm' hE]
  set A : Set (Fin n → Ω) := Φ ⁻¹' {x | G x ≤ a}
  have hAm : MeasurableSet A := hΦm (measurableSet_le hGm measurable_const)
  have hQA : Q A = P {ω | F (WithLp.toLp 2 fun i => X i ω) ≤ a} :=
    htr _ (measurableSet_le hGm measurable_const)
  have hQB : Q (Φ ⁻¹' {x | a + r ≤ G x}) = P {ω | a + r ≤ F (WithLp.toLp 2 fun i => X i ω)} :=
    htr _ (measurableSet_le measurable_const hGm)
  rcases eq_or_ne (Q A) 0 with h0 | h0
  · rw [measureReal_def, ← hQA, h0, ENNReal.toReal_zero, zero_mul]
    positivity
  have hAne : A.Nonempty := Set.nonempty_iff_ne_empty.mpr fun h => h0 (by rw [h, measure_empty])
  have hsub : Φ ⁻¹' {x | a + r ≤ G x} ⊆ {y | r / (2 * K) ≤ ConvexDistance.convexDistance A y} :=
    fun y hy => div_le_convexDistance hK hXK hFc hFL hAne hy
  have htail := ConvexDistanceWanted.measure_le_convexDistance_le P n hAm
    (t := r / (2 * K)) (by positivity)
  have hle : Q A * Q (Φ ⁻¹' {x | a + r ≤ G x}) ≤
      ENNReal.ofReal (exp (-(r / (2 * K)) ^ 2 / 4)) :=
    calc Q A * Q (Φ ⁻¹' {x | a + r ≤ G x})
        ≤ Q A * (ENNReal.ofReal (exp (-(r / (2 * K)) ^ 2 / 4)) * (Q A)⁻¹) := by
          gcongr
          exact (measure_mono hsub).trans htail
      _ = ENNReal.ofReal (exp (-(r / (2 * K)) ^ 2 / 4)) := by
          rw [mul_comm, mul_assoc, ENNReal.inv_mul_cancel h0 (measure_ne_top _ _), mul_one]
  rw [measureReal_def, measureReal_def, ← hQA, ← hQB, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_le_of_le_ofReal (exp_pos _).le hle

/-- **Talagrand's concentration inequality around a median** (Tao, *Topics in Random Matrix
Theory*, Theorem 2.1.13, `(2.18)`, real case). There are absolute constants `C, c > 0` such
that: if `X₁, …, Xₙ` are independent real random variables with `|Xᵢ| ≤ K` (`K > 0`), `F` is a
convex `1`-Lipschitz function on Euclidean `ℝⁿ`, and `m` is a median of `F(X)`, then
`P(|F(X) - m| ≥ λK) ≤ C exp(-cλ²)` for every `λ > 0`. -/
theorem talagrand_concentration_median :
    ∃ C > 0, ∃ c > 0, ∀ (Ω : Type*) (_ : MeasurableSpace Ω) (P : Measure Ω),
      IsProbabilityMeasure P → ∀ (n : ℕ) (X : Fin n → Ω → ℝ) (K : ℝ), 0 < K →
      (∀ i, Measurable (X i)) → iIndepFun X P → (∀ i ω, |X i ω| ≤ K) →
      ∀ F : EuclideanSpace ℝ (Fin n) → ℝ, ConvexOn ℝ Set.univ F → LipschitzWith 1 F →
      ∀ m : ℝ, 1 / 2 ≤ P.real {ω | F (WithLp.toLp 2 fun i => X i ω) ≤ m} →
        1 / 2 ≤ P.real {ω | m ≤ F (WithLp.toLp 2 fun i => X i ω)} →
      ∀ t : ℝ, 0 < t →
        P.real {ω | t * K ≤ |F (WithLp.toLp 2 fun i => X i ω) - m|} ≤ C * exp (-c * t ^ 2) := by
  refine ⟨4, by norm_num, 1 / 16, by norm_num, ?_⟩
  intro Ω _ P hP n X K hK hXm hXi hXK F hFc hFL m hm₁ hm₂ t ht
  have he : exp (-(t * K / (2 * K)) ^ 2 / 4) = exp (-(1 / 16) * t ^ 2) := by
    congr 1
    field_simp
    ring
  have hup := measureReal_mul_measureReal_le P hK hXm hXi hXK hFc hFL m (r := t * K)
    (by positivity)
  have hlow := measureReal_mul_measureReal_le P hK hXm hXi hXK hFc hFL (m - t * K)
    (r := t * K) (by positivity)
  rw [he] at hup hlow
  rw [sub_add_cancel] at hlow
  -- Upper tail: `P(F(X) ≤ m) ≥ 1/2` and the two-level form at `a = m`.
  have hup' : P.real {ω | m + t * K ≤ F (WithLp.toLp 2 fun i => X i ω)} ≤
      2 * exp (-(1 / 16) * t ^ 2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm₁)
      (measureReal_nonneg (μ := P) (s := {ω | m + t * K ≤ F (WithLp.toLp 2 fun i => X i ω)}))]
  -- Lower tail: `P(F(X) ≥ m) ≥ 1/2` and the two-level form at `a = m - tK`.
  have hlow' : P.real {ω | F (WithLp.toLp 2 fun i => X i ω) ≤ m - t * K} ≤
      2 * exp (-(1 / 16) * t ^ 2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm₂)
      (measureReal_nonneg (μ := P) (s := {ω | F (WithLp.toLp 2 fun i => X i ω) ≤ m - t * K}))]
  calc P.real {ω | t * K ≤ |F (WithLp.toLp 2 fun i => X i ω) - m|}
      ≤ P.real ({ω | m + t * K ≤ F (WithLp.toLp 2 fun i => X i ω)} ∪
          {ω | F (WithLp.toLp 2 fun i => X i ω) ≤ m - t * K}) := by
        refine measureReal_mono fun ω hω => ?_
        simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
        rcases le_abs'.mp hω with h | h
        · right
          linarith
        · left
          linarith
    _ ≤ P.real {ω | m + t * K ≤ F (WithLp.toLp 2 fun i => X i ω)} +
          P.real {ω | F (WithLp.toLp 2 fun i => X i ω) ≤ m - t * K} :=
        measureReal_union_le _ _
    _ ≤ 2 * exp (-(1 / 16) * t ^ 2) + 2 * exp (-(1 / 16) * t ^ 2) := add_le_add hup' hlow'
    _ = 4 * exp (-(1 / 16) * t ^ 2) := by ring

end MathlibExt.Probability.TalagrandConcentrationWanted
