/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
import MathlibExt.Probability.ConvexDistanceInequality
import Mathlib.Analysis.Convex.Function

/-!
# Concentration of the Euclidean operator norm around a median

The operator norm of a real matrix with independent entries bounded by one has Gaussian
concentration around each median, with constants independent of the dimension.

## References

* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS, 2012,
  Corollary 2.3.6, Proposition 2.3.10, Theorem 2.3.24, and the discussion after Theorem 2.4.2.
* Z. D. Bai and Y. Q. Yin, *Necessary and sufficient conditions for almost sure convergence of
  the largest eigenvalue of a Wigner matrix*, Ann. Probab. 16 (1988), no. 4, 1729–1741.
* M. Talagrand, *Concentration of measure and isoperimetric inequalities in product spaces*,
  Publ. Math. IHÉS 81 (1995), 73–205, Theorem 4.1.1.
-/

@[expose] public section

namespace MathlibExt.Probability.WignerOperatorNormWanted

open MeasureTheory ProbabilityTheory Real

private theorem div_le_convexDistance {Ω : Type*} {n : ℕ} {X : Fin n → Ω → ℝ} {K : ℝ}
    (hK : 0 < K) (hXK : ∀ i ω, |X i ω| ≤ K) {F : EuclideanSpace ℝ (Fin n) → ℝ}
    (hFc : ConvexOn ℝ Set.univ F) (hFL : LipschitzWith 1 F) {a r : ℝ}
    (hA : {y : Fin n → Ω | F (WithLp.toLp 2 fun i => X i (y i)) ≤ a}.Nonempty)
    {x : Fin n → Ω} (hx : a + r ≤ F (WithLp.toLp 2 fun i => X i (x i))) :
    r / (2 * K) ≤ ConvexDistance.convexDistance
      {y : Fin n → Ω | F (WithLp.toLp 2 fun i => X i (y i)) ≤ a} x := by
  set A := {y : Fin n → Ω | F (WithLp.toLp 2 fun i => X i (y i)) ≤ a}
  set p : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun i => X i (x i)
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

private theorem convex_lipschitz_concentration_median :
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
  have hup' : P.real {ω | m + t * K ≤ F (WithLp.toLp 2 fun i => X i ω)} ≤
      2 * exp (-(1 / 16) * t ^ 2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm₁)
      (measureReal_nonneg (μ := P) (s := {ω | m + t * K ≤ F (WithLp.toLp 2 fun i => X i ω)}))]
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

private def entryMatrix (n : ℕ) (z : EuclideanSpace ℝ (Fin (n * n))) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => z (finProdFinEquiv (i, j))

private lemma entryMatrix_bound (n : ℕ) (z : EuclideanSpace ℝ (Fin (n * n))) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (entryMatrix n z)‖ ≤ ‖z‖ := by
  refine (Matrix.toEuclideanCLM (𝕜 := ℝ) (entryMatrix n z)).opNorm_le_bound
    (norm_nonneg z) ?_
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [EuclideanSpace.real_norm_sq_eq, mul_pow, EuclideanSpace.real_norm_sq_eq x]
  change (∑ i, (∑ j, z (finProdFinEquiv (i, j)) * x j) ^ 2) ≤
    ‖z‖ ^ 2 * ∑ j, x j ^ 2
  have hsum : (∑ i : Fin n, ∑ j : Fin n, z (finProdFinEquiv (i, j)) ^ 2) = ‖z‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa only [Fintype.sum_prod_type] using
      Equiv.sum_comp (finProdFinEquiv : Fin n × Fin n ≃ Fin (n * n)) (fun k => z k ^ 2)
  calc
    _ ≤ ∑ i : Fin n, (∑ j : Fin n, z (finProdFinEquiv (i, j)) ^ 2) * ∑ j, x j ^ 2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
    _ = _ := by rw [← Finset.sum_mul, hsum]

private lemma entryMatrix_lipschitz (n : ℕ) :
    LipschitzWith 1 (fun z : EuclideanSpace ℝ (Fin (n * n)) =>
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (entryMatrix n z)‖) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul, Real.dist_eq]
  calc
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (entryMatrix n x) -
      Matrix.toEuclideanCLM (𝕜 := ℝ) (entryMatrix n y)‖ := abs_norm_sub_norm_le _ _
    _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (entryMatrix n (x - y))‖ := by
      rw [← map_sub]
      rfl
    _ ≤ ‖x - y‖ := entryMatrix_bound n (x - y)
    _ = dist x y := (dist_eq_norm x y).symm

private lemma entryMatrix_convex (n : ℕ) :
    ConvexOn ℝ Set.univ (fun z : EuclideanSpace ℝ (Fin (n * n)) =>
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (entryMatrix n z)‖) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb _
  have heq : Matrix.toEuclideanCLM (𝕜 := ℝ) (entryMatrix n (a • x + b • y)) =
      a • Matrix.toEuclideanCLM (𝕜 := ℝ) (entryMatrix n x) +
      b • Matrix.toEuclideanCLM (𝕜 := ℝ) (entryMatrix n y) := by
    rw [← map_smul, ← map_smul, ← map_add]
    rfl
  change ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (entryMatrix n (a • x + b • y))‖ ≤
    a * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (entryMatrix n x)‖ +
      b * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (entryMatrix n y)‖
  rw [heq]
  simpa [norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb] using
    norm_add_le (a • Matrix.toEuclideanCLM (𝕜 := ℝ) (entryMatrix n x))
      (b • Matrix.toEuclideanCLM (𝕜 := ℝ) (entryMatrix n y))

/-- **Concentration of the operator norm** (Tao, *Topics in Random Matrix Theory*,
Proposition 2.3.10, real case). There are absolute constants `C, c > 0` such that, if the
entries of a random `n × n` real matrix `M` are independent, have mean zero and are bounded by
`1`, and `m` is a median of `‖M‖`, then `P(|‖M‖ - m| ≥ λ) ≤ C exp(-cλ²)` for every `λ > 0`.
The constants do not depend on `n`. -/
public theorem opNorm_concentration_median :
    ∃ C > 0, ∃ c > 0, ∀ (Ω : Type*) (_ : MeasurableSpace Ω) (P : Measure Ω),
      IsProbabilityMeasure P → ∀ (n : ℕ) (M : Ω → Matrix (Fin n) (Fin n) ℝ),
      (∀ i j, Measurable fun ω => M ω i j) →
      iIndepFun (fun ij : Fin n × Fin n => fun ω => M ω ij.1 ij.2) P →
      (∀ i j, ∫ ω, M ω i j ∂P = 0) → (∀ i j ω, |M ω i j| ≤ 1) →
      ∀ m : ℝ, 1 / 2 ≤ P.real {ω | ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (M ω)‖ ≤ m} →
        1 / 2 ≤ P.real {ω | m ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (M ω)‖} →
      ∀ t : ℝ, 0 < t →
        P.real {ω | t ≤ |‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (M ω)‖ - m|} ≤
          C * exp (-c * t ^ 2) := by
  obtain ⟨C, hC, c, hc, h⟩ := convex_lipschitz_concentration_median
  refine ⟨C, hC, c, hc, ?_⟩
  intro Ω _ P hP n M hmeas hind _hmean hbounded m hm₁ hm₂ t ht
  let X (k : Fin (n * n)) (ω : Ω) := M ω (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  have hXi : iIndepFun X P := hind.precomp finProdFinEquiv.symm.injective
  have hXm : ∀ k, Measurable (X k) := fun k => hmeas _ _
  have hXb : ∀ k ω, |X k ω| ≤ (1 : ℝ) := fun k ω => hbounded _ _ ω
  have heq (ω : Ω) : entryMatrix n (WithLp.toLp 2 fun k => X k ω) = M ω := by
    ext i j
    change M ω (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
      (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = M ω i j
    rw [Equiv.symm_apply_apply]
  simpa only [mul_one, heq] using h Ω inferInstance P hP (n * n) X 1 zero_lt_one hXm hXi hXb
    (fun z => ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (entryMatrix n z)‖)
    (entryMatrix_convex n) (entryMatrix_lipschitz n) m (by simpa only [heq] using hm₁)
    (by simpa only [heq] using hm₂) t ht

end MathlibExt.Probability.WignerOperatorNormWanted
