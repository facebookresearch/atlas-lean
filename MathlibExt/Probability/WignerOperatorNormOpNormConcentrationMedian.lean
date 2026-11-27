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
import MathlibExt.Probability.TalagrandConcentration
import Mathlib.Analysis.Convex.Function

/-!
# Concentration of the Euclidean operator norm around a median

The operator norm of a real matrix with independent, mean-zero entries bounded by one has
Gaussian concentration around each median, with constants independent of the dimension. As in
Tao's proof, the operator norm is convex and `1`-Lipschitz for the Frobenius norm, so Talagrand's
concentration inequality `talagrand_concentration_median` (Tao's Theorem 2.1.13) applies to the
`n²` entries.

## Implementation notes

`opNorm_concentration_median` keeps the full name it had in
`WantedExt/Probability/WignerOperatorNormWanted.lean`, so it lives in the namespace
`MathlibExt.Probability.WignerOperatorNormWanted`.

## References

* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS, 2012,
  Proposition 2.3.10 and Theorem 2.1.13.
* M. Talagrand, *Concentration of measure and isoperimetric inequalities in product spaces*,
  Publ. Math. IHÉS 81 (1995), 73–205, Theorem 4.1.1.
-/

@[expose] public section

namespace MathlibExt.Probability.WignerOperatorNormWanted

open MeasureTheory ProbabilityTheory Real

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
  obtain ⟨C, hC, c, hc, h⟩ :=
    MathlibExt.Probability.TalagrandConcentrationWanted.talagrand_concentration_median
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
