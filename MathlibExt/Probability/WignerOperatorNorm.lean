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
public import MathlibExt.Probability.WignerMatrix
import Mathlib.Probability.Moments.SubGaussian
import MathlibExt.Analysis.CoveringNumbers

/-!
# Upper tail of the Wigner operator norm

The operator norm of a Wigner matrix with independent centered entries bounded by one
has an exponentially small upper tail above a constant multiple of the square root of
its dimension. The proof applies Hoeffding's lemma to bilinear forms on a finite net.
-/

public section

namespace MathlibExt.Probability.WignerOperatorNormWanted

open MeasureTheory ProbabilityTheory Real
open scoped NNReal InnerProductSpace
open MathlibExt.Analysis.WignerSemicircleWanted.Analysis.WignerSemicircleProblem (wignerMatrix)

private abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

-- A real matrix acts separately on the real and imaginary parts of a complex vector.
private lemma complex_norm_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (M.map Complex.ofReal)‖ ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖ := by
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) M
  let S := Matrix.toEuclideanCLM (𝕜 := ℂ) (M.map Complex.ofReal)
  let re (z : EuclideanSpace ℂ (Fin n)) : Vec n := WithLp.toLp 2 (fun i => (z i).re)
  let im (z : EuclideanSpace ℂ (Fin n)) : Vec n := WithLp.toLp 2 (fun i => (z i).im)
  have hparts (z : EuclideanSpace ℂ (Fin n)) : ‖z‖ ^ 2 = ‖re z‖ ^ 2 + ‖im z‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simp only [Complex.sq_norm, Complex.normSq_apply, ← sq, Finset.sum_add_distrib]
    rfl
  apply S.opNorm_le_bound (norm_nonneg T)
  intro z
  have hre : re (S z) = T (re z) := by
    ext i
    change (∑ j, (M i j : ℂ) * z j).re = ∑ j, M i j * (z j).re
    simp
  have him : im (S z) = T (im z) := by
    ext i
    change (∑ j, (M i j : ℂ) * z j).im = ∑ j, M i j * (z j).im
    simp
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [hparts (S z), hre, him, mul_pow, hparts z, mul_add]
  simpa only [mul_pow] using add_le_add
    (pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm (re z)) 2)
    (pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm (im z)) 2)

-- Approximating both unit vectors costs at most half of the operator norm.
private lemma exists_net_pair {n : ℕ} (N : Finset (Vec n)) (hN : ∀ x ∈ N, ‖x‖ ≤ 1)
    (hcover : ∀ x, ‖x‖ ≤ 1 → ∃ y ∈ N, dist x y ≤ 1 / 4)
    (T : Vec n →L[ℝ] Vec n) {t : ℝ} (ht : 0 ≤ t) (hT : t < ‖T‖) :
    ∃ p ∈ N ×ˢ N, t / 2 < ⟪p.1, T p.2⟫_ℝ := by
  by_contra! h
  have hbound : ‖T‖ ≤ t / 2 + ‖T‖ / 2 := by
    apply ContinuousLinearMap.opNorm_le_of_re_inner_le (by positivity)
    intro x y hx hy
    obtain ⟨a, ha, hxa⟩ := hcover x hx.le
    obtain ⟨b, hb, hyb⟩ := hcover y hy.le
    rw [dist_eq_norm] at hxa hyb
    have h₁ := real_inner_le_norm y (T (x - a))
    have h₂ := real_inner_le_norm (y - b) (T a)
    rw [hy, one_mul] at h₁
    have he₁ := h₁.trans ((T.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hxa (norm_nonneg T)))
    have he₂ := h₂.trans (mul_le_mul hyb ((T.le_opNorm a).trans
      (by simpa using mul_le_mul_of_nonneg_left (hN a ha) (norm_nonneg T)))
      (norm_nonneg _) (by norm_num))
    have hp := h (b, a) (Finset.mem_product.mpr ⟨hb, ha⟩)
    simp only [map_sub, inner_sub_right, inner_sub_left] at he₁ he₂
    change ⟪T x, y⟫_ℝ ≤ _
    rw [real_inner_comm]
    linarith
  linarith

-- For either triangle of the matrix, the sum of the squared coefficients is at most one.
private lemma triangle_mgf {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → ℕ → Ω → ℝ}
    (hind : iIndepFun (fun ij : {p : ℕ × ℕ // p.1 ≤ p.2} => X ij.val.1 ij.val.2) P)
    (hmgf : ∀ i j, i ≤ j → HasSubgaussianMGF (X i j) 1 P)
    {n : ℕ} (s : Finset (Fin n × Fin n)) (hs : ∀ p ∈ s, p.1 ≤ p.2)
    (x y : Vec n) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    HasSubgaussianMGF
      (fun ω => ∑ p ∈ s, (x p.1 * y p.2) * X p.1 p.2 ω) 1 P := by
  classical
  let idx (p : s) : {p : ℕ × ℕ // p.1 ≤ p.2} :=
    ⟨(p.val.1, p.val.2), hs p p.2⟩
  have hinj : Function.Injective idx := by
    intro p q h
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg (fun r => r.val.1) h
    · exact congrArg (fun r => r.val.2) h
  let w (p : Fin n × Fin n) := x p.1 * y p.2
  let c (p : s) : ℝ≥0 := ⟨w p ^ 2, sq_nonneg _⟩
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun (s := Finset.univ) (c := c)
    ((hind.precomp hinj).comp (fun p z => w p * z) (fun p => measurable_const.mul measurable_id))
    (fun p _ => by
      have hp := (hmgf _ _ (hs p p.2)).const_mul (w p)
      convert! hp using 1
      ext
      change w p ^ 2 = w p ^ 2 * (1 : ℝ)
      rw [mul_one])
  have hc : (∑ p : s, (c p : ℝ)) ≤ 1 := calc
    _ = ∑ p ∈ s, w p ^ 2 := Finset.sum_coe_sort s _
    _ ≤ ∑ p, w p ^ 2 := Finset.sum_le_univ_sum_of_nonneg fun p => sq_nonneg _
    _ = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Finset.sum_mul]
      simp only [Fintype.sum_prod_type, w, mul_pow, Finset.mul_sum]
    _ ≤ 1 := by
      simpa using mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hx 2)
        (pow_le_pow_left₀ (norm_nonneg _) hy 2) (sq_nonneg _) (by positivity)
  have hrewrite (ω : Ω) : (∑ p : s, w p * X p.val.1 p.val.2 ω) =
      ∑ p ∈ s, w p * X p.1 p.2 ω :=
    Finset.sum_coe_sort s (fun p => w p * X p.1 p.2 ω)
  simp only [Function.comp_apply, idx] at hsum
  simp_rw [hrewrite] at hsum
  refine ⟨hsum.integrable_exp_mul, fun t => (hsum.mgf_le t).trans ?_⟩
  apply Real.exp_le_exp.mpr
  push_cast
  gcongr

private lemma bilinear_mgf {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → ℕ → Ω → ℝ}
    (hind : iIndepFun (fun ij : {p : ℕ × ℕ // p.1 ≤ p.2} => X ij.val.1 ij.val.2) P)
    (hmgf : ∀ i j, i ≤ j → HasSubgaussianMGF (X i j) 1 P)
    {n : ℕ} (x y : Vec n) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    HasSubgaussianMGF (fun ω => ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ)
      ((wignerMatrix X n ω).map Complex.re) y⟫_ℝ) 4 P := by
  classical
  let U := Finset.univ.filter fun p : Fin n × Fin n => p.1 ≤ p.2
  let V := Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2
  have hu := triangle_mgf hind hmgf U (fun p hp => (Finset.mem_filter.mp hp).2) x y hx hy
  have hv := triangle_mgf hind hmgf V (fun p hp => (Finset.mem_filter.mp hp).2.le) y x hy hx
  -- The two sums share their off-diagonal entries. The general sub-Gaussian sum
  -- bound combines them with parameter (√1 + √1)².
  have h := hu.add hv
  norm_num at h
  apply h.congr
  apply ae_of_all
  intro ω
  dsimp only
  rw [Matrix.inner_toEuclideanCLM _ x y]
  simp only [U, V, Finset.sum_filter, Fintype.sum_prod_type, Matrix.mulVec, dotProduct,
    Matrix.map_apply, wignerMatrix, Complex.ofReal_re, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun i j : Fin n =>
    if i < j then y i * x j * X i j ω else 0), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i ≤ j
  · simp [hij, not_lt.mpr hij, mul_comm, mul_left_comm]
  · have hji := lt_of_not_ge hij
    have hval : (j : ℕ) ≤ i := hji.le
    simp [hij, hji, min_eq_right hval, max_eq_left hval, mul_comm, mul_left_comm]

/-- **Upper tail estimate for Wigner ensembles** (Tao, *Topics in Random Matrix Theory*,
Corollary 2.3.6, real case). There are absolute constants `C, c > 0` such that, if the
upper-triangular entries `X i j` (`i ≤ j`) of a real symmetric array are independent, have mean
zero and are bounded by `1`, then the `n × n` Wigner matrix `M` satisfies
`P(‖M‖ > A√n) ≤ C exp(-cAn)` for every `n` and every `A ≥ C`. -/
theorem wigner_opNorm_upper_tail :
    ∃ C > 0, ∃ c > 0, ∀ (Ω : Type*) (_ : MeasurableSpace Ω) (P : Measure Ω),
      IsProbabilityMeasure P → ∀ (X : ℕ → ℕ → Ω → ℝ),
      (∀ i j, Measurable (X i j)) →
      iIndepFun (fun ij : {p : ℕ × ℕ // p.1 ≤ p.2} => X ij.val.1 ij.val.2) P →
      (∀ i j, i ≤ j → ∫ ω, X i j ω ∂P = 0) → (∀ i j, i ≤ j → ∀ ω, |X i j ω| ≤ 1) →
      ∀ (n : ℕ) (A : ℝ), C ≤ A →
        P.real {ω | A * √n < ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
          (wignerMatrix X n ω)‖} ≤ C * exp (-c * A * n) := by
  classical
  refine ⟨128, by norm_num, 1, by norm_num, ?_⟩
  intro Ω _ P hP X hmeas hind hmean hbounded n A hA
  let : IsProbabilityMeasure P := hP
  have hmgf (i j : ℕ) (hij : i ≤ j) : HasSubgaussianMGF (X i j) 1 P := by
    have hb : ∀ᵐ ω ∂P, X i j ω ∈ Set.Icc (-1 : ℝ) 1 :=
      ae_of_all _ fun ω => abs_le.mp (hbounded i j hij ω)
    have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (hmeas i j).aemeasurable hb (hmean i j hij)
    norm_num at h
    exact h
  obtain ⟨N, hN, hcover, hcard⟩ := euclidean_ball_net (m := n) (R := 1) (ε := 1 / 4)
    (by norm_num) (by norm_num)
  norm_num at hcard
  let t := A * √n
  have ht : 0 ≤ t := mul_nonneg (by linarith) (sqrt_nonneg _)
  let T (ω : Ω) := Matrix.toEuclideanCLM (𝕜 := ℝ) ((wignerMatrix X n ω).map Complex.re)
  let event (p : Vec n × Vec n) := {ω | t / 2 ≤ ⟪p.1, T ω p.2⟫_ℝ}
  have hnet : {ω | t < ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (wignerMatrix X n ω)‖} ⊆
      ⋃ p ∈ N ×ˢ N, event p := by
    intro ω hω
    have hreal := complex_norm_le ((wignerMatrix X n ω).map Complex.re)
    obtain ⟨p, hp, hval⟩ := exists_net_pair N hN hcover (T ω) ht (lt_of_lt_of_le hω hreal)
    exact Set.mem_iUnion₂.mpr ⟨p, hp, hval.le⟩
  have htail (p) (hp : p ∈ N ×ˢ N) : P.real (event p) ≤ exp (-(t / 2) ^ 2 / 8) := by
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    have h := (bilinear_mgf hind hmgf p.1 p.2 (hN _ ha) (hN _ hb)).measure_ge_le
      (ε := t / 2) (by positivity)
    norm_num at h
    exact h
  calc
    _ ≤ P.real (⋃ p ∈ N ×ˢ N, event p) := measureReal_mono hnet (measure_ne_top P _)
    _ ≤ ∑ p ∈ N ×ˢ N, P.real (event p) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ N ×ˢ N, exp (-(t / 2) ^ 2 / 8) := Finset.sum_le_sum htail
    _ = (N.card : ℝ) ^ 2 * exp (-(t / 2) ^ 2 / 8) := by
      simp [sq, nsmul_eq_mul]
    _ ≤ (exp 8 ^ n) ^ 2 * exp (-(t / 2) ^ 2 / 8) := by
      gcongr
      exact hcard.trans (pow_le_pow_left₀ (by norm_num) (by linarith [add_one_le_exp (8 : ℝ)]) n)
    _ ≤ 128 * exp (-1 * A * n) := by
      rw [← exp_nat_mul, ← exp_nat_mul, ← exp_add]
      apply le_trans (b := exp (-1 * A * n)) _ (by linarith [exp_pos (-1 * A * n)])
      apply exp_le_exp.mpr
      have ht2 : t ^ 2 = A ^ 2 * n := by simp [t, mul_pow]
      have hcoeff : 16 - A ^ 2 / 32 ≤ -A := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hA) (show 0 ≤ A + 96 by linarith)]
      have h := mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      nlinarith

end MathlibExt.Probability.WignerOperatorNormWanted
