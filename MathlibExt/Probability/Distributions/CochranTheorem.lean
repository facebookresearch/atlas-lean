/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.ChiSquare
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import MathlibExt.Probability.Distributions.Gamma

/-!
# Cochran's theorem on Gaussian quadratic forms

For a standard Gaussian vector `Z` in a finite-dimensional real inner product space `E` and a
subspace `K` of dimension `r ≥ 1`, the squared length `‖P_K Z‖²` of the orthogonal projection of
`Z` onto `K` has the chi-square law with `r` degrees of freedom. In coordinates: if
`Z = (Z₁, …, Zₙ)` has independent standard normal entries and `A` is a symmetric idempotent
matrix of rank `r ≥ 1`, then `Zᵀ A Z ~ χ²_r`.

This is the single-projection form of Cochran's theorem. The decomposition statement (if
`‖Z‖² = Q₁ + ⋯ + Q_m` with quadratic forms of ranks `r₁ + ⋯ + r_m = n`, then the `Qᵢ` are
independent with `Qᵢ ~ χ²_{rᵢ}`) is not covered here.

The chi-square law with `0` degrees of freedom is `chiSquareMeasure 0 = gammaMeasure 0 (1/2)`,
which is the zero measure (Mathlib's `Γ(0) = 0` makes the density vanish), not the Dirac mass
at `0`; this is why every statement assumes a positive dimension or rank.

## Main results

* `gaussianReal_map_sq` (in `Distributions.ChiSquare`): `Z² ~ χ²₁` for `Z ~ N(0, 1)`.
* `pi_gaussianReal_map_sum_sq`: for independent standard normal coordinates, `∑_{i ∈ s} Zᵢ²`
  is chi-square with `|s|` degrees of freedom (`s ≠ ∅`).
* `stdGaussian_map_sum_sq_inner`: the same in the coordinates of any orthonormal basis.
* `stdGaussian_map_norm_sq_starProjection` (Cochran's theorem, projection form).
* `pi_gaussianReal_map_dotProduct_mulVec` (Cochran's theorem, matrix form).

The proof extends an orthonormal basis of `K` by one of `Kᗮ`, uses the basis independence of
the standard Gaussian law (`stdGaussian_eq_map_pi_orthonormalBasis`) to write `‖P_K Z‖²` as a sum
of `dim K` squared independent standard normal coordinates, and identifies that sum through its
MGF (`eq_gammaMeasure_of_mgf_eq`).

## References

* W. G. Cochran, *The distribution of quadratic forms in a normal system, with applications to
  the analysis of covariance*, Proc. Cambridge Philos. Soc. 30 (1934), 178–191.
* C. R. Rao, *Linear Statistical Inference and its Applications*, 2nd ed., Wiley (1973),
  ch. 3b.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Module
open scoped RealInnerProductSpace

/-- The chi-square MGF on all of `ℝ`: `(1 - 2t)^{-p/2}` below `1/2` and `0` (infinite exponential
moment) from `1/2` on, written as `((√(1 - 2t))⁻¹) ^ p`. -/
private theorem mgf_chiSquareMeasure_eq_pow {p : ℕ} (hp : 0 < p) (t : ℝ) :
    mgf id (chiSquareMeasure p) t = ((√(1 - 2 * t))⁻¹) ^ p := by
  rcases lt_or_ge t (1 / 2) with ht | ht
  · rw [mgf_chiSquareMeasure_of_lt hp ht]
    have h1 : (1 / 2 : ℝ) / (1 / 2 - t) = (1 - 2 * t)⁻¹ := by
      field_simp
    have h0 : (0 : ℝ) ≤ (1 - 2 * t)⁻¹ := inv_nonneg.2 (by linarith)
    have h2 : (p : ℝ) / 2 = 1 / 2 * p := by ring
    rw [h1, h2, Real.rpow_mul_natCast h0, ← Real.sqrt_eq_rpow, Real.sqrt_inv]
  · have hsq : √(1 - 2 * t) = 0 := Real.sqrt_eq_zero'.2 (by linarith)
    rw [hsq, inv_zero, zero_pow hp.ne']
    refine mgf_undef fun hi => ?_
    have hmem : t ∈ integrableExpSet id (chiSquareMeasure p) := hi
    rw [chiSquareMeasure,
      ProbabilityTheory.integrableExpSet_gammaMeasure
        (by positivity) (by norm_num)] at hmem
    exact absurd hmem (not_lt.2 ht)

/-- For independent standard normal coordinates, the sum of the squares of the coordinates in a
nonempty finite set `s` has the chi-square law with `|s|` degrees of freedom. -/
theorem pi_gaussianReal_map_sum_sq {ι : Type*} [Fintype ι] {s : Finset ι} (hs : s.Nonempty) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).map (fun x => ∑ i ∈ s, x i ^ 2) =
      chiSquareMeasure s.card := by
  have := isProbabilityMeasure_chiSquareMeasure hs.card_pos
  refine ProbabilityTheory.eq_gammaMeasure_of_mgf_eq
    (by have := hs.card_pos; positivity) (by norm_num) ?_
  funext t
  rw [← chiSquareMeasure, mgf_chiSquareMeasure_eq_pow hs.card_pos,
    mgf_map (Finset.measurable_sum _ fun i _ => by fun_prop).aemeasurable (by fun_prop)]
  have hind : iIndepFun (fun i (x : ι → ℝ) => x i ^ 2) (Measure.pi fun _ : ι => gaussianReal 0 1) :=
    iIndepFun_pi (X := fun _ (y : ℝ) => y ^ 2) fun _ => by fun_prop
  have hsum : (id ∘ fun x : ι → ℝ => ∑ i ∈ s, x i ^ 2) = ∑ i ∈ s, fun x : ι → ℝ => x i ^ 2 := by
    ext x
    simp
  rw [hsum, hind.mgf_sum (fun _ => by fun_prop)]
  have hone : ∀ i, mgf (fun x : ι → ℝ => x i ^ 2) (Measure.pi fun _ : ι => gaussianReal 0 1) t =
      (√(1 - 2 * t))⁻¹ := by
    intro i
    calc mgf (fun x : ι → ℝ => x i ^ 2) (Measure.pi fun _ : ι => gaussianReal 0 1) t
        = mgf (fun y : ℝ => y ^ 2)
            ((Measure.pi fun _ : ι => gaussianReal 0 1).map (Function.eval i)) t :=
          (mgf_map (X := fun y : ℝ => y ^ 2) (measurable_pi_apply i).aemeasurable
            (by fun_prop)).symm
      _ = (√(1 - 2 * t))⁻¹ := by
          rw [(measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).map_eq]
          exact mgf_sq_stdGaussian t
  simp [hone]

/-- Coordinates of the standard Gaussian law in an orthonormal basis `b`: the sum of the squared
coordinates `⟪b i, x⟫` over a nonempty set `s` of indices is chi-square with `|s|` degrees of
freedom. -/
theorem stdGaussian_map_sum_sq_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {s : Finset ι} (hs : s.Nonempty) :
    (stdGaussian E).map (fun x => ∑ i ∈ s, ⟪b i, x⟫ ^ 2) = chiSquareMeasure s.card := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis b, Measure.map_map (by fun_prop) (by fun_prop)]
  have : ((fun x => ∑ i ∈ s, ⟪b i, x⟫ ^ 2) ∘ fun x : ι → ℝ => ∑ i, x i • b i) =
      fun x => ∑ i ∈ s, x i ^ 2 := by
    funext x
    simp [b.orthonormal.inner_right_fintype]
  rw [this, pi_gaussianReal_map_sum_sq hs]

private theorem norm_sq_starProjection_eq_sum {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (K : Submodule ℝ E) [K.HasOrthogonalProjection] {ι : Type*}
    [Fintype ι] (bK : OrthonormalBasis ι ℝ K) (x : E) :
    ‖K.starProjection x‖ ^ 2 = ∑ i, ⟪(bK i : E), x⟫ ^ 2 := by
  calc ‖K.starProjection x‖ ^ 2 = ‖(⟨K.starProjection x, K.starProjection_apply_mem x⟩ : K)‖ ^ 2 :=
        rfl
    _ = ∑ i, ⟪bK i, (⟨K.starProjection x, K.starProjection_apply_mem x⟩ : K)⟫ ^ 2 :=
        (bK.sum_sq_inner_right _).symm
    _ = ∑ i, ⟪(bK i : E), x⟫ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Submodule.coe_inner, ← Submodule.inner_starProjection_left_eq_right,
          Submodule.starProjection_eq_self_iff.2 (bK i).2]

private theorem exists_orthonormalBasis_sum {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (K : Submodule ℝ E) :
    ∃ b : OrthonormalBasis (Fin (finrank ℝ K) ⊕ Fin (finrank ℝ Kᗮ)) ℝ E,
      ∀ i, b (Sum.inl i) = (stdOrthonormalBasis ℝ K i : E) := by
  classical
  set bK := stdOrthonormalBasis ℝ K
  set bL := stdOrthonormalBasis ℝ Kᗮ
  let v : Fin (finrank ℝ K) ⊕ Fin (finrank ℝ Kᗮ) → E :=
    Sum.elim (fun i => (bK i : E)) (fun j => (bL j : E))
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    rintro (i | i) (j | j)
    · simp only [v, Sum.elim_inl, ← Submodule.coe_inner, Sum.inl.injEq]
      exact (orthonormal_iff_ite.1 bK.orthonormal) i j
    · simpa [v] using Submodule.inner_right_of_mem_orthogonal (bK i).2 (bL j).2
    · simpa [v] using Submodule.inner_left_of_mem_orthogonal (bK j).2 (bL i).2
    · simp only [v, Sum.elim_inr, ← Submodule.coe_inner, Sum.inr.injEq]
      exact (orthonormal_iff_ite.1 bL.orthonormal) i j
  have hcard : Fintype.card (Fin (finrank ℝ K) ⊕ Fin (finrank ℝ Kᗮ)) = finrank ℝ E := by
    simp [Submodule.finrank_add_finrank_orthogonal]
  refine ⟨OrthonormalBasis.mk hv (hv.linearIndependent.span_eq_top_of_card_eq_finrank' hcard).ge,
    fun i => ?_⟩
  simp [v]

/-- **Cochran's theorem**, projection form: for the standard Gaussian law on a
finite-dimensional real inner product space `E` and a subspace `K` of positive dimension, the
squared norm of the orthogonal projection onto `K` is chi-square with `dim K` degrees of
freedom. -/
theorem stdGaussian_map_norm_sq_starProjection {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (K : Submodule ℝ E) (hK : 0 < finrank ℝ K) :
    (stdGaussian E).map (fun x => ‖K.starProjection x‖ ^ 2) = chiSquareMeasure (finrank ℝ K) := by
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_sum K
  set s := (Finset.univ : Finset (Fin (finrank ℝ K))).map
    (Function.Embedding.inl (β := Fin (finrank ℝ Kᗮ)))
  have hs : s.Nonempty := (Finset.univ_nonempty_iff.2 ⟨(⟨0, hK⟩ : Fin _)⟩).map
  have hfun : (fun x => ‖K.starProjection x‖ ^ 2) = fun x => ∑ i ∈ s, ⟪b i, x⟫ ^ 2 := by
    funext x
    rw [norm_sq_starProjection_eq_sum K (stdOrthonormalBasis ℝ K), Finset.sum_map]
    simp [hb]
  rw [hfun, stdGaussian_map_sum_sq_inner b hs]
  simp [s]

open Matrix in
/-- **Cochran's theorem**, matrix form: if `Z` has independent standard normal coordinates and
`A` is a symmetric idempotent matrix of positive rank, the quadratic form `Zᵀ A Z` is
chi-square with `rank A` degrees of freedom. -/
theorem pi_gaussianReal_map_dotProduct_mulVec {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (hAA : A * A = A) (hr : 0 < A.rank) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).map (fun x => x ⬝ᵥ A *ᵥ x) =
      chiSquareMeasure A.rank := by
  classical
  set T := Matrix.toEuclideanLin A
  have hT : T.IsSymmetricProjection := by
    refine ⟨?_, Matrix.isSymmetric_toEuclideanLin_iff.2 hA⟩
    change T * T = T
    rw [Module.End.mul_eq_comp, ← Matrix.toLpLin_mul_same, hAA]
  obtain ⟨hK, hTeq⟩ := LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.1 hT
  set K := LinearMap.range T
  have hrank : finrank ℝ K = A.rank :=
    (Matrix.rank_eq_finrank_range_toLin A (EuclideanSpace.basisFun ι ℝ).toBasis
      (EuclideanSpace.basisFun ι ℝ).toBasis).symm
  have hq : ∀ x : ι → ℝ, x ⬝ᵥ A *ᵥ x = ‖K.starProjection (WithLp.toLp 2 x)‖ ^ 2 := by
    intro x
    have hP : K.starProjection (WithLp.toLp 2 x) = WithLp.toLp 2 (A *ᵥ x) := by
      exact (LinearMap.congr_fun hTeq (WithLp.toLp 2 x)).symm
    rw [← real_inner_self_eq_norm_sq, Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.2 (K.starProjection_apply_mem _), hP]
    simp [PiLp.inner_apply, dotProduct, mul_comm]
  rw [funext hq]
  change Measure.map ((fun y => ‖K.starProjection y‖ ^ 2) ∘ WithLp.toLp 2) _ = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop), map_pi_eq_stdGaussian,
    stdGaussian_map_norm_sq_starProjection K (hrank ▸ hr), hrank]

end ProbabilityTheory
