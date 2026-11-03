/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.HasLaw

/-!
# Cochran's theorem: joint independence and the rank criterion

Let `Z` be a standard Gaussian vector in a finite-dimensional real inner product space `E`.

* If `K₁, …, K_m` are pairwise orthogonal subspaces, the orthogonal projections
  `P_{K₁} Z, …, P_{K_m} Z` are mutually independent, hence so are the quadratic forms
  `‖P_{Kᵢ} Z‖²`.
* **Rank criterion** (Cochran 1934): for square matrices `A₁, …, A_m` over a field with
  `A₁ + ⋯ + A_m = 1`, the ranks add up to the size `n` iff every `Aᵢ` is idempotent and
  `Aᵢ Aⱼ = 0` for `i ≠ j`.
* **Cochran's theorem**, independence part: if `Z = (Z₁, …, Zₙ)` has independent standard
  normal coordinates and `‖Z‖² = Zᵀ A₁ Z + ⋯ + Zᵀ A_m Z` with symmetric `Aᵢ` summing to the
  identity and `rank A₁ + ⋯ + rank A_m = n`, the quadratic forms `Zᵀ Aᵢ Z` are mutually
  independent.
* **One-way layout**: for i.i.d. `N(μ, v)` observations labelled by groups, the vector of group
  means is independent of the within-group residuals; hence the between-group and within-group
  sums of squares of the analysis of variance are independent.
* For an i.i.d. sample `X₁, …, Xₙ ~ N(μ, v)`, the sample mean `X̄ ~ N(μ, v / n)` is independent
  of the residual vector `(Xᵢ - X̄)ᵢ` and hence of `(n - 1) S² = ∑ (Xᵢ - X̄)²`.

Not covered here: the marginal laws `‖P_K Z‖² ~ χ²_{dim K}` and `Zᵀ A Z ~ χ²_{rank A}` (the
single-projection form of Cochran's theorem, a separate development), hence
`(n - 1) S² / v ~ χ²_{n-1}` and the `χ²` laws of the sums of squares; the Student `t` and
Snedecor `F` laws of the resulting ratios.

## Main results

* `iIndepFun_starProjection_stdGaussian`, `iIndepFun_norm_sq_starProjection_stdGaussian`.
* `Matrix.cochran_rank_criterion`.
* `iIndepFun_dotProduct_mulVec_pi_gaussianReal` (Cochran's theorem, independence part).
* `groupMean`, `indepFun_groupMean_residual`, `indepFun_sumSqBetween_sumSqWithin`.
* `hasLaw_sampleMean`, `indepFun_sampleMean_residual`, `indepFun_sampleMean_sumSqDev`.

## References

* W. G. Cochran, *The distribution of quadratic forms in a normal system, with applications to
  the analysis of covariance*, Proc. Cambridge Philos. Soc. 30 (1934), 178–191.
* C. R. Rao, *Linear Statistical Inference and its Applications*, 2nd ed., Wiley (1973), ch. 3b.
* G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury (2002), Theorem 5.3.1.
-/

@[expose] public section

open MeasureTheory Module Finset
open scoped RealInnerProductSpace

namespace Matrix

/-- **Rank criterion** (Cochran 1934): square matrices `A k` over a field that sum to
the identity have ranks adding up to the size iff they are idempotent and pairwise
annihilating. -/
theorem cochran_rank_criterion {R : Type*} [Field R] {n : Type*} [Fintype n] [DecidableEq n]
    {κ : Type*} [Fintype κ] (A : κ → Matrix n n R) (hsum : ∑ k, A k = 1) :
    ∑ k, (A k).rank = Fintype.card n ↔
      (∀ k, A k * A k = A k) ∧ Pairwise fun k l => A k * A l = 0 := by
  classical
  set W : κ → Submodule R (n → R) := fun k => LinearMap.range (A k).mulVecLin
  let Φ : ((k : κ) → W k) →ₗ[R] (n → R) := ∑ k, (W k).subtype ∘ₗ LinearMap.proj k
  have hΦ : ∀ y, Φ y = ∑ k, (y k : n → R) := fun y => by simp [Φ]
  have hsumv : ∀ x : n → R, ∑ k, A k *ᵥ x = x := fun x => by
    rw [← Matrix.sum_mulVec, hsum, Matrix.one_mulVec]
  have hmem : ∀ k (x : n → R), A k *ᵥ x ∈ W k := fun k x => ⟨x, rfl⟩
  have hsurj : Function.Surjective Φ := fun x =>
    ⟨fun k => ⟨A k *ᵥ x, hmem k x⟩, by rw [hΦ]; exact hsumv x⟩
  have hdim : finrank R ((k : κ) → W k) = ∑ k, (A k).rank := Module.finrank_pi_fintype R
  constructor
  · intro hr
    have hinj : Function.Injective Φ :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (by rw [hdim, hr, Module.finrank_pi])).2 hsurj
    have key : ∀ l (z : n → R) k, A k *ᵥ (A l *ᵥ z) = if k = l then A l *ᵥ z else 0 := by
      intro l z
      have h := @hinj (fun k => ⟨A k *ᵥ (A l *ᵥ z), hmem k _⟩)
        (Pi.single l ⟨A l *ᵥ z, hmem l z⟩) (by
          rw [hΦ, hΦ, hsumv]
          rw [Finset.sum_eq_single l (fun k _ hk => by simp [hk])
            (by simp)]
          simp)
      intro k
      have hk := congrArg (fun y => (y k : n → R)) h
      by_cases hkl : k = l
      · subst hkl; simpa using hk
      · simpa [hkl, Pi.single_apply] using hk
    refine ⟨fun k => ?_, fun k l hkl => ?_⟩
    · refine Matrix.ext_iff_mulVec.2 fun z => ?_
      rw [← Matrix.mulVec_mulVec, key k z k]
      simp
    · refine Matrix.ext_iff_mulVec.2 fun z => ?_
      rw [← Matrix.mulVec_mulVec, key l z k]
      simp [hkl]
  · rintro ⟨hidem, hzero⟩
    have hinj : Function.Injective Φ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro y hy
      rw [hΦ] at hy
      funext l
      obtain ⟨z, hz⟩ := (y l).2
      have hA : ∀ k, A l *ᵥ (y k : n → R) = if k = l then (y l : n → R) else 0 := by
        intro k
        obtain ⟨w, hw⟩ := (y k).2
        simp only [Matrix.mulVecLin_apply] at hw
        rw [← hw, Matrix.mulVec_mulVec]
        by_cases hkl : k = l
        · subst hkl
          rw [hidem, hw]
          simp
        · rw [hzero (Ne.symm hkl), Matrix.zero_mulVec]
          simp [hkl]
      have := congrArg (fun x => A l *ᵥ x) hy
      simp only [Matrix.mulVec_sum, hA, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
        Matrix.mulVec_zero] at this
      exact Subtype.ext this
    have hbij := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
    rw [← hdim, hbij.finrank_eq, Module.finrank_pi]

end Matrix

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Under the standard Gaussian law, orthogonal projections onto pairwise orthogonal subspaces are
mutually independent. -/
theorem iIndepFun_starProjection_stdGaussian {κ : Type*} [Finite κ] (K : κ → Submodule ℝ E)
    (hK : Pairwise fun k l => K k ⟂ K l) :
    iIndepFun (fun k x => (K k).starProjection x) (stdGaussian E) := by
  have := Fintype.ofFinite κ
  have hG : HasGaussianLaw (fun x k => (K k).starProjection x) (stdGaussian E) :=
    (IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map_fun
      (ContinuousLinearMap.pi fun k => (K k).starProjection :  E →L[ℝ] (κ → E))
  refine hG.iIndepFun_of_covariance_inner fun k l hkl x y => ?_
  have h1 : ∀ (j : κ) (z : E), (fun ω => ⟪z, (K j).starProjection ω⟫) =
      fun ω => ⟪(K j).starProjection z, ω⟫ := fun j z => by
    funext ω
    exact (Submodule.inner_starProjection_left_eq_right (K j) z ω).symm
  rw [h1 k x, h1 l y, ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian, innerSL_apply_apply]
  exact (hK hkl).inner_eq ((K k).starProjection_apply_mem x) ((K l).starProjection_apply_mem y)

/-- Under the standard Gaussian law, the squared lengths `‖P_{K k} Z‖²` of the projections onto
pairwise orthogonal subspaces are mutually independent. -/
theorem iIndepFun_norm_sq_starProjection_stdGaussian {κ : Type*} [Finite κ]
    (K : κ → Submodule ℝ E) (hK : Pairwise fun k l => K k ⟂ K l) :
    iIndepFun (fun k x => ‖(K k).starProjection x‖ ^ 2) (stdGaussian E) :=
  (iIndepFun_starProjection_stdGaussian K hK).comp (fun _ v => ‖v‖ ^ 2) fun _ => by fun_prop

/-- The mean of the observations `x i` with `grp i = g` (`0` for an empty group). -/
noncomputable def groupMean {ι G : Type*} [Fintype ι] [DecidableEq G] (grp : ι → G)
    (x : ι → ℝ) (g : G) : ℝ :=
  (∑ i with grp i = g, x i) / (#{i | grp i = g} : ℕ)

section OneWay

variable {ι : Type*} [Fintype ι]

private theorem hasGaussianLaw_eval_pi (μ : ℝ) (v : NNReal) (i : ι) :
    HasGaussianLaw (fun x : ι → ℝ => x i) (Measure.pi fun _ : ι => gaussianReal μ v) :=
  HasLaw.hasGaussianLaw (μ := gaussianReal μ v)
    ⟨(measurable_pi_apply i).aemeasurable,
      (measurePreserving_eval (fun _ : ι => gaussianReal μ v) i).map_eq⟩

private theorem hasGaussianLaw_id_pi (μ : ℝ) (v : NNReal) :
    HasGaussianLaw (fun x : ι → ℝ => fun i => x i) (Measure.pi fun _ : ι => gaussianReal μ v) :=
  iIndepFun.hasGaussianLaw (X := fun i (x : ι → ℝ) => x i)
    (fun i => hasGaussianLaw_eval_pi μ v i)
    (iIndepFun_pi (X := fun _ (y : ℝ) => y) fun _ => by fun_prop)

private theorem memLp_eval_pi (μ : ℝ) (v : NNReal) (i : ι) :
    MemLp (fun x : ι → ℝ => x i) 2 (Measure.pi fun _ : ι => gaussianReal μ v) :=
  (hasGaussianLaw_eval_pi μ v i).memLp_two

private theorem covariance_eval_pi [DecidableEq ι] (μ : ℝ) (v : NNReal) (i j : ι) :
    cov[fun x : ι → ℝ => x i, fun x => x j; Measure.pi fun _ : ι => gaussianReal μ v] =
      if i = j then (v : ℝ) else 0 := by
  split_ifs with hij
  · subst hij
    rw [covariance_self (measurable_pi_apply i).aemeasurable]
    have h := (measurePreserving_eval (fun _ : ι => gaussianReal μ v) i).map_eq
    rw [← variance_id_map (measurable_pi_apply i).aemeasurable, h, variance_id_gaussianReal]
  · exact ((iIndepFun_pi (X := fun _ (y : ℝ) => y) fun _ => by fun_prop).indepFun hij
      ).covariance_eq_zero (memLp_eval_pi μ v i) (memLp_eval_pi μ v j)

private theorem memLp_groupMean {G : Type*} [DecidableEq G] (grp : ι → G) (μ : ℝ) (v : NNReal)
    (g : G) :
    MemLp (fun x => groupMean grp x g) 2 (Measure.pi fun _ : ι => gaussianReal μ v) := by
  have := (memLp_finsetSum {i | grp i = g} fun i _ => memLp_eval_pi μ v i).const_mul
    ((#{i | grp i = g} : ℕ) : ℝ)⁻¹
  simpa [groupMean, div_eq_inv_mul] using this

private theorem covariance_groupMean_eval {G : Type*} [DecidableEq G]
    (grp : ι → G) (μ : ℝ) (v : NNReal) (g : G) (j : ι) :
    cov[fun x => groupMean grp x g, fun x => x j; Measure.pi fun _ : ι => gaussianReal μ v] =
      if grp j = g then (v : ℝ) / (#{i | grp i = g} : ℕ) else 0 := by
  classical
  simp only [groupMean]
  rw [covariance_fun_div_left, covariance_fun_sum_left' (fun i _ => memLp_eval_pi μ v i)
    (memLp_eval_pi μ v j)]
  simp only [covariance_eval_pi, Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ,
    true_and]
  split_ifs <;> simp

private theorem covariance_groupMean_groupMean {G : Type*} [DecidableEq G]
    (grp : ι → G) (μ : ℝ) (v : NNReal) (g h : G) (hh : ∃ i, grp i = h) :
    cov[fun x => groupMean grp x g, fun x => groupMean grp x h;
      Measure.pi fun _ : ι => gaussianReal μ v] =
      if g = h then (v : ℝ) / (#{i | grp i = h} : ℕ) else 0 := by
  classical
  have hpos : (#{i | grp i = h} : ℕ) ≠ 0 := by
    obtain ⟨i, hi⟩ := hh
    exact Finset.card_ne_zero.2 ⟨i, by simp [hi]⟩
  have hpos' : ((#{i | grp i = h} : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hpos
  conv_lhs => enter [2]; simp only [groupMean]
  rw [covariance_fun_div_right, covariance_fun_sum_right' (fun i _ => memLp_eval_pi μ v i)
    (memLp_groupMean grp μ v g)]
  have hterm : ∀ i ∈ ({i | grp i = h} : Finset ι),
      cov[fun x => groupMean grp x g, fun x => x i; Measure.pi fun _ : ι => gaussianReal μ v] =
        if g = h then (v : ℝ) / (#{i | grp i = g} : ℕ) else 0 := by
    intro i hi
    have hi' : grp i = h := by simpa using hi
    rw [covariance_groupMean_eval, hi']
    by_cases hgh : g = h
    · subst hgh; simp
    · simp [hgh, Ne.symm hgh]
  rw [Finset.sum_congr rfl hterm]
  split_ifs with hgh
  · subst hgh
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp
  · simp

/-- **Gaussian one-way layout**: for i.i.d. `N(μ, v)` observations `xᵢ` labelled by groups
`grp i`, the vector of group means is independent of the vector of within-group residuals
`xᵢ - x̄_{grp i}`. -/
theorem indepFun_groupMean_residual {G : Type*} [Finite G] [DecidableEq G] (grp : ι → G)
    (μ : ℝ) (v : NNReal) :
    IndepFun (fun x g => groupMean grp x g) (fun x i => x i - groupMean grp x (grp i))
      (Measure.pi fun _ : ι => gaussianReal μ v) := by
  classical
  have := Fintype.ofFinite G
  set P := Measure.pi fun _ : ι => gaussianReal μ v
  set M : G → (ι → ℝ) →L[ℝ] ℝ := fun g =>
    ((#{i | grp i = g} : ℕ) : ℝ)⁻¹ • ∑ i with grp i = g, ContinuousLinearMap.proj i
  have hM : ∀ g x, M g x = groupMean grp x g := fun g x => by
    simp [M, groupMean, div_eq_inv_mul]
  set L : (ι → ℝ) →L[ℝ] (G → ℝ) × (ι → ℝ) :=
    (ContinuousLinearMap.pi M).prod
      (ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj j - M (grp j))
  have hG : HasGaussianLaw
      (fun x : ι → ℝ => (fun g => groupMean grp x g, fun j => x j - groupMean grp x (grp j)))
      P := by
    have := (hasGaussianLaw_id_pi μ v).map_fun L
    convert this using 2 with x
    ext <;> simp [L, hM]
  refine hG.indepFun_of_covariance_eval (X := fun g x => groupMean grp x g)
    (Y := fun j x => x j - groupMean grp x (grp j)) fun g j => ?_
  rw [covariance_fun_sub_right (memLp_groupMean grp μ v g) (memLp_eval_pi μ v j)
    (memLp_groupMean grp μ v (grp j)), covariance_groupMean_eval]
  rw [covariance_groupMean_groupMean grp μ v g (grp j) ⟨j, rfl⟩]
  by_cases hgj : grp j = g
  · subst hgj
    simp
  · simp [hgj, Ne.symm hgj]

private theorem sum_groupMean {G : Type*} [Finite G] [DecidableEq G] (grp : ι → G)
    (x : ι → ℝ) : ∑ k, groupMean grp x (grp k) = ∑ k, x k := by
  have := Fintype.ofFinite G
  rw [← Finset.sum_fiberwise (g := grp) (f := fun k => groupMean grp x (grp k)),
    ← Finset.sum_fiberwise (g := grp) (f := x)]
  refine Finset.sum_congr rfl fun g _ => ?_
  have hc : ∀ k ∈ ({k | grp k = g} : Finset ι), groupMean grp x (grp k) = groupMean grp x g :=
    fun k hk => by rw [(Finset.mem_filter.1 hk).2]
  rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul, groupMean]
  by_cases h0 : (#{i | grp i = g} : ℕ) = 0
  · rw [Finset.card_eq_zero.1 h0]
    simp
  · field_simp

/-- **One-way analysis of variance**: for i.i.d. `N(μ, v)` observations labelled by groups, the
between-group sum of squares `∑ᵢ (x̄_{grp i} - x̄)²` is independent of the within-group sum of
squares `∑ᵢ (xᵢ - x̄_{grp i})²`. -/
theorem indepFun_sumSqBetween_sumSqWithin {G : Type*} [Finite G] [DecidableEq G]
    (grp : ι → G) (μ : ℝ) (v : NNReal) :
    IndepFun (fun x => ∑ i, (groupMean grp x (grp i) - (∑ j, x j) / Fintype.card ι) ^ 2)
      (fun x => ∑ i, (x i - groupMean grp x (grp i)) ^ 2)
      (Measure.pi fun _ : ι => gaussianReal μ v) := by
  have h := (indepFun_groupMean_residual grp μ v).comp
    (φ := fun m : G → ℝ => ∑ i, (m (grp i) - (∑ k, m (grp k)) / Fintype.card ι) ^ 2)
    (ψ := fun r : ι → ℝ => ∑ i, r i ^ 2) (by fun_prop) (by fun_prop)
  simpa [Function.comp_def, sum_groupMean] using h

/-- For an i.i.d. sample `X₁, …, Xₙ ~ N(μ, v)` with `n ≥ 1`, the sample mean has the law
`N(μ, v / n)`. -/
theorem hasLaw_sampleMean {n : ℕ} (hn : 0 < n) (μ : ℝ) (v : NNReal) :
    HasLaw (fun x : Fin n → ℝ => (∑ i, x i) / n) (gaussianReal μ (v / n))
      (Measure.pi fun _ : Fin n => gaussianReal μ v) := by
  set P := Measure.pi fun _ : Fin n => gaussianReal μ v
  have hgm : ∀ x : Fin n → ℝ, groupMean (fun _ : Fin n => ()) x () = (∑ i, x i) / n := by
    simp [groupMean]
  set m : (Fin n → ℝ) →L[ℝ] ℝ := (n : ℝ)⁻¹ • ∑ i, ContinuousLinearMap.proj i
  have hm : (fun x : Fin n → ℝ => m x) = fun x : Fin n → ℝ => (∑ i, x i) / n := by
    funext x
    simp [m, div_eq_inv_mul]
  have hG : HasGaussianLaw (fun x : Fin n → ℝ => (∑ i, x i) / n) P := by
    have := (hasGaussianLaw_id_pi (ι := Fin n) μ v).map_fun m
    rwa [hm] at this
  refine ⟨hG.aemeasurable, ?_⟩
  rw [hG.map_eq_gaussianReal]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hmean : P[fun x : Fin n → ℝ => (∑ i, x i) / n] = μ := by
    rw [integral_div, integral_finsetSum _ fun i _ => (memLp_eval_pi μ v i).integrable
      one_le_two]
    have hi : ∀ i : Fin n, ∫ x : Fin n → ℝ, x i ∂P = μ := fun i => by
      calc ∫ x : Fin n → ℝ, x i ∂P = ∫ y, id y ∂(P.map fun x => x i) :=
            (integral_map (μ := P) (measurable_pi_apply i).aemeasurable
              aestronglyMeasurable_id).symm
        _ = μ := by
          rw [(measurePreserving_eval (fun _ : Fin n => gaussianReal μ v) i).map_eq]
          exact integral_id_gaussianReal
    rw [Finset.sum_congr rfl fun i _ => hi i]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hvar : Var[fun x : Fin n → ℝ => (∑ i, x i) / n; P] = v / n := by
    rw [← covariance_self hG.aemeasurable]
    have h := covariance_groupMean_groupMean (fun _ : Fin n => ()) μ v () () ⟨⟨0, hn⟩, rfl⟩
    simp only [hgm] at h
    rw [h]
    simp
  rw [hmean, hvar]
  congr 1
  ext
  simp only [Real.coe_toNNReal', NNReal.coe_div, NNReal.coe_natCast]
  exact max_eq_left (by positivity)

end OneWay

open Matrix in
/-- **Cochran's theorem**, independence part: if `Z` has independent standard normal coordinates
and symmetric matrices `A k` sum to the identity with ranks adding up to the dimension, the
quadratic forms `Zᵀ (A k) Z` are mutually independent. -/
theorem iIndepFun_dotProduct_mulVec_pi_gaussianReal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : Type*} [Fintype κ] (A : κ → Matrix ι ι ℝ) (hA : ∀ k, (A k).IsHermitian)
    (hsum : ∑ k, A k = 1) (hrank : ∑ k, (A k).rank = Fintype.card ι) :
    iIndepFun (fun k (x : ι → ℝ) => x ⬝ᵥ A k *ᵥ x)
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  classical
  obtain ⟨hidem, hzero⟩ := (Matrix.cochran_rank_criterion A hsum).1 hrank
  have hT : ∀ k, (A k)ᵀ = A k := fun k => by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using (hA k).eq
  set P := Measure.pi fun _ : ι => gaussianReal 0 1
  set L : (ι → ℝ) →L[ℝ] (κ → ι → ℝ) :=
    ContinuousLinearMap.pi fun k => LinearMap.toContinuousLinearMap (A k).mulVecLin
  have hG : HasGaussianLaw (fun x : ι → ℝ => fun k a => (A k *ᵥ x) a) P := by
    have := (hasGaussianLaw_id_pi (ι := ι) 0 1).map_fun L
    convert this using 2 with x
    ext k a
    simp [L]
  have hcov : ∀ k l, k ≠ l → ∀ a b,
      cov[fun x : ι → ℝ => (A k *ᵥ x) a, fun x => (A l *ᵥ x) b; P] = 0 := by
    intro k l hkl a b
    simp only [Matrix.mulVec, dotProduct]
    rw [covariance_fun_sum_fun_sum (fun c => (memLp_eval_pi 0 1 c).const_mul _)
      (fun d => (memLp_eval_pi 0 1 d).const_mul _)]
    simp only [covariance_const_mul_left, covariance_const_mul_right, covariance_eval_pi]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, NNReal.coe_one,
      mul_one]
    have h : (A k * A l) a b = 0 := by rw [hzero hkl, Matrix.zero_apply]
    rw [Matrix.mul_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [show A l b c = A l c b from by rw [← Matrix.transpose_apply (A l), hT l]]
    ring
  have hind : iIndepFun (fun k (x : ι → ℝ) => A k *ᵥ x) P := by
    have := hG.iIndepFun_of_covariance_eval (X := fun k a (x : ι → ℝ) => (A k *ᵥ x) a) hcov
    exact this
  have hq : ∀ k (x : ι → ℝ), x ⬝ᵥ A k *ᵥ x = (A k *ᵥ x) ⬝ᵥ (A k *ᵥ x) := by
    intro k x
    calc x ⬝ᵥ A k *ᵥ x = x ⬝ᵥ (A k * A k) *ᵥ x := by rw [hidem k]
      _ = x ⬝ᵥ A k *ᵥ (A k *ᵥ x) := by rw [Matrix.mulVec_mulVec]
      _ = (x ᵥ* A k) ⬝ᵥ (A k *ᵥ x) := Matrix.dotProduct_mulVec _ _ _
      _ = (A k *ᵥ x) ⬝ᵥ (A k *ᵥ x) := by
          rw [← Matrix.mulVec_transpose, hT k]
  have := hind.comp (fun _ (y : ι → ℝ) => y ⬝ᵥ y) fun _ => by fun_prop
  convert this using 2 with k
  funext x
  exact hq k x


/-- For an i.i.d. sample `X₁, …, Xₙ ~ N(μ, v)`, the sample mean is independent of the residual
vector `(Xᵢ - X̄)ᵢ`. -/
theorem indepFun_sampleMean_residual {n : ℕ} (μ : ℝ) (v : NNReal) :
    IndepFun (fun x : Fin n → ℝ => (∑ i, x i) / n)
      (fun x : Fin n → ℝ => fun i => x i - (∑ j, x j) / n)
      (Measure.pi fun _ : Fin n => gaussianReal μ v) := by
  have h := indepFun_groupMean_residual (fun _ : Fin n => ()) μ v
  have hφ : Measurable fun f : Unit → ℝ => f () := measurable_pi_apply ()
  have hgm : ∀ x : Fin n → ℝ, groupMean (fun _ : Fin n => ()) x () = (∑ i, x i) / n := by
    simp [groupMean]
  have h' := h.comp hφ measurable_id
  simp only [hgm] at h'
  exact h'

/-- For an i.i.d. sample `X₁, …, Xₙ ~ N(μ, v)`, the sample mean `X̄` is independent of the sum of
squared deviations `∑ (Xᵢ - X̄)² = (n - 1) S²`. -/
theorem indepFun_sampleMean_sumSqDev {n : ℕ} (μ : ℝ) (v : NNReal) :
    IndepFun (fun x : Fin n → ℝ => (∑ i, x i) / n)
      (fun x : Fin n → ℝ => ∑ i, (x i - (∑ j, x j) / n) ^ 2)
      (Measure.pi fun _ : Fin n => gaussianReal μ v) :=
  (indepFun_sampleMean_residual μ v).comp (φ := id) (ψ := fun r => ∑ i, r i ^ 2)
    measurable_id (by fun_prop)

end ProbabilityTheory
