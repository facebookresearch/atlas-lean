/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Probability.ProductMeasure
import MathlibExt.Analysis.InnerProductSpace.EckartYoungFrobenius
import MathlibExt.Probability.Distributions.CochranTheorem
import MathlibExt.Probability.Distributions.GammaMoments

/-!
# Average Frobenius error of the randomized range finder

For a Gaussian test matrix `Ω`, `integral_residualFrobenius_le` bounds the expected
Frobenius error of projecting `A` onto the range of `A * Ω` by a multiple of its singular
value tail, as in Halko, Martinsson and Tropp, *Finding structure with randomness*, §10.2.

The proof measures the projection error on each right singular vector. For a leading vector,
the other leading Gaussian rows impose at most `k - 1` linear constraints on the `k + p`
sample coefficients. Cochran's theorem evaluates the reciprocal moment of the projected row
in the remaining subspace. Orthogonality then reduces the contribution of the independent
trailing rows to the sum of their singular values squared.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace MathlibExt.LinearAlgebra.Matrix.RandomizedRangeFinderWanted

variable {m n : ℕ}

/-- **Range-finder residual.** The residual `(I - P_Y) A` of the randomized range finder with
sample matrix `Y = AΩ`, as an operator from `ℝⁿ` to `ℝᵐ` (Halko, Martinsson and Tropp, SIAM Rev.
53 (2011), §1.5 and §9.1). -/
noncomputable def residual {ℓ : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (Ω : Matrix (Fin n) (Fin ℓ) ℝ) : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (ContinuousLinearMap.id ℝ _ -
      (LinearMap.range (Matrix.toEuclideanLin (A * Ω))).starProjection).comp
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A))

/-- **Frobenius error of the range finder.** The Frobenius norm
`‖(I - P_Y) A‖_F = (∑ⱼ ‖(I - P_Y) A eⱼ‖²)^{1/2}` of the range-finder residual (Halko, Martinsson
and Tropp, SIAM Rev. 53 (2011), §10.2). -/
noncomputable def residualFrobenius {ℓ : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (Ω : Matrix (Fin n) (Fin ℓ) ℝ) : ℝ :=
  Real.sqrt (∑ j, ‖residual A Ω (EuclideanSpace.single j 1)‖ ^ 2)

/-- **Standard Gaussian test matrix.** The law of an `n × ℓ` standard Gaussian matrix:
independent `N(0, 1)` entries, as a measure on the entry functions `Fin n × Fin ℓ → ℝ`
(Halko, Martinsson and Tropp, SIAM Rev. 53 (2011), §4.1 and §10). -/
noncomputable def gaussianMatrixLaw (n ℓ : ℕ) : Measure (Fin n × Fin ℓ → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

open Real
open scoped RealInnerProductSpace

-- The squared length of a projected Gaussian has a chi-square law. Its reciprocal
-- has finite mean when the projection has dimension greater than two.
private lemma integral_inv_proj {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (K : Submodule ℝ E) (hr : 2 < Module.finrank ℝ K) :
    ∫ x, (‖K.starProjection x‖ ^ 2)⁻¹ ∂stdGaussian E =
      ((Module.finrank ℝ K : ℝ) - 2)⁻¹ := by
  let r := Module.finrank ℝ K
  have hr' : 2 < (r : ℝ) := by exact_mod_cast hr
  have h := stdGaussian_map_norm_sq_starProjection K (by omega)
  rw [← integral_map (φ := fun x => ‖K.starProjection x‖ ^ 2) (f := fun t : ℝ => t⁻¹)
    (by fun_prop) (by fun_prop), h]
  have hm := integral_rpow_gammaMeasure (a := (r : ℝ) / 2) (r := 1 / 2) (p := -1)
    (by linarith) (by norm_num) (by linarith)
  simp only [Real.rpow_neg_one] at hm
  change (∫ x : ℝ, x⁻¹ ∂gammaMeasure ((r : ℝ) / 2) (1 / 2)) = _
  rw [hm]
  have hpos : 0 < (r : ℝ) / 2 + -1 := by linarith
  have hrec := Real.Gamma_add_one hpos.ne'
  rw [show ((r : ℝ) / 2 + -1) + 1 = r / 2 by ring] at hrec
  change _ = ((r : ℝ) - 2)⁻¹
  rw [hrec]
  rw [show ((r : ℝ) / 2 + -1) * Gamma (r / 2 + -1) * (1 / 2 : ℝ)⁻¹ =
    Gamma (r / 2 + -1) * ((r : ℝ) - 2) by ring, ← div_div, div_self (Gamma_pos_of_pos hpos).ne',
    one_div]

private abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

private abbrev rowsLaw (n l : ℕ) : Measure (Fin n → Vec l) :=
  Measure.pi fun _ => stdGaussian (Vec l)

-- In right singular coordinates, the image of a coefficient vector z under the sample
-- matrix is the linear combination below. Taking the distance as an infimum gives
-- measurability even when the sample matrix changes rank.
private def sampleDistance {m n l : ℕ} (u : Fin n → Vec m) (y : Vec m) (r : Fin n → Vec l) : ℝ :=
  ⨅ z : Vec l, ‖y - ∑ j, ⟪r j, z⟫ • u j‖

private lemma sampleDistance_le {m n l : ℕ} (u : Fin n → Vec m) (y : Vec m) (r : Fin n → Vec l)
    (z : Vec l) : sampleDistance u y r ≤ ‖y - ∑ j, ⟪r j, z⟫ • u j‖ :=
  ciInf_le ⟨0, by rintro _ ⟨w, rfl⟩; positivity⟩ z

private lemma sampleDistance_bounds {m n l : ℕ} (u : Fin n → Vec m) (y : Vec m)
    (r : Fin n → Vec l) :
    0 ≤ sampleDistance u y r ∧ sampleDistance u y r ≤ ‖y‖ :=
  ⟨le_ciInf fun _ => norm_nonneg _, by simpa using sampleDistance_le u y r 0⟩

private lemma measurable_sampleDistance {m n l : ℕ} (u : Fin n → Vec m) (y : Vec m) :
    Measurable (sampleDistance (l := l) u y) := by
  apply UpperSemicontinuous.measurable
  apply upperSemicontinuous_ciInf (fun _ => ⟨0, by rintro _ ⟨_, rfl⟩; positivity⟩)
  exact fun z => Continuous.upperSemicontinuous (by fun_prop)

private lemma integral_inner_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (z : E) :
    ∫ x, ⟪x, z⟫ ^ 2 ∂stdGaussian E = ‖z‖ ^ 2 := by
  have h := variance_dual_stdGaussian (innerSL ℝ z)
  rw [variance_of_integral_eq_zero (by fun_prop) (integral_strongDual_stdGaussian _)] at h
  simpa only [innerSL_apply_apply, innerSL_apply_norm, real_inner_comm (x := z)] using h

private lemma integral_rows_inner_sq {n l : ℕ} (z : Vec l) (i : Fin n) :
    ∫ r, ⟪r i, z⟫ ^ 2 ∂rowsLaw n l = ‖z‖ ^ 2 := by
  rw [← integral_map (φ := fun r : Fin n → Vec l => r i) (f := fun x : Vec l => ⟪x, z⟫ ^ 2)
    (measurable_pi_apply i).aemeasurable (by fun_prop),
    (measurePreserving_eval (fun _ : Fin n => stdGaussian (Vec l)) i).map_eq]
  exact integral_inner_sq z

private lemma integrable_rows_inner_sq {n l : ℕ} (z : Vec l) (i : Fin n) :
    Integrable (fun r => ⟪r i, z⟫ ^ 2) (rowsLaw n l) := by
  by_cases hz : z = 0
  · simp [hz]
  apply Integrable.of_integral_ne_zero
  rw [integral_rows_inner_sq]
  positivity

-- Select rows from two independent copies of the Gaussian matrix. This expresses
-- integration over disjoint groups of rows as an iterated integral.
private def selectRows {ι E : Type*} [DecidableEq ι] (s : Finset ι) (a b : ι → E) (j : ι) : E :=
  if j ∈ s then a j else b j

private lemma continuous_selectRows {ι E : Type*} [DecidableEq ι] [TopologicalSpace E]
    (s : Finset ι) :
    Continuous (fun ab : (ι → E) × (ι → E) => selectRows s ab.1 ab.2) :=
  continuous_pi fun j => by
    by_cases hj : j ∈ s
    · simp only [selectRows, ite_eq_left hj]
      fun_prop
    · simp only [selectRows, ite_eq_right hj]
      fun_prop

private lemma measurePreserving_selectRows {n l : ℕ} (s : Finset (Fin n)) :
    MeasurePreserving (fun ab => selectRows s ab.1 ab.2) ((rowsLaw n l).prod (rowsLaw n l))
      (rowsLaw n l) := by
  let μ := stdGaussian (Vec l)
  have h (j : Fin n) :
      MeasurePreserving (fun q : Vec l × Vec l => if j ∈ s then q.1 else q.2) (μ.prod μ) μ := by
    by_cases hj : j ∈ s
    · simpa [hj] using (measurePreserving_fst (μ := μ) (ν := μ))
    · simpa [hj] using (measurePreserving_snd (μ := μ) (ν := μ))
  exact (measurePreserving_pi _ _ h).comp
    (measurePreserving_arrowProdEquivProdArrow _ _ _ (fun _ => μ) (fun _ => μ)).symm

private lemma integral_selectRows {n l : ℕ} (s : Finset (Fin n)) {f : (Fin n → Vec l) → ℝ}
    (hf : Integrable f (rowsLaw n l)) :
    ∫ r, f r ∂rowsLaw n l =
      ∫ a, ∫ b, f (selectRows s a b) ∂rowsLaw n l ∂rowsLaw n l := by
  have hp := measurePreserving_selectRows (l := l) s
  conv_lhs => rw [← hp.map_eq]
  rw [integral_map hp.measurable.aemeasurable (hp.map_eq.symm ▸ hf.aestronglyMeasurable)]
  exact integral_prod _ (hp.integrable_comp_of_integrable hf)

private lemma integrable_sampleDistance_sq {n l m : ℕ} {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] (u : Fin n → Vec m) (y : Vec m)
    {r : α → Fin n → Vec l} (hr : Measurable r) :
    Integrable (fun a => sampleDistance u y (r a) ^ 2) μ := by
  apply (integrable_const (μ := μ) (‖y‖ ^ 2)).mono'
    (((measurable_sampleDistance u y).comp hr).pow_const 2).aestronglyMeasurable
  filter_upwards with a
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (sampleDistance_bounds _ _ _).1 (sampleDistance_bounds _ _ _).2 _

private lemma norm_sum_sq {n m : ℕ} (s : Finset (Fin n)) (w : Fin n → ℝ) (u : Fin n → Vec m)
    (hu : Pairwise fun i j => ⟪u i, u j⟫ = 0) :
    ‖∑ j ∈ s, w j • u j‖ ^ 2 = ∑ j ∈ s, w j ^ 2 * ‖u j‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]; ring
  · intro j hj hji
    simp [real_inner_smul_left, real_inner_smul_right, hu hji.symm]
  · simp [hi]

-- Fix a coefficient vector that reproduces the ith leading coordinate and kills the others.
-- Only the independent trailing rows contribute to its mean squared error.
private lemma integral_over_tail_rows_le {n l m : ℕ} (u : Fin n → Vec m)
    (hu : Pairwise fun i j => ⟪u i, u j⟫ = 0) (s : Finset (Fin n)) (i : Fin n) (hi : i ∈ s)
    (a b : Fin n → Vec l) (z : Vec l) (hi' : ⟪b i, z⟫ = 1)
    (ha : ∀ j ∈ s.erase i, ⟪a j, z⟫ = 0) :
    (∫ c, sampleDistance u (u i) (selectRows (s.erase i) a (selectRows {i} b c)) ^ 2 ∂rowsLaw n l) ≤
      ‖z‖ ^ 2 * ∑ j ∈ sᶜ, ‖u j‖ ^ 2 := by
  let rhs (c : Fin n → Vec l) := ∑ j ∈ sᶜ, ⟪c j, z⟫ ^ 2 * ‖u j‖ ^ 2
  have hint (j : Fin n) := (integrable_rows_inner_sq z j).mul_const (‖u j‖ ^ 2)
  have hbound (c : Fin n → Vec l) :
      sampleDistance u (u i) (selectRows (s.erase i) a (selectRows {i} b c)) ^ 2 ≤ rhs c := by
    let r := selectRows (s.erase i) a (selectRows {i} b c)
    have hlead : ∑ j ∈ s, ⟪r j, z⟫ • u j = u i := by
      rw [Finset.sum_eq_single i]
      · simp [r, selectRows, hi']
      · intro j hj hji
        have hj' := Finset.mem_erase.mpr ⟨hji, hj⟩
        simp [r, selectRows, hj', ha j hj']
      · simp [hi]
    have htail : ∑ j ∈ sᶜ, ⟪r j, z⟫ • u j = ∑ j ∈ sᶜ, ⟪c j, z⟫ • u j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_compl.mp hj
      have hji : j ≠ i := by rintro rfl; exact hj' hi
      simp [r, selectRows, hj', hji]
    calc
      _ ≤ ‖u i - ∑ j, ⟪r j, z⟫ • u j‖ ^ 2 :=
        pow_le_pow_left₀ (sampleDistance_bounds _ _ _).1 (sampleDistance_le _ _ _ _) _
      _ = rhs c := by
        rw [← s.sum_add_sum_compl, hlead, htail, sub_add_cancel_left, norm_neg,
          norm_sum_sq _ _ u hu]
  calc
    _ ≤ ∫ c, rhs c ∂rowsLaw n l := integral_mono_of_nonneg (.of_forall fun _ => sq_nonneg _)
      (integrable_finsetSum _ fun j _ => hint j) (.of_forall hbound)
    _ = _ := by
      simp only [rhs, integral_finsetSum _ (fun j _ => hint j), integral_mul_const,
        integral_rows_inner_sq, Finset.mul_sum]

-- Fix the other leading rows and the ith row in turn. After integrating the trailing rows,
-- average over the ith row using its projected chi-square law.
-- Project row i onto the orthogonal complement of the other leading rows and divide
-- by its squared length to obtain the required coefficient vector.
private lemma integral_lead_bound {n m k p : ℕ} (u : Fin n → Vec m)
    (hu : Pairwise fun i j => ⟪u i, u j⟫ = 0) (s : Finset (Fin n)) (hs : s.card = k)
    (hk : 0 < k) (hp : 2 ≤ p) (i : Fin n) (hi : i ∈ s) :
    (∫ r, sampleDistance u (u i) r ^ 2 ∂rowsLaw n (k + p)) ≤
      ((p : ℝ) - 1)⁻¹ * ∑ j ∈ sᶜ, ‖u j‖ ^ 2 := by
  let l := k + p
  let μ := rowsLaw n l
  let e (r : Fin n → Vec l) := sampleDistance u (u i) r ^ 2
  let T := ∑ j ∈ sᶜ, ‖u j‖ ^ 2
  have hT : 0 ≤ T := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpp : 0 < (p : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast (by omega : 1 < p))
  change (∫ r, e r ∂μ) ≤ ((p : ℝ) - 1)⁻¹ * T
  have he₀ : Integrable e μ := integrable_sampleDistance_sq u (u i) measurable_id
  rw [integral_selectRows (s.erase i) he₀]
  calc
    _ ≤ ∫ _ : Fin n → Vec l, ((p : ℝ) - 1)⁻¹ * T ∂μ := by
      apply integral_mono_of_nonneg (.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _)
        (integrable_const _) (.of_forall _)
      intro a
      have he : Integrable (fun r : Fin n → Vec l => e (selectRows (s.erase i) a r)) μ :=
        integrable_sampleDistance_sq u (u i)
          ((continuous_selectRows _).comp (continuous_const.prodMk continuous_id)).measurable
      change (∫ r, e (selectRows (s.erase i) a r) ∂μ) ≤ _
      rw [integral_selectRows {i} he]
      let S := Submodule.span ℝ (a '' (↑(s.erase i) : Set (Fin n)))
      let K := Sᗮ
      let d := Module.finrank ℝ K
      have hc : Module.finrank ℝ S ≤ (s.erase i).card :=
        (finrank_span_le_ncard _ ((s.erase i).finite_toSet.image a)).trans
          (by simpa only [Set.ncard_coe_finset] using
            (Set.ncard_image_le (f := a) (s.erase i).finite_toSet))
      have hd : p + 1 ≤ d := by
        have hdim := S.finrank_add_finrank_orthogonal
        rw [finrank_euclideanSpace_fin] at hdim
        rw [Finset.card_erase_of_mem hi, hs] at hc
        change p + 1 ≤ Module.finrank ℝ Sᗮ
        change Module.finrank ℝ S + Module.finrank ℝ Sᗮ = k + p at hdim
        omega
      have hdr : 2 < d := by omega
      have hdr' : 2 < (d : ℝ) := by exact_mod_cast hdr
      let v (b : Fin n → Vec l) := K.starProjection (b i)
      have hM := measurePreserving_eval (fun _ : Fin n => stdGaussian (Vec l)) i
      have hmom : (∫ b, (‖v b‖ ^ 2)⁻¹ ∂μ) = ((d : ℝ) - 2)⁻¹ :=
        (hM.hasLaw.integral_comp (f := fun x => (‖K.starProjection x‖ ^ 2)⁻¹) (by fun_prop)).trans
          (integral_inv_proj K hdr)
      have hvi : Integrable (fun b => (‖v b‖ ^ 2)⁻¹) μ :=
        Integrable.of_integral_ne_zero (hmom.trans_ne (inv_ne_zero (by linarith)))
      have hLaw : HasLaw (fun b => ‖v b‖ ^ 2) (chiSquareMeasure d) μ :=
        (show HasLaw (fun x => ‖K.starProjection x‖ ^ 2) (chiSquareMeasure d) (stdGaussian _) from
          ⟨by fun_prop, stdGaussian_map_norm_sq_starProjection _ (by omega)⟩).comp hM.hasLaw
      -- The exceptional zero projection has chi-square probability zero.
      have hne : ∀ᵐ b ∂μ, ‖v b‖ ^ 2 ≠ 0 :=
        (hLaw.ae_iff (p := fun x => x ≠ 0) (by fun_prop)).2 (Measure.ae_ne _ _)
      calc
        _ ≤ ∫ b, (‖v b‖ ^ 2)⁻¹ * T ∂μ := by
          apply integral_mono_of_nonneg (.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _)
            (hvi.mul_const _)
          filter_upwards [hne] with b hb
          let z := (‖v b‖ ^ 2)⁻¹ • v b
          have hiv : ⟪b i, v b⟫ = ‖v b‖ ^ 2 := by
            rw [real_inner_comm (v b)]
            exact K.re_inner_starProjection_eq_normSq (b i)
          have hiz : ⟪b i, z⟫ = 1 := by simp [z, real_inner_smul_right, hiv, hb]
          have haz (j : Fin n) (hj : j ∈ s.erase i) : ⟪a j, z⟫ = 0 := by
            apply Submodule.inner_right_of_mem_orthogonal (K := S)
            · exact Submodule.subset_span ⟨j, hj, rfl⟩
            · exact K.smul_mem _ (K.starProjection_apply_mem _)
          have hz : ‖z‖ ^ 2 = (‖v b‖ ^ 2)⁻¹ := by
            rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow]
            field_simp
          exact (integral_over_tail_rows_le u hu s i hi a b z hiz haz).trans_eq (by rw [hz])
        _ = ((d : ℝ) - 2)⁻¹ * T := by rw [integral_mul_const, hmom]
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ hT
          apply inv_anti₀ hpp
          have hdp : (p : ℝ) + 1 ≤ d := by exact_mod_cast hd
          linarith
    _ = _ := by simp [μ]

private abbrev entryLaw (n : ℕ) := Measure.pi fun _ : Fin n => gaussianReal 0 1

private def flattenRows (n l : ℕ) : (Fin n → Vec l) ≃ᵐ (Fin n × Fin l → ℝ) :=
  (MeasurableEquiv.piCongrRight fun _ => (MeasurableEquiv.toLp 2 (Fin l → ℝ)).symm).trans
    (MeasurableEquiv.curry _ _ _).symm

private lemma flattenRows_preserving (n l : ℕ) :
    MeasurePreserving (flattenRows n l) (rowsLaw n l) (gaussianMatrixLaw n l) := by
  have h : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin l → ℝ)) (entryLaw l)
      (stdGaussian (Vec l)) := ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  have hc : MeasurePreserving (MeasurableEquiv.curry (Fin n) (Fin l) ℝ).symm
      (Measure.pi fun _ : Fin n => entryLaw l) (gaussianMatrixLaw n l) := by
    refine ⟨(MeasurableEquiv.curry _ _ _).symm.measurable, ?_⟩
    simpa only [Measure.infinitePi_eq_pi, entryLaw, gaussianMatrixLaw] using
      Measure.infinitePi_map_curry_symm (fun (_ : Fin n) (_ : Fin l) => gaussianReal 0 1)
  exact hc.comp (measurePreserving_pi _ _ fun _ => h.symm)

private def transposeEntries (n l : ℕ) : (Fin n × Fin l → ℝ) ≃ᵐ (Fin l × Fin n → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ => ℝ) (Equiv.prodComm _ _)

private lemma transpose_preserving (n l : ℕ) :
    MeasurePreserving (transposeEntries n l) (gaussianMatrixLaw n l) (gaussianMatrixLaw l n) :=
  measurePreserving_piCongrLeft (fun _ : Fin l × Fin n => gaussianReal 0 1) (Equiv.prodComm _ _)

-- Assemble standard Gaussian columns in the chosen basis. This change of variables
-- preserves the product Gaussian law and identifies the sample distances with the residual.
private def synthesizeColumns {n l : ℕ} (b : OrthonormalBasis (Fin n) ℝ (Vec n)) :
    (Fin n → Vec l) ≃ᵐ (Fin n × Fin l → ℝ) :=
  let col : (Fin n → Vec l) ≃ᵐ (Fin l → Vec n) :=
    ((flattenRows n l).trans (transposeEntries n l)).trans (flattenRows l n).symm
  col.trans ((MeasurableEquiv.piCongrRight fun _ => b.repr.symm.toMeasurableEquiv).trans
    ((flattenRows l n).trans (transposeEntries l n)))

private lemma synthesizeColumns_preserving {n l : ℕ} (b : OrthonormalBasis (Fin n) ℝ (Vec n)) :
    MeasurePreserving (synthesizeColumns (l := l) b) (rowsLaw n l) (gaussianMatrixLaw n l) := by
  have hb : MeasurePreserving b.repr.symm.toMeasurableEquiv (stdGaussian (Vec n))
      (stdGaussian (Vec n)) := ⟨by fun_prop, stdGaussian_map _⟩
  exact (transpose_preserving l n).comp ((flattenRows_preserving l n).comp
    ((measurePreserving_pi _ _ fun _ => hb).comp ((flattenRows_preserving l n).symm.comp
      ((transpose_preserving n l).comp (flattenRows_preserving n l)))))

private lemma synthesizeColumns_apply {n l : ℕ} (b : OrthonormalBasis (Fin n) ℝ (Vec n))
    (r : Fin n → Vec l) (i : Fin n) (j : Fin l) :
    synthesizeColumns b r (i, j) = (∑ t, r t j • b t) i := by
  change (b.repr.symm (WithLp.toLp 2 (fun t => r t j))) i = _
  rw [← b.sum_repr_symm]

private lemma sample_apply {n l : ℕ} (b : OrthonormalBasis (Fin n) ℝ (Vec n))
    (r : Fin n → Vec l) (z : Vec l) :
    Matrix.toEuclideanLin (Matrix.of fun i j => synthesizeColumns b r (i, j)) z =
      ∑ t, ⟪r t, z⟫ • b t := by
  ext i
  simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, Matrix.of_apply,
    synthesizeColumns_apply, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply,
    smul_eq_mul, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma residual_on_basis {n m l : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : OrthonormalBasis (Fin n) ℝ (Vec n)) (r : Fin n → Vec l) (x : Vec n) :
    ‖residual A (Matrix.of fun i j => synthesizeColumns b r (i, j)) x‖ =
      sampleDistance (fun i => Matrix.toEuclideanLin A (b i)) (Matrix.toEuclideanLin A x) r := by
  let Ω := Matrix.of fun i j => synthesizeColumns b r (i, j)
  let T := Matrix.toEuclideanLin A
  let Y := Matrix.toEuclideanLin (A * Ω)
  change ‖T x - (LinearMap.range Y).starProjection (T x)‖ = _
  rw [Submodule.starProjection_minimal, ← Y.surjective_rangeRestrict.iInf_comp
    (fun y : LinearMap.range Y => ‖T x - y‖)]
  apply iInf_congr
  intro z
  change ‖T x - Matrix.toEuclideanLin (A * Ω) z‖ = _
  rw [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
  change ‖T x - T (Matrix.toEuclideanLin Ω z)‖ = _
  rw [sample_apply, map_sum]
  simp only [map_smul, T]

private lemma residualFrob_rotated {n m l : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : OrthonormalBasis (Fin n) ℝ (Vec n)) (r : Fin n → Vec l) :
    residualFrobenius A (Matrix.of fun i j => synthesizeColumns b r (i, j)) =
      √(∑ i, sampleDistance (fun j => Matrix.toEuclideanLin A (b j))
        (Matrix.toEuclideanLin A (b i)) r ^ 2) := by
  let R := (residual A (Matrix.of fun i j => synthesizeColumns b r (i, j))).toLinearMap
  have ht (v : OrthonormalBasis (Fin n) ℝ (Vec n)) :
      (R.adjoint ∘ₗ R).trace ℝ _ = ∑ j, ‖R (v j)‖ ^ 2 := by
    rw [LinearMap.trace_eq_sum_inner _ v]
    simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  unfold residualFrobenius
  congr 1
  calc
    _ = (R.adjoint ∘ₗ R).trace ℝ _ := by
      simpa [EuclideanSpace.basisFun_apply, R] using (ht (EuclideanSpace.basisFun (Fin n) ℝ)).symm
    _ = _ := (ht b).trans <| Finset.sum_congr rfl fun i _ =>
      congrArg (· ^ 2) (residual_on_basis A b r (b i))

private lemma basis_energy {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (i j : Fin n) :
    let b := Matrix.EckartYoungFrobenius.rightSingularBasis A
    let T := Matrix.toEuclideanLin A
    ⟪T (b i), T (b j)⟫ = T.singularValues i ^ 2 * (if i = j then 1 else 0) := by
  intro b T
  rw [← T.adjoint_inner_left]
  change ⟪(T.adjoint ∘ₗ T) (b i), b j⟫ = _
  simp only [b, Matrix.EckartYoungFrobenius.rightSingularBasis,
    LinearMap.IsSymmetric.apply_eigenvectorBasis, real_inner_smul_left,
    OrthonormalBasis.inner_eq_ite, T.sq_singularValues_fin finrank_euclideanSpace_fin,
    RCLike.ofReal_real_eq_id, id_eq]

private lemma mean_sqrt_sum_sq_le {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : ι → X → ℝ) (hf : ∀ i, Measurable (f i))
    (hint : ∀ i, Integrable (fun x => f i x ^ 2) μ) :
    (∫ x, √(∑ i, f i x ^ 2) ∂μ) ^ 2 ≤ ∑ i, ∫ x, f i x ^ 2 ∂μ := by
  let F (x : X) := √(∑ i, f i x ^ 2)
  have hFsq : (fun x => F x ^ 2) = fun x => ∑ i, f i x ^ 2 :=
    funext fun x => Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hFm : Measurable F := (Finset.measurable_sum _ fun i _ => (hf i).pow_const 2).sqrt
  have hmem : MemLp F 2 μ := by
    apply (memLp_two_iff_integrable_sq hFm.aestronglyMeasurable).2
    rw [hFsq]
    exact integrable_finsetSum _ fun i _ => hint i
  have hvar := variance_nonneg F μ
  rw [variance_eq_sub hmem] at hvar
  change 0 ≤ (∫ x, F x ^ 2 ∂μ) - (∫ x, F x ∂μ) ^ 2 at hvar
  rw [hFsq, integral_finsetSum _ fun i _ => hint i] at hvar
  exact sub_nonneg.mp hvar

private lemma mean_error {n m k p : ℕ} (u : Fin n → Vec m)
    (hu : Pairwise fun i j => ⟪u i, u j⟫ = 0) (s : Finset (Fin n)) (hs : s.card = k)
    (hk : 0 < k) (hp : 2 ≤ p) :
    (∫ r, √(∑ i, sampleDistance u (u i) r ^ 2) ∂rowsLaw n (k + p)) ≤
      √(1 + k / (p - 1 : ℝ)) * √(∑ i ∈ sᶜ, ‖u i‖ ^ 2) := by
  let μ := rowsLaw n (k + p)
  let F (r : Fin n → Vec (k + p)) := √(∑ i, sampleDistance u (u i) r ^ 2)
  let T := ∑ i ∈ sᶜ, ‖u i‖ ^ 2
  have he (i : Fin n) : Integrable (fun r => sampleDistance u (u i) r ^ 2) μ :=
    integrable_sampleDistance_sq u (u i) measurable_id
  have htail (i : Fin n) : (∫ r, sampleDistance u (u i) r ^ 2 ∂μ) ≤ ‖u i‖ ^ 2 := by
    calc
      _ ≤ ∫ _ : Fin n → Vec (k + p), ‖u i‖ ^ 2 ∂μ := integral_mono (he i) (integrable_const _)
        fun r => let h := sampleDistance_bounds u (u i) r
          pow_le_pow_left₀ h.1 h.2 _
      _ = _ := by simp [μ]
  change (∫ r, F r ∂μ) ≤ √(1 + k / (p - 1 : ℝ)) * √T
  have hden : 0 ≤ (p - 1 : ℝ) := sub_nonneg.mpr (by exact_mod_cast (by omega : 1 ≤ p))
  rw [← Real.sqrt_mul (show 0 ≤ 1 + (k : ℝ) / (p - 1) by positivity)]
  apply Real.le_sqrt_of_sq_le
  calc
    _ ≤ ∑ i, ∫ r, sampleDistance u (u i) r ^ 2 ∂μ :=
      mean_sqrt_sum_sq_le μ (fun i => sampleDistance u (u i))
        (fun i => measurable_sampleDistance u (u i)) he
    _ ≤ (∑ _i ∈ s, ((p : ℝ) - 1)⁻¹ * T) + (∑ i ∈ sᶜ, ‖u i‖ ^ 2) := by
      rw [← s.sum_add_sum_compl (fun i => ∫ r, sampleDistance u (u i) r ^ 2 ∂μ)]
      exact add_le_add (Finset.sum_le_sum fun i hi => integral_lead_bound u hu s hs hk hp i hi)
        (Finset.sum_le_sum fun i _ => htail i)
    _ = (1 + k / (p - 1 : ℝ)) * T := by
      change (∑ _i ∈ s, ((p : ℝ) - 1)⁻¹ * T) + T = _
      simp only [Finset.sum_const, nsmul_eq_mul, hs]
      ring

/-- **Average Frobenius error of the randomized range finder** (N. Halko, P.-G. Martinsson and
J. A. Tropp, *Finding structure with randomness*, SIAM Rev. 53 (2011), arXiv:0909.4061,
Theorem 10.5). Let `A` be a real `m × n` matrix with singular values `σ₁ ≥ σ₂ ≥ …`, choose a
target rank `k ≥ 2` and an oversampling parameter `p ≥ 2` with `k + p ≤ min(m, n)`, and let `Ω`
be an `n × (k + p)` standard Gaussian matrix. Then
`E ‖(I - P_{AΩ}) A‖_F ≤ (1 + k / (p - 1))^{1/2} (∑_{j>k} σⱼ²)^{1/2}`; with `σ` 0-indexed as
`LinearMap.singularValues`, the sum runs over indices `k ≤ j < n`. -/
theorem integral_residualFrobenius_le {k p : ℕ} (hk : 2 ≤ k) (hp : 2 ≤ p)
    (hkp : k + p ≤ min m n) (A : Matrix (Fin m) (Fin n) ℝ) :
    ∫ ω, residualFrobenius A (Matrix.of fun i j => ω (i, j)) ∂(gaussianMatrixLaw n (k + p)) ≤
      Real.sqrt (1 + k / (p - 1 : ℝ)) *
        Real.sqrt (∑ j ∈ Finset.Ico k n, (Matrix.toEuclideanLin A).singularValues j ^ 2) := by
  let b := Matrix.EckartYoungFrobenius.rightSingularBasis A
  let u (i : Fin n) := Matrix.toEuclideanLin A (b i)
  let s := Finset.univ.filter fun i : Fin n => i.val < k
  have hkn : k ≤ n := by omega
  have hs : s.card = k := Fin.card_filter_val_lt.trans (min_eq_right hkn)
  have hu : Pairwise fun i j => ⟪u i, u j⟫ = 0 := fun i j hij => by
    simpa only [ite_eq_right hij, mul_zero] using basis_energy A i j
  have hnorm (i : Fin n) : ‖u i‖ ^ 2 = (Matrix.toEuclideanLin A).singularValues i ^ 2 := by
    simpa [real_inner_self_eq_norm_sq, u, b] using basis_energy A i i
  have htail : ∑ i ∈ sᶜ, ‖u i‖ ^ 2 =
      ∑ j ∈ Finset.Ico k n, (Matrix.toEuclideanLin A).singularValues j ^ 2 := by
    apply Finset.sum_bij (fun i _ => i.val)
    · intro i hi
      exact Finset.mem_Ico.mpr ⟨by simpa [s] using hi, i.isLt⟩
    · intro i _ j _ hij
      exact Fin.ext hij
    · intro j hj
      refine ⟨⟨j, (Finset.mem_Ico.mp hj).2⟩, ?_, rfl⟩
      simpa [s] using (Finset.mem_Ico.mp hj).1
    · exact fun i _ => hnorm i
  rw [← (synthesizeColumns_preserving (l := k + p) b).integral_comp'
    (fun ω => residualFrobenius A (Matrix.of fun i j => ω (i, j))), ← htail]
  simp only [residualFrob_rotated]
  exact mean_error u hu s hs (by omega) hp

end MathlibExt.LinearAlgebra.Matrix.RandomizedRangeFinderWanted
