/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Networks.RandomGraph
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Order.Notation

/-!
# Random graph tests: 12 N05.1 + 13 N05.3 = 25

N05.1 covers the exponential-family law on `Fin 2` with an edge
statistic (normalizer, probabilities, `PMF`, log-likelihood, moment
equation, derivatives, affine invariance, duplicate non-injectivity).
N05.3 covers a concrete two-block model with label swap (admissible
membership, 17/90 and 73/90 values computed independently on two
vertices, normalization, collision on three vertices in valid space).
-/

open scoped Matrix

namespace MathlibExtTest.Probability.Networks

@[expose] public section

open MathlibExt.Probability.Networks

open Classical in
/-- Edge statistic for `Fin 2`: 1 on `⊤`, 0 otherwise. -/
noncomputable def edgeStat : SimpleGraph (Fin 2) → Fin 1 → ℝ :=
  fun G _ => if G = ⊤ then 1 else 0

open Classical in
/-- Duplicated statistic: both coordinates equal the edge indicator. -/
noncomputable def dupStat : SimpleGraph (Fin 2) → Fin 2 → ℝ :=
  fun G _ => if G = (⊤ : SimpleGraph (Fin 2)) then 1 else 0

/-- Duplicate direction `(1, -1)` annihilating `dupStat`. -/
noncomputable def dupV : Fin 2 → ℝ :=
  fun i => if i = 0 then 1 else -1

/-- Normalizer positivity for the edge statistic. -/
theorem normalizer_edgeStat :
    0 < ergmNormalizer edgeStat 0 :=
  ergmNormalizer_pos _ _

/-- Probability positivity at the top graph. -/
theorem prob_edgeStat_top :
    0 < ergmProb edgeStat 0 ⊤ :=
  ergmProb_pos _ _ _

/-- Probabilities sum to one for the edge statistic. -/
theorem sum_prob_edgeStat :
    ∑ G, ergmProb edgeStat 0 G = 1 :=
  sum_ergmProb _ _

/-- PMF evaluation and real value for the edge statistic. -/
theorem pmf_edgeStat :
    ergmPMF edgeStat 0 ⊤ =
      ENNReal.ofReal (ergmProb edgeStat 0 ⊤) ∧
      (ergmPMF edgeStat 0 ⊤).toReal = ergmProb edgeStat 0 ⊤ :=
  ⟨ergmPMF_apply _ _ _, toReal_ergmPMF_apply _ _ _⟩

/-- Log-likelihood equals log probability for the edge statistic. -/
theorem loglik_eq_edgeStat :
    ergmLogLik edgeStat 0 ⊤ =
      Real.log (ergmProb edgeStat 0 ⊤) :=
  ergmLogLik_eq_log_ergmProb _ _ _

/-- Moment equation for the edge statistic. -/
theorem score_zero_iff_edgeStat :
    ergmScore edgeStat 0 ⊤ = 0 ↔
      edgeStat ⊤ = ergmMean edgeStat 0 :=
  ergmScore_eq_zero_iff _ _ _

/-- The mean is the gradient of the log-normalizer, directional form, edge case. -/
theorem deriv_log_normalizer_edgeStat :
    HasDerivAt
      (fun s : ℝ => Real.log (ergmNormalizer edgeStat (0 + s • fun _ => (1:ℝ))))
      ((fun _ => (1:ℝ)) ⬝ᵥ ergmMean edgeStat 0) 0 :=
  hasDerivAt_log_ergmNormalizer _ _ _

/-- The mean is the gradient of the log-normalizer, coordinate form, edge case. -/
theorem deriv_log_normalizer_update_edgeStat :
    HasDerivAt
      (fun s : ℝ => Real.log (ergmNormalizer edgeStat (Function.update 0 0 s)))
      (ergmMean edgeStat 0 0) ((0 : Fin 1 → ℝ) 0) :=
  hasDerivAt_log_ergmNormalizer_update _ _ _

/-- Directional derivative is the score, edge case. -/
theorem deriv_loglik_edgeStat :
    HasDerivAt
      (fun s : ℝ => ergmLogLik edgeStat (0 + s • fun _ => (1:ℝ)) ⊤)
      ((fun _ => (1:ℝ)) ⬝ᵥ ergmScore edgeStat 0 ⊤) 0 :=
  hasDerivAt_ergmLogLik _ _ _ _

/-- Coordinate derivative is the score coordinate, edge case. -/
theorem deriv_loglik_update_edgeStat :
    HasDerivAt
      (fun s : ℝ => ergmLogLik edgeStat (Function.update 0 0 s) ⊤)
      (ergmScore edgeStat 0 ⊤ 0) ((0 : Fin 1 → ℝ) 0) :=
  hasDerivAt_ergmLogLik_update _ _ _ _

/-- Mean derivative is covariance, edge case. -/
theorem deriv_mean_edgeStat :
    HasDerivAt
      (fun s : ℝ => ergmMean edgeStat (0 + s • fun _ => (1:ℝ)) 0)
      (∑ k, ergmCov edgeStat 0 0 k * (fun _ => (1:ℝ)) k) 0 :=
  hasDerivAt_ergmMean _ _ _ _

/-- Score derivative is negative covariance, edge case. -/
theorem deriv_score_edgeStat :
    HasDerivAt
      (fun s : ℝ => ergmScore edgeStat (0 + s • fun _ => (1:ℝ)) ⊤ 0)
      (-(∑ k, ergmCov edgeStat 0 0 k * (fun _ => (1:ℝ)) k)) 0 :=
  hasDerivAt_ergmScore _ _ _ _ _

/-- Adding the zero direction leaves the law unchanged. -/
theorem affine_invariant_edgeStat :
    ergmProb edgeStat (0 + 0) = ergmProb edgeStat 0 :=
  ergmProb_add_of_affine _ _ (fun _ => zero_dotProduct _)

/-- Duplicated statistics are not identifiable. -/
theorem dupNotInjective :
    ¬ Function.Injective (ergmProb dupStat) := by
  rw [ergmProb_injective_iff]
  intro h
  have h1 : ∀ G, dupV ⬝ᵥ dupStat G = 0 := by
    intro G
    simp only [dotProduct, Fin.sum_univ_two, dupV, dupStat]
    by_cases hG : G = (⊤ : SimpleGraph (Fin 2))
    · simp [hG]
    · simp [hG]
  have h2 : dupV = 0 := h dupV 0 h1
  have h0 := congrFun h2 0
  simp [dupV] at h0

/-- Concrete mixing proportions `1/3`, `2/3`. -/
noncomputable def sbmP : Fin 2 → ℝ := ![1/3, 2/3]

/-- Concrete affinities, symmetric in `[0,1]`. -/
noncomputable def sbmW : Fin 2 → Fin 2 → ℝ :=
  ![![1/2, 1/10], ![1/10, 1/5]]

/-- Label swap on two blocks. -/
noncomputable def sbmSwap : Equiv.Perm (Fin 2) := Equiv.swap 0 1

/-- Swapped mixing proportions. -/
noncomputable def sbmP_swap : Fin 2 → ℝ := sbmP ∘ sbmSwap

/-- Swapped affinities. -/
noncomputable def sbmW_swap : Fin 2 → Fin 2 → ℝ :=
  fun i j => sbmW (sbmSwap i) (sbmSwap j)

/-- Concrete parameters inhabit the admissible space. -/
theorem sbm_admissible_orig : SBMAdmissible sbmP sbmW := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    fin_cases k <;> simp [sbmP]
  · simp [sbmP, Fin.sum_univ_two]
    norm_num
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [sbmW] <;> norm_num
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [sbmW]

/-- Swapped parameters inhabit the admissible space. -/
theorem sbm_admissible_swapped :
    SBMAdmissible sbmP_swap sbmW_swap :=
  SBMAdmissible_relabel sbmSwap sbm_admissible_orig

/-- Swapped parameters differ from the originals. -/
theorem swapped_ne :
    (sbmP_swap, sbmW_swap) ≠ (sbmP, sbmW) := by
  intro h
  have h1 : sbmP_swap = sbmP := congrArg Prod.fst h
  have h2 := congrFun h1 0
  simp [sbmP_swap, sbmP, sbmSwap, Function.comp_apply] at h2
  norm_num at h2

/-- Edge weight on two vertices is `17/90` (original side). -/
theorem weight_edge_orig :
    sbmGraphWeight sbmP sbmW (⊤ : SimpleGraph (Fin 2)) = 17/90 := by
  classical
  simp only [sbmGraphWeight, sbmLabelWeight, sbmEdgeWeight]
  simp [Fin.prod_univ_two, SimpleGraph.top_adj]
  have hvez : (∑ z : Fin 2 → Fin 2, sbmP (z 0) * sbmP (z 1) * sbmW (z 0) (z 1)) =
      ∑ p : Fin 2 × Fin 2, sbmP p.1 * sbmP p.2 * sbmW p.1 p.2 :=
    Equiv.sum_comp (finTwoArrowEquiv (Fin 2))
      (fun p : Fin 2 × Fin 2 => sbmP p.1 * sbmP p.2 * sbmW p.1 p.2)
  rw [hvez, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two, sbmP, sbmW]
  norm_num

/-- Edge weight on two vertices is `17/90` (swapped side, independent). -/
theorem weight_edge_swapped :
    sbmGraphWeight sbmP_swap sbmW_swap
      (⊤ : SimpleGraph (Fin 2)) = 17/90 := by
  classical
  simp only [sbmGraphWeight, sbmLabelWeight, sbmEdgeWeight]
  simp [Fin.prod_univ_two, SimpleGraph.top_adj]
  have hvez : (∑ z : Fin 2 → Fin 2, sbmP_swap (z 0) *
      sbmP_swap (z 1) * sbmW_swap (z 0) (z 1)) =
      ∑ p : Fin 2 × Fin 2, sbmP_swap p.1 * sbmP_swap p.2 * sbmW_swap p.1 p.2 :=
    Equiv.sum_comp (finTwoArrowEquiv (Fin 2))
      (fun p : Fin 2 × Fin 2 => sbmP_swap p.1 * sbmP_swap p.2 * sbmW_swap p.1 p.2)
  rw [hvez, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two, sbmP_swap, sbmW_swap, sbmP, sbmW,
    sbmSwap, Function.comp_apply]
  norm_num

/-- Empty weight on two vertices is `73/90` (original side). -/
theorem weight_empty_orig :
    sbmGraphWeight sbmP sbmW (⊥ : SimpleGraph (Fin 2)) = 73/90 := by
  classical
  simp only [sbmGraphWeight, sbmLabelWeight, sbmEdgeWeight]
  simp [Fin.prod_univ_two, SimpleGraph.bot_adj]
  have hvez : (∑ z : Fin 2 → Fin 2, sbmP (z 0) * sbmP (z 1) *
      (1 - sbmW (z 0) (z 1))) =
      ∑ p : Fin 2 × Fin 2, sbmP p.1 * sbmP p.2 * (1 - sbmW p.1 p.2) :=
    Equiv.sum_comp (finTwoArrowEquiv (Fin 2))
      (fun p : Fin 2 × Fin 2 => sbmP p.1 * sbmP p.2 * (1 - sbmW p.1 p.2))
  rw [hvez, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two, sbmP, sbmW]
  norm_num

/-- Empty weight on two vertices is `73/90` (swapped side, independent). -/
theorem weight_empty_swapped :
    sbmGraphWeight sbmP_swap sbmW_swap
      (⊥ : SimpleGraph (Fin 2)) = 73/90 := by
  classical
  simp only [sbmGraphWeight, sbmLabelWeight, sbmEdgeWeight]
  simp [Fin.prod_univ_two, SimpleGraph.bot_adj]
  have hvez : (∑ z : Fin 2 → Fin 2, sbmP_swap (z 0) *
      sbmP_swap (z 1) * (1 - sbmW_swap (z 0) (z 1))) =
      ∑ p : Fin 2 × Fin 2, sbmP_swap p.1 * sbmP_swap p.2 * (1 - sbmW_swap p.1 p.2) :=
    Equiv.sum_comp (finTwoArrowEquiv (Fin 2))
      (fun p : Fin 2 × Fin 2 => sbmP_swap p.1 * sbmP_swap p.2 * (1 - sbmW_swap p.1 p.2))
  rw [hvez, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two, sbmP_swap, sbmW_swap, sbmP, sbmW,
    sbmSwap, Function.comp_apply]
  norm_num

/-- Normalization values sum to one: `73/90 + 17/90 = 1`. -/
theorem norm_73_17 : (73/90 : ℝ) + 17/90 = 1 := by
  norm_num

/-- Graph weights sum to one on two vertices (admissible). -/
theorem sum_weight_two :
    ∑ G : SimpleGraph (Fin 2), sbmGraphWeight sbmP sbmW G = 1 :=
  sum_sbmGraphWeight sbm_admissible_orig

/-- Nonnegativity on two vertices at the top graph. -/
theorem weight_nonneg_two :
    0 ≤ sbmGraphWeight sbmP sbmW (⊤ : SimpleGraph (Fin 2)) :=
  sbmGraphWeight_nonneg _ sbm_admissible_orig

/-- PMF evaluation on two vertices at the top graph. -/
theorem pmf_apply_two :
    sbmGraphPMF sbmP sbmW sbm_admissible_orig
      (⊤ : SimpleGraph (Fin 2)) =
      ENNReal.ofReal (17/90) := by
  rw [sbmGraphPMF_apply, weight_edge_orig]

/-- Relabeling collision on three vertices as functions. -/
theorem relabel_collision_three :
    sbmGraphWeight (V := Fin 3) sbmP_swap sbmW_swap =
      sbmGraphWeight (V := Fin 3) sbmP sbmW := by
  have h := sbmGraphWeight_relabel (V := Fin 3) (p := sbmP)
    (W := sbmW) sbmSwap
  unfold sbmP_swap sbmW_swap
  exact h

/-- Collision in valid space on three vertices: same `PMF` and no
injectivity for the admissible map. -/
theorem collision_valid_three :
    sbmGraphPMF (V := Fin 3) sbmP_swap sbmW_swap
      (SBMAdmissible_relabel sbmSwap sbm_admissible_orig) =
      sbmGraphPMF (V := Fin 3) sbmP sbmW sbm_admissible_orig ∧
      ¬ Function.Injective
        (fun θ : {θ : (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) //
          SBMAdmissible θ.1 θ.2} =>
          sbmGraphPMF (V := Fin 3) θ.1.1 θ.1.2 θ.2) := by
  have hEq : sbmGraphPMF (V := Fin 3) (sbmP ∘ sbmSwap)
    (fun i j => sbmW (sbmSwap i) (sbmSwap j))
    (SBMAdmissible_relabel sbmSwap sbm_admissible_orig) =
    sbmGraphPMF (V := Fin 3) sbmP sbmW sbm_admissible_orig :=
    sbmGraphPMF_relabel (V := Fin 3) sbmSwap sbm_admissible_orig
  have hNe : (sbmP ∘ sbmSwap,
    fun i j => sbmW (sbmSwap i) (sbmSwap j)) ≠ (sbmP, sbmW) :=
    swapped_ne
  have hNot := not_injective_sbmGraphPMF_of_relabel_ne (Fin 3)
    sbmSwap sbm_admissible_orig hNe
  refine ⟨?_, hNot⟩
  unfold sbmP_swap sbmW_swap
  exact hEq

end

end MathlibExtTest.Probability.Networks
