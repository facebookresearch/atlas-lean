/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.Eigenstrat
public import Mathlib.MeasureTheory.Measure.Dirac.Def

@[expose] public section

open Matrix MeasureTheory MathlibExt.Biology.StatisticalGenetics.Eigenstrat
open MathlibExt.Probability.Statistics.PCA
open scoped InnerProductSpace

namespace MathlibExtTest.Biology.StatisticalGenetics.Eigenstrat

/-! ### Patterson's normalization -/

/-- Two individuals, one marker with counts `0` and `2`: `μ = 1`, `p̂ = 1/2`, and the normalized
entries are `∓1 / √(1/4) = ∓2`. -/
def C : Matrix (Fin 2) (Fin 1) ℝ := !![0; 2]

example : alleleFreq C 0 = 1 / 2 := by
  simp [alleleFreq, colMean, C, Fin.sum_univ_two]

example : normalizedGenotype C 0 0 = -2 ∧ normalizedGenotype C 1 0 = 2 := by
  have h : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  simp only [normalizedGenotype, center, alleleFreq, colMean, C, of_apply, Fin.sum_univ_two]
  norm_num [h]

/-- A monomorphic marker (`p̂ = 0`) has normalized column equal to the junk value `0`. -/
example (i : Fin 2) : normalizedGenotype (0 : Matrix (Fin 2) (Fin 1) ℝ) i 0 = 0 := by
  simp [normalizedGenotype, center, colMean]

/-- `Ψ 1 = 0` for any genotype matrix with at least one individual. -/
example (C : Matrix (Fin 5) (Fin 7) ℝ) : relatednessMatrix C *ᵥ 1 = 0 :=
  relatednessMatrix_mulVec_one C (by norm_num)

/-- The top two axes of five individuals span a plane. -/
example (C : Matrix (Fin 5) (Fin 7) ℝ) : Module.finrank ℝ (topAxesSpan C 2) = 2 :=
  finrank_topAxesSpan C (by norm_num)

/-! ### Residualization -/

/-- Adjusting for nothing (`V = ⊥`) leaves vectors unchanged. -/
example (y : EuclideanSpace ℝ (Fin 3)) : adjusted ⊥ y = y :=
  adjusted_of_mem_orthogonal ⊥
    (by rw [Submodule.bot_orthogonal_eq_top]; exact Submodule.mem_top)

/-- Adjusting for everything (`V = ⊤`) leaves nothing. -/
example (y : EuclideanSpace ℝ (Fin 3)) : adjusted ⊤ y = 0 :=
  (adjusted_eq_zero_iff ⊤ y).mpr Submodule.mem_top

/-- Stratification lying in the adjustment subspace is removed from the phenotype. -/
example (V : Submodule ℝ (EuclideanSpace ℝ (Fin 4))) (s z : EuclideanSpace ℝ (Fin 4))
    (hs : s ∈ V) : adjusted V (s + z) = adjusted V z :=
  adjusted_add_of_mem V hs z

/-- Frisch–Waugh–Lovell is non-vacuous: the existence form produces a decomposition, and the
uniqueness form then identifies its coefficient. -/
example (V : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) (y g : EuclideanSpace ℝ (Fin 3))
    (hg : adjusted V g ≠ 0) :
    ∃ c ∈ V, ∃ β : ℝ, y - c - β • g ∈ (V ⊔ Submodule.span ℝ {g})ᗮ ∧
      β = ⟪adjusted V g, adjusted V y⟫_ℝ / ‖adjusted V g‖ ^ 2 :=
  let ⟨c, hc, he⟩ := exists_frischWaughLovell V y g
  ⟨c, hc, _, he, (frischWaughLovell V y g hg hc _ he).1⟩

/-- The identifiability hypothesis of Frisch–Waugh–Lovell holds for a nonzero SNP vector when
nothing is adjusted for. -/
example :
    adjusted (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin 2))) (EuclideanSpace.single 0 1) ≠ 0 := by
  rw [Ne, adjusted_eq_zero_iff, Submodule.mem_bot]
  intro h
  have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) h
  simp at this

/-- Axis-by-axis adjustment on the first coordinate axis of `ℝ²` keeps the second coordinate. -/
example (y : EuclideanSpace ℝ (Fin 2)) :
    adjusted (Submodule.span ℝ (Set.range ![EuclideanSpace.single (0 : Fin 2) (1 : ℝ)])) y =
      y - ⟪EuclideanSpace.single 0 1, y⟫_ℝ • EuclideanSpace.single 0 1 := by
  rw [adjusted_span_orthonormal]
  · simp
  · rw [orthonormal_iff_ite]
    intro i j
    fin_cases i; fin_cases j
    simp

/-! ### The EIGENSTRAT statistic -/

/-- The statistic is between `0` and `N - K - 1`. -/
example (V : Submodule ℝ (EuclideanSpace ℝ (Fin 10))) (y g : EuclideanSpace ℝ (Fin 10)) :
    0 ≤ chiSq V 3 y g ∧ chiSq V 3 y g ≤ 6 := by
  refine ⟨chiSq_nonneg V (by norm_num) y g, ?_⟩
  have := chiSq_le V (K := 3) (by norm_num) y g
  norm_num at this
  linarith

/-- With no adjustment and a phenotype equal to the genotype (perfect correlation), the statistic
attains its maximum `N - K - 1 = 3 - 0 - 1 = 2`. -/
example (g : EuclideanSpace ℝ (Fin 3)) (hg : g ≠ 0) : chiSq ⊥ 0 g g = 2 := by
  have h0 : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg
  have hr : adjusted ⊥ g = g := adjusted_of_mem_orthogonal ⊥
    (by rw [Submodule.bot_orthogonal_eq_top]; exact Submodule.mem_top)
  simp only [chiSq, hr, real_inner_self_eq_norm_sq]
  field_simp
  norm_num

/-- A genotype lying entirely in the axis span gives the statistic `0`. -/
example (V : Submodule ℝ (EuclideanSpace ℝ (Fin 4))) (y g : EuclideanSpace ℝ (Fin 4))
    (hg : g ∈ V) : chiSq V 2 y g = 0 :=
  chiSq_of_mem V 2 y hg

/-! ### Number of significant axes -/

/-- Statistics `3, 2, 1/2, 5` with threshold `1`: the sequential rule stops at the third, so two
axes are significant, although the fourth statistic also exceeds the threshold. -/
noncomputable def stat : ℕ → ℝ := fun k => if k = 0 then 3 else if k = 1 then 2 else
  if k = 2 then 1 / 2 else 5

example : numSignificant stat 1 4 = 2 := by
  simp [numSignificant, stat]
  norm_num

/-- Decreasing statistics `10, 9, 8, 7, 6` with threshold `7`: three are significant. -/
example : numSignificant (fun k => (10 : ℝ) - k) 7 5 = 3 := by
  simp [numSignificant]
  norm_num

/-- Non-vacuity of the conditional error bound: a point-mass null under which the leading
statistic is `0`, below the threshold `1`, so the null-tail hypothesis holds with `F 1 = 0.95`. -/
example : (Measure.dirac ()) {_ω : Unit | 0 < numSignificant (fun _ => (0 : ℝ)) 1 3} ≤
    ENNReal.ofReal (1 - 0.95) :=
  measure_lt_numSignificant_le (Measure.dirac ()) (fun _ _ => 0) (fun _ => 0.95) 1 3 0
    (by simp)

end MathlibExtTest.Biology.StatisticalGenetics.Eigenstrat
