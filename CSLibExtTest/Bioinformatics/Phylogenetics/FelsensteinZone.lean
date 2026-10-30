/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Phylogenetics.FelsensteinZone
public meta import CSLibExt.Bioinformatics.Phylogenetics.FelsensteinZone

/-!
# Tests for the pulley principle, LogDet distances, the Felsenstein zone and NJ consistency

* Non-vacuity of `IsReversibleSemigroup`: the Jukes–Cantor model with the uniform distribution,
  and every GTR model; the pulley moves on a concrete Jukes–Cantor quartet.
* LogDet: the distance of a vertex to itself, a concrete three-point instance, the junk value of
  a singular joint distribution (independent sites), and a two-step path.
* The Felsenstein zone: the pattern distribution sums to `1`; a point inside the zone
  (`P = 2/5`, `Q = 1/10`); the boundary `Q = 1/2` and the diagonal `P = Q`, where the
  differences vanish; Fitch scores of an informative pattern on the three quartets.
* Jukes–Cantor: the path matrix of `[1, 2]` is the matrix of length `3`; corrected distances of a
  taxon to itself are `0`.
-/

@[expose] public section

namespace CSLibExtTest.Bioinformatics.Phylogenetics.FelsensteinZone

open Cslib.Bioinformatics.Phylogenetics FelsensteinPruning Tree FelsensteinZone Parsimony
open MathlibExt.Biology.Phylogenetics.JukesCantor
open MathlibExt.Biology.Phylogenetics.SubstitutionModels
open Matrix ProbabilityTheory

/-! ### The pulley principle -/

/-- Non-vacuity: the Jukes–Cantor transition probabilities form a reversible semigroup for the
uniform distribution. -/
theorem jc_isReversibleSemigroup (μ : ℝ) :
    IsReversibleSemigroup (fun _ : Fin 4 => (1 / 4 : ℝ)) (jcProb μ) where
  chapman_kolmogorov s t a c := sum_jcProb_mul_jcProb μ s t a c
  detailed_balance t a b := by
    unfold jcProb
    by_cases h : a = b
    · subst h; rfl
    · simp [h, Ne.symm h]

/-- Every GTR model gives a reversible semigroup. -/
theorem gtr_isReversibleSemigroup (π : Fin 4 → ℝ) {s : Matrix (Fin 4) (Fin 4) ℝ}
    (hs : ∀ i j, s i j = s j i) :
    IsReversibleSemigroup π (fun t => ctmcTransition (gtrRate π s) t) :=
  isReversibleSemigroup_ctmcTransition (isDetailedBalance_gtrRate π hs)

/-- Leaf data: taxon `0` shows base `0`, the other taxa base `1`. -/
def obs₀ (l : Fin 4) (b : Fin 4) : ℝ :=
  if b = (if l = 0 then 0 else 1) then 1 else 0

/-- Sliding the root of a Jukes–Cantor quartet along the internal edge. -/
example : likelihood obs₀
      (node (jcProb 1 (1 / 3)) (node (jcProb 1 1) (leaf 0) (jcProb 1 2) (leaf 1))
        (jcProb 1 (2 / 3)) (node (jcProb 1 1) (leaf 2) (jcProb 1 1) (leaf 3)))
      (fun _ => 1 / 4) =
    likelihood obs₀
      (node (jcProb 1 0) (node (jcProb 1 1) (leaf 0) (jcProb 1 2) (leaf 1))
        (jcProb 1 1) (node (jcProb 1 1) (leaf 2) (jcProb 1 1) (leaf 3)))
      (fun _ => 1 / 4) :=
  likelihood_slide (jc_isReversibleSemigroup 1) obs₀ _ _ (by norm_num)

/-- Rerooting a Jukes–Cantor quartet onto the pendant edge of taxon `0`. -/
example : likelihood obs₀
      (node (jcProb 1 (1 / 3)) (node (jcProb 1 1) (leaf 0) (jcProb 1 2) (leaf 1))
        (jcProb 1 (2 / 3)) (leaf 2))
      (fun _ => 1 / 4) =
    likelihood obs₀
      (node (jcProb 1 (1 / 2)) (leaf 0) (jcProb 1 (1 / 2))
        (node (jcProb 1 2) (leaf 1) (jcProb 1 (1 / 3 + 2 / 3)) (leaf 2)))
      (fun _ => 1 / 4) :=
  likelihood_reroot (jc_isReversibleSemigroup 1) obs₀ _ _ _ (by norm_num)

/-! ### LogDet -/

/-- The distance of a vertex to itself is `0`. -/
example : paralinear (diagonal fun _ : Fin 2 => (1 / 2 : ℝ)) = 0 :=
  paralinear_diagonal fun _ => by norm_num

/-- A symmetric two-state transition matrix with change probability `1/4`. -/
noncomputable def M₀ : Matrix (Fin 2) (Fin 2) ℝ := !![3 / 4, 1 / 4; 1 / 4, 3 / 4]

theorem det_M₀ : M₀.det = 1 / 2 := by
  simp [M₀, det_fin_two]
  norm_num

theorem rowSum_M₀ (i : Fin 2) : ∑ j, M₀ i j = 1 := by
  fin_cases i <;> simp [M₀, Fin.sum_univ_two] <;> norm_num

/-- Non-vacuity of the three-point hypotheses: two branches with change probability `1/4` from
a uniform middle vertex. -/
example : paralinear (M₀ᵀ * diagonal (fun _ => 1 / 2) * M₀) =
    paralinear (M₀ᵀ * diagonal (fun _ => 1 / 2)) + paralinear (diagonal (fun _ => 1 / 2) * M₀) :=
  paralinear_threePoint (fun _ => by norm_num) rowSum_M₀ rowSum_M₀ (by rw [det_M₀]; norm_num)
    (by rw [det_M₀]; norm_num)

/-- A two-step path with change probability `1/4` on each edge. -/
example : paralinear (diagonal (fun _ => 1 / 2) * pathProd (fun _ => M₀) 2) =
    ∑ i ∈ Finset.range 2,
      paralinear (diagonal ((fun _ => 1 / 2) ᵥ* pathProd (fun _ => M₀) i) * M₀) :=
  paralinear_pathProd (fun _ => by norm_num)
    (fun _ i j => by fin_cases i <;> fin_cases j <;> norm_num [M₀]) (fun _ => rowSum_M₀)
    (fun _ => by rw [det_M₀]; norm_num) 2

/-- Junk value outside the domain: for independent states (`det F = 0`) the true distance is
infinite, but Lean's `log 0 = 0` gives `log (1/4)`. -/
example : paralinear (fun _ _ => 1 / 4 : Matrix (Fin 2) (Fin 2) ℝ) = Real.log (1 / 4) := by
  have h : (Matrix.of fun _ _ => (1 / 4 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 0 := by
    simp [det_fin_two]
  have h2 : (1 / 4 + 1 / 4 : ℝ) * (1 / 4 + 1 / 4) = 1 / 4 := by norm_num
  simp only [paralinear, Fin.sum_univ_two, Fin.prod_univ_two]
  rw [show (fun _ _ => (1 / 4 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.of fun _ _ => 1 / 4
    from rfl, h, h2]
  simp

/-! ### The Felsenstein zone -/

/-- The pattern distribution of the quartet sums to `1`. -/
example : ∑ σ, patternProb (2 / 5) (1 / 10) (2 / 5) (1 / 10) (1 / 10) σ = 1 :=
  sum_patternProb _ _ _ _ _

/-- Inside the zone: `P = 2/5`, `Q = 1/10` (`P ^ 2 = 0.16 > 0.09 = Q (1 - Q)`). -/
example : splitFreq (2 / 5) (1 / 10) (2 / 5) (1 / 10) (1 / 10) 0 2 1 3 -
    splitFreq (2 / 5) (1 / 10) (2 / 5) (1 / 10) (1 / 10) 0 1 2 3 = 7 / 125 := by
  rw [splitFreq_wrong_sub_true]
  norm_num

/-- Inside the zone parsimony prefers the wrong quartet. -/
example : expectedScore (2 / 5) (1 / 10) (2 / 5) (1 / 10) (1 / 10) 0 2 1 3 <
    expectedScore (2 / 5) (1 / 10) (2 / 5) (1 / 10) (1 / 10) 0 1 2 3 :=
  (expectedScore_wrong_lt (by norm_num) (by norm_num) (by norm_num)).1

/-- Outside the zone (`P = Q = 1/10`) the true split is the most frequent. -/
example : splitFreq (1 / 10) (1 / 10) (1 / 10) (1 / 10) (1 / 10) 0 2 1 3 <
    splitFreq (1 / 10) (1 / 10) (1 / 10) (1 / 10) (1 / 10) 0 1 2 3 := by
  have := splitFreq_wrong_sub_true (1 / 10) (1 / 10)
  norm_num at this
  linarith

/-- Boundary `Q = 1/2`: the wrong and true splits are equally frequent. -/
example (P : ℝ) : splitFreq P (1 / 2) P (1 / 2) (1 / 2) 0 2 1 3 =
    splitFreq P (1 / 2) P (1 / 2) (1 / 2) 0 1 2 3 := by
  have := splitFreq_wrong_sub_true P (1 / 2)
  norm_num at this
  linarith

/-- Diagonal `P = Q`: the wrong and third splits are equally frequent. -/
example (Q : ℝ) : splitFreq Q Q Q Q Q 0 2 1 3 = splitFreq Q Q Q Q Q 0 3 1 2 := by
  have := splitFreq_wrong_sub_third Q Q
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero] at this
  linarith

/-- Pattern probabilities are nonnegative inside the model domain. -/
example (σ : Fin 4 → Bool) : 0 ≤ patternProb (2 / 5) (1 / 10) (2 / 5) (1 / 10) (1 / 10) σ :=
  patternProb_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) σ

/-- The pattern `1100` supports `AB | CD`: one change on that quartet, two on the others. -/
example : parsimonyScore 0 1 2 3 ![true, true, false, false] = 1 ∧
    parsimonyScore 0 2 1 3 ![true, true, false, false] = 2 ∧
    parsimonyScore 0 3 1 2 ![true, true, false, false] = 2 := by
  decide

/-! ### Jukes–Cantor distances -/

/-- Chapman–Kolmogorov along a path of lengths `1` and `2`. -/
example (μ : ℝ) : jcPath μ [1, 2] = Matrix.of (jcProb μ 3) := by
  rw [jcPath_eq]
  norm_num

/-- The corrected distance along that path is `3 μ`. -/
example (μ : ℝ) : jcDistance (∑ j ∈ Finset.univ.erase 0, jcPath μ [1, 2] 0 j) = μ * 3 := by
  rw [jcDistance_jcPath]
  norm_num

/-- The corrected empirical distance of a taxon to itself is `0`. -/
example (seq : ℕ → Fin 3 → Fin 4) (n : ℕ) (x : Fin 3) : jcHat seq n x x = 0 := by
  simp [jcHat, pHat, jcDistance]

end CSLibExtTest.Bioinformatics.Phylogenetics.FelsensteinZone
