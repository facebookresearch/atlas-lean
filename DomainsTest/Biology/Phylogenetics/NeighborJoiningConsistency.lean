/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.Phylogenetics.NeighborJoiningConsistency
public import Domains.Biology.Phylogenetics.SubstitutionModels

/-!
# The pulley principle and neighbor joining for nucleotide substitution models
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

/-! ### Jukes–Cantor distances -/

/-- Chapman–Kolmogorov along a path of lengths `1` and `2`. -/
example (μ : ℝ) : jcPath μ [1, 2] = Matrix.of (jcProb μ 3) := by
  rw [jcPath_eq]
  norm_num

/-- The corrected distance along that path is `3 μ`. -/
example (μ : ℝ) : jcDistance (∑ j ∈ Finset.univ.erase 0, jcPath μ [1, 2] 0 j) = μ * 3 := by
  rw [jcDistance_jcPath]
  norm_num

end CSLibExtTest.Bioinformatics.Phylogenetics.FelsensteinZone
