/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.SplitDecompositionCanonicalDecompResidueEqZeroOfTreeLike
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for vanishing tree-like split residues

Canonical decompositions reconstruct a four-point star from their split summands alone, including
when two labels share a zero-distance class.
-/

namespace MathlibExtTest.Combinatorics.SimpleGraph
namespace SplitDecompositionCanonicalDecompResidueEqZeroOfTreeLike

open WantedExt.Biology.ComputationalBiology.SplitDecompositionWanted
open MathlibExt.Biology.Phylogenetics.Buneman

private def star (x y : Fin 4) : ℝ := if x = y then 0 else 2

private lemma star_metric : IsMetric star := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    simp [star]
  · intro x y
    simp [star, eq_comm]
  · intro x y z
    fin_cases x <;> fin_cases y <;> fin_cases z <;> norm_num [star]

private lemma star_fourPoint : FourPointCondition star := by
  intro x y z t
  fin_cases x <;> fin_cases y <;> fin_cases z <;> fin_cases t <;> norm_num [star]

private lemma reconstruct {Y : Type*} [Fintype Y] [DecidableEq Y]
    {d r : Y → Y → ℝ} {k : ℕ} {ds : Fin k → Y → Y → ℝ}
    (hcanon : IsCanonicalDecomp d k ds r) (hr : ∀ x y, r x y = 0) :
    ∀ x y, ∑ i, ds i x y = d x y := by
  intro x y
  simpa [hr x y] using (hcanon.2.2.2.1 x y).symm

example (k : ℕ) (ds : Fin k → Fin 4 → Fin 4 → ℝ) (r : Fin 4 → Fin 4 → ℝ)
    (hcanon : IsCanonicalDecomp star k ds r) :
    r = 0 ∧ ∀ x y, ∑ i, ds i x y = star x y := by
  have hr := canonicalDecomp_residue_eq_zero_of_treeLike star star_metric star_fourPoint
    k ds r hcanon
  exact ⟨funext fun x => funext fun y => hr x y, reconstruct hcanon hr⟩

example : star 0 1 = 2 ∧ star 1 2 = 2 ∧ star 2 3 = 2 := by
  norm_num [star]

private def label (x : Fin 4) : Fin 4 := if x = 0 then 1 else x

private def repeatedStar (x y : Fin 4) : ℝ := star (label x) (label y)

private lemma repeatedStar_metric : IsMetric repeatedStar :=
  ⟨fun x => star_metric.1 (label x), fun x y => star_metric.2.1 (label x) (label y),
    fun x y z => star_metric.2.2 (label x) (label y) (label z)⟩

private lemma repeatedStar_fourPoint : FourPointCondition repeatedStar :=
  fun x y z t => star_fourPoint (label x) (label y) (label z) (label t)

example (k : ℕ) (ds : Fin k → Fin 4 → Fin 4 → ℝ) (r : Fin 4 → Fin 4 → ℝ)
    (hcanon : IsCanonicalDecomp repeatedStar k ds r) :
    r = 0 ∧ ∀ x y, ∑ i, ds i x y = repeatedStar x y := by
  have hr := canonicalDecomp_residue_eq_zero_of_treeLike repeatedStar repeatedStar_metric
    repeatedStar_fourPoint k ds r hcanon
  exact ⟨funext fun x => funext fun y => hr x y, reconstruct hcanon hr⟩

example : (0 : Fin 4) ≠ 1 ∧ repeatedStar 0 1 = 0 ∧ repeatedStar 0 2 = 2 ∧
    repeatedStar 2 3 = 2 := by
  norm_num [repeatedStar, label, star]

end SplitDecompositionCanonicalDecompResidueEqZeroOfTreeLike
end MathlibExtTest.Combinatorics.SimpleGraph
