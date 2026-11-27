/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.WeightedSimplicialFaceLaws
import Mathlib.Tactic.NormNum

/-!
# Tests of weighted simplicial face laws

The two edges of a path share exactly one vertex. Sampling a top edge before choosing a
vertex distinguishes the middle vertex even when the two edges have equal probabilities.
For top cardinality zero, the family `{∅}` has one top face and its rank law is the same
point mass. The void family `∅` has no weighting at any top cardinality.
-/

open MathlibExt.Combinatorics MathlibExt.Combinatorics.RationalSimplicialHomologyShared
open scoped ENNReal

namespace WeightedSimplicialFaceLawsTest

private def path := ({0, 1} : Finset ℕ).powerset ∪ ({1, 2} : Finset ℕ).powerset
private def leftEdge : facesOfCard path 2 := ⟨{0, 1}, by decide⟩
private def rightEdge : facesOfCard path 2 := ⟨{1, 2}, by decide⟩
private def a : facesOfCard path 1 := ⟨{0}, by decide⟩
private def b : facesOfCard path 1 := ⟨{1}, by decide⟩
private def c : facesOfCard path 1 := ⟨{2}, by decide⟩

private theorem topUniv : (Finset.univ : Finset (facesOfCard path 2)) = {leftEdge, rightEdge} :=
  by decide

private theorem pathComplex : IsSimplicialComplex path := by
  intro σ hσ τ hτ
  rcases Finset.mem_union.mp hσ with h | h
  · exact Finset.mem_union_left _ (Finset.mem_powerset.mpr (hτ.trans (Finset.mem_powerset.mp h)))
  · exact Finset.mem_union_right _ (Finset.mem_powerset.mpr (hτ.trans (Finset.mem_powerset.mp h)))

private theorem pathPure (τ : Finset ℕ) (hτ : τ ∈ path) :
    ∃ σ : facesOfCard path 2, τ ⊆ σ.val := by
  rcases Finset.mem_union.mp hτ with h | h
  · exact ⟨leftEdge, Finset.mem_powerset.mp h⟩
  · exact ⟨rightEdge, Finset.mem_powerset.mp h⟩

private noncomputable def w (σ : facesOfCard path 2) : ℝ := if σ = leftEdge then 1 / 4 else 3 / 4

private noncomputable def weighted : PureWeightedComplex path 1 where
  simplicial := pathComplex
  covers := pathPure
  topLaw := PMF.ofFintype (fun σ => ENNReal.ofReal (w σ)) (by
    rw [topUniv, Finset.sum_pair (by decide : leftEdge ≠ rightEdge)]
    rw [← ENNReal.ofReal_add (by norm_num [w]) (by norm_num [w, show rightEdge ≠ leftEdge by decide])]
    norm_num [w, show rightEdge ≠ leftEdge by decide])
  top_pos σ := by
    simp only [PMF.ofFintype_apply, ENNReal.ofReal_pos, w]
    split <;> norm_num

private noncomputable def fair : PureWeightedComplex path 1 :=
  PureWeightedComplex.uniform pathComplex pathPure ⟨leftEdge.val, leftEdge.property⟩

private theorem vertexMasses (X : PureWeightedComplex path 1) :
    ((X.faceLaw (by decide : 1 ≤ 2) a).toReal,
      (X.faceLaw (by decide : 1 ≤ 2) b).toReal, (X.faceLaw (by decide : 1 ≤ 2) c).toReal) =
    ((X.topLaw leftEdge).toReal / 2,
      ((X.topLaw leftEdge).toReal + (X.topLaw rightEdge).toReal) / 2,
      (X.topLaw rightEdge).toReal / 2) := by
  have two (f : facesOfCard path (1 + 1) → ℝ) : ∑ σ, f σ = f leftEdge + f rightEdge := by
    rw [topUniv, Finset.sum_pair (by decide : leftEdge ≠ rightEdge)]
  simp only [X.faceLaw_toReal, Finset.sum_filter, two]
  norm_num [show a.val ⊆ leftEdge.val by decide, show ¬a.val ⊆ rightEdge.val by decide,
    show b.val ⊆ leftEdge.val by decide, show b.val ⊆ rightEdge.val by decide,
    show ¬c.val ⊆ leftEdge.val by decide, show c.val ⊆ rightEdge.val by decide, Nat.choose]

-- A nonuniform top law: the two coface contributions both reach the middle vertex.
example : ((weighted.faceLaw (by decide : 1 ≤ 2) a).toReal,
    (weighted.faceLaw (by decide : 1 ≤ 2) b).toReal, (weighted.faceLaw (by decide : 1 ≤ 2) c).toReal) =
    (1 / 8, 1 / 2, 3 / 8) := by
  rw [vertexMasses]
  norm_num [weighted, w, show rightEdge ≠ leftEdge by decide]

-- Uniform top edges do not make all three singleton outcomes equiprobable.
example : ((fair.faceLaw (by decide : 1 ≤ 2) a).toReal,
    (fair.faceLaw (by decide : 1 ≤ 2) b).toReal, (fair.faceLaw (by decide : 1 ≤ 2) c).toReal) =
    (1 / 4, 1 / 2, 1 / 4) := by
  rw [vertexMasses]
  norm_num [fair, PureWeightedComplex.uniform, PureWeightedComplexOfRank.uniform,
    show Fintype.card ↥(facesOfCard path 2) = 2 by decide]

-- The augmented bottom rank has one outcome; the top rank retains the unequal edge masses.
example : weighted.faceLaw (by decide : 0 ≤ 2) ⟨∅, by decide⟩ = 1 := by
  rw [weighted.faceLaw_zero, PMF.pure_apply]
  exact ite_eq_left (Subtype.ext rfl)

example : (weighted.faceLaw (by decide : 2 ≤ 2) rightEdge).toReal = 3 / 4 := by
  rw [weighted.faceLaw_top]
  norm_num [weighted, w, show rightEdge ≠ leftEdge by decide]

-- In the family whose sole face is empty, that face itself is the top draw.
private def emptyOnly : Finset (Finset ℕ) := {∅}
private def rootFace : facesOfCard emptyOnly 0 := ⟨∅, by decide⟩

private noncomputable def augmented : PureWeightedComplexOfRank emptyOnly 0 :=
  PureWeightedComplexOfRank.uniform (by
    intro σ hσ τ hτ
    have hs : σ = ∅ := Finset.mem_singleton.mp hσ
    exact Finset.mem_singleton.mpr (Finset.subset_empty.mp (hs ▸ hτ))) (by
    intro τ hτ
    exact ⟨rootFace, (Finset.mem_singleton.mp hτ) ▸ Finset.Subset.rfl⟩)
    ⟨∅, rootFace.property⟩

example : augmented.topLaw = PMF.pure rootFace := by
  calc augmented.topLaw = augmented.faceLaw (le_refl 0) := augmented.faceLaw_top.symm
    _ = PMF.pure rootFace := augmented.faceLaw_zero

example : augmented.faceLaw (le_refl 0) = PMF.pure rootFace := augmented.faceLaw_zero

example : augmented.topLaw rootFace = 1 ∧ augmented.faceLaw (le_refl 0) rootFace = 1 := by
  have ht : augmented.topLaw = PMF.pure rootFace := augmented.faceLaw_top.symm.trans
    augmented.faceLaw_zero
  rw [ht, augmented.faceLaw_zero]
  exact ⟨PMF.pure_apply_self _, PMF.pure_apply_self _⟩

-- Downward closure and the covering condition hold vacuously for the void family,
-- but a PMF on any of its (empty) ranks is impossible.
example (r : ℕ) : ¬ Nonempty (PureWeightedComplexOfRank ∅ r) := by
  rintro ⟨X⟩
  obtain ⟨σ, _⟩ := X.topLaw.support_nonempty
  simpa [facesOfCard] using σ.property

end WeightedSimplicialFaceLawsTest
