/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Phylogenetics.NeighborJoiningBME
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Neighbor joining: Q-criterion vs local star BME length: tests

* The coefficients of `T_ab` on four clusters: `1/2`, `1/4` and `1/2`.
* Non-vacuity of the run-level theorem: the start of every run on a symmetric dissimilarity
  with zero diagonal on four taxa satisfies its hypotheses (four singleton clusters), so the
  pairs neighbor joining may join first are exactly the pairs of least `cherryLength`, which
  at this first step is the BME length of the join tree on the taxa.
* Non-vacuity of `cherryLength_eq_length`: its realization hypothesis is satisfied by the
  dissimilarity it describes.
* Boundary: with two clusters, `|S| - 2 = 0` and Lean's `1 / 0 = 0` makes the coefficients
  outside `{a, b}` vanish (a junk value; every theorem assumes `|S| ≥ 3`).
-/

namespace Cslib.Bioinformatics.Phylogenetics.NeighborJoiningBME

open Finset Cslib.Bioinformatics.Phylogenetics.NeighborJoining

/-- The four singleton clusters of `Fin 4`. -/
def four : Finset (Finset (Fin 4)) := Finset.univ.image fun x => {x}

theorem card_four : four.card = 4 := by decide

example : cherryCoeff four {0} {1} {0} {1} = 1 / 2 := by simp [cherryCoeff]
example : cherryCoeff four {0} {1} {0} {2} = 1 / 4 := by
  simp [cherryCoeff, card_four]; norm_num
example : cherryCoeff four {0} {1} {2} {3} = 1 / 2 := by
  simp [cherryCoeff, card_four]; norm_num

/-- A symmetric dissimilarity on four taxa with zero diagonal (not a tree metric). -/
def d₄ : Fin 4 → Fin 4 → ℝ := fun x y => if x = y then 0 else (x.val + y.val + 1 : ℝ)

theorem d₄_symm (x y : Fin 4) : d₄ x y = d₄ y x := by
  unfold d₄
  by_cases h : x = y
  · subst h; rfl
  · simp only [h, Ne.symm h, ↓reduceIte]; ring

theorem d₄_diag (x : Fin 4) : d₄ x x = 0 := by simp [d₄]

-- At the start of a run, a pair of taxa minimizes `Q` iff joining it gives the least
-- `cherryLength` (the BME length of the join tree on the taxa at this first step).
example (a b : Finset (Fin 4)) (ha : a ∈ four) (hb : b ∈ four) (hab : a ≠ b) :
    (∀ a' ∈ four, ∀ b' ∈ four, a' ≠ b' →
        qCriterion four (initialDist d₄) a b ≤ qCriterion four (initialDist d₄) a' b') ↔
      ∀ a' ∈ four, ∀ b' ∈ four, a' ≠ b' →
        cherryLength four (initialDist d₄) a b ≤ cherryLength four (initialDist d₄) a' b' :=
  NJRun.isMin_qCriterion_iff_cherryLength d₄_symm d₄_diag NJRun.init (by decide) ha hb hab

-- The dissimilarity stays symmetric with zero diagonal along the run.
example : (∀ u v, initialDist d₄ u v = initialDist d₄ v u) ∧
    ∀ u ∈ four, initialDist d₄ u u = 0 :=
  NJRun.symm_diag d₄_symm d₄_diag NJRun.init

/-- The path-length dissimilarity of `T_ab` described in `cherryLength_eq_length`. -/
noncomputable def treeDist (a b : Finset (Fin 4)) (ℓ : Finset (Fin 4) → ℝ) (m : ℝ)
    (u v : Finset (Fin 4)) : ℝ :=
  if (u = a ∨ u = b) ∧ (v = a ∨ v = b) then ℓ u + ℓ v
  else if u = a ∨ u = b ∨ v = a ∨ v = b then ℓ u + m + ℓ v
  else ℓ u + ℓ v

-- Non-vacuity: the realization hypothesis holds for `treeDist`, so on the four singletons
-- with pendant lengths `ℓ` and internal length `m` the BME length is the tree length.
example (ℓ : Finset (Fin 4) → ℝ) (m : ℝ) :
    cherryLength four (treeDist {0} {1} ℓ m) {0} {1} = ∑ c ∈ four, ℓ c + m :=
  cherryLength_eq_length four (by rw [card_four]; norm_num) (by decide) (by decide) (by decide)
    ℓ m _ fun _ _ _ _ _ => rfl

/-! ## Boundary: two clusters -/

/-- Two singleton clusters. -/
def two : Finset (Finset (Fin 2)) := {{0}, {1}}

-- With `|S| = 2` the coefficient `1 / (|S| - 2)` is Lean's `1 / 0 = 0` (junk value).
example : cherryCoeff two {0} {0} {1} {1} = 0 := by
  have : two.card = 2 := by decide
  simp [cherryCoeff, this]

end Cslib.Bioinformatics.Phylogenetics.NeighborJoiningBME
