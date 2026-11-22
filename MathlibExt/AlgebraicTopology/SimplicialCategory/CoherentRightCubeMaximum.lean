/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeRelations
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomFlagEvaluation
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentMaximumNerveOperators

/-!
# Actual original maximum map of the right-cube quotient

Original front-prefix composition retains the maximum of the same last
factor. The actual maximum map therefore descends to the constructed
right-cube quotient, and the original front flags are a section. This
section is not asserted to be a whole opposite inverse.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.RightCubeMaximum
open PathLastMaximum RightCubeRelations MaximumNerveOperators
variable {n : ℕ}

/-- Adding the structural zero source preserves the supplied original last path's actual largest front label. -/
theorem maximum_prepend (i : Fin (n + 1)) (p : LastPath.{u} i) :
    maximum 0 (prependZero i p) = maximum i p := by
  apply le_antisymm
  · apply Finset.max'_le
    intro j hj
    have hJ := (mem_frontSet 0 (prependZero i p) j).mp hj
    change ULift.up.{u} j.castSucc = ULift.up (0 : Fin (n + 2)) ∨ ULift.up.{u} j.castSucc ∈ p.I at hJ
    rcases hJ with h | h
    · have h₀ : j = 0 := Fin.ext (congrArg (fun a => a.down.val) h)
      subst j
      exact Fin.zero_le _
    · exact le_maximum i p j ((mem_frontSet i p j).mpr h)
  · apply le_maximum 0 (prependZero i p) (maximum i p)
    apply (mem_frontSet 0 (prependZero i p) _).mpr
    exact Or.inr ((mem_frontSet i p _).mp (maximum_mem i p))

/-- Each actual original front-prefix relation preserves the entire maximum-labelled standard-simplex image. -/
theorem relation_maximum {q : SimplexCategoryᵒᵖ}
    {a b : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q} (h : Relation n a b) :
    (maximumMap 0).app q a = (maximumMap 0).app q b := by
  cases h with
  | composition i p r =>
    induction q using Opposite.rec with
    | _ q =>
      induction q using SimplexCategory.rec with
      | _ d =>
        apply SSet.stdSimplex.ext
        intro j
        exact (maximum_compose 0 i (p.obj j) (r.obj j)).trans (maximum_prepend i (r.obj j)).symm

/-- The generated actual quotient relation preserves the original maximum image in every scalar degree. -/
theorem setoid_maximum {q : SimplexCategoryᵒᵖ}
    {a b : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q} (h : (setoid.{u} n q).r a b) :
    (maximumMap 0).app q a = (maximumMap 0).app q b := by
  induction h with
  | rel a b h => exact relation_maximum h
  | refl a => rfl
  | symm a b h ih => exact ih.symm
  | trans a b c h h' ih ih' => exact ih.trans ih'

/-- The genuine whole maximum map from the original right-cube quotient to the standard resolving simplex. -/
def map (n : ℕ) : RightCubeRelations.object.{u} n ⟶ (Δ[n] : SSet.{u}) where
  app q := ↾_root_.Quotient.lift ((maximumMap (0 : Fin (n + 1))).app q) (fun _ _ h => setoid_maximum h)
  naturality q r θ := by
    ext a
    induction a using _root_.Quotient.inductionOn with
    | _ a => exact congr($((maximumMap (0 : Fin (n + 1))).naturality θ) a)

/-- The whole original cube projection reads back the same actual maximum map. -/
theorem projection_map (n : ℕ) : RightCubeRelations.projection.{u} n ≫ map n = maximumMap (0 : Fin (n + 1))
    := by ext q a; rfl

/-- The actual original flag map into the constructed right-cube quotient. -/
def sectionMap (n : ℕ) : (Δ[n] : SSet.{u}) ⟶ RightCubeRelations.object.{u} n :=
  HomFlagEvaluation.flagMap ≫ RightCubeRelations.projection n

/-- The actual maximum quotient map retains its original flag section on the entire standard resolving simplex. -/
theorem section_map (n : ℕ) : sectionMap.{u} n ≫ map n = 𝟙 (Δ[n] : SSet.{u}) :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun f => HomFlagEvaluation.flagMap ≫ f) (projection_map n)).trans
      (HomFlagEvaluation.flag_maximum (n := n)))

end CategoryTheory.CoherentRealization.RightCubeMaximum
