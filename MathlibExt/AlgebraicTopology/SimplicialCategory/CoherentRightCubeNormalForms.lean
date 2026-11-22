/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeReduction

/-!
# Genuine normal forms of the original right-cube quotient

Reduction at the actual first maximum removes precisely the mutable
original front prefix. Each generating relation has the same whole
reduced path chain, and the actual generated equivalence relation is
therefore exactly equality of these normal forms. No quotient or
relative-latching comparison is supplied as input.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.RightCubeNormalForms
open PathLastMaximum RightCubeRelations RightCubePrefixCylinder RightCubeReduction
variable {n : ℕ}

/-- A prefix below the retained cut contributes no original suffix label beyond the actual zero insertion. -/
theorem trim_prefix (i j : Fin (n + 1)) (hji : j ≤ i) (p : Prefix.{u} j) (r : LastPath.{u} j) :
    {ULift.up.{u} (0 : Fin (n + 2))} ∪ {x | x ∈ p.I ∪ r.I ∧ ULift.up.{u} i.castSucc ≤ x} =
      {ULift.up.{u} (0 : Fin (n + 2))} ∪ {x | x ∈ ({ULift.up.{u} (0 : Fin (n + 2))} ∪ r.I) ∧ ULift.up.{u}
        i.castSucc ≤ x} := by
  ext x
  change (x = ULift.up.{u} (0 : Fin (n + 2)) ∨ ((x ∈ p.I ∨ x ∈ r.I) ∧ ULift.up i.castSucc ≤ x)) ↔
    (x = ULift.up.{u} (0 : Fin (n + 2)) ∨ ((x = ULift.up.{u} (0 : Fin (n + 2)) ∨ x ∈ r.I) ∧ ULift.up i.castSucc ≤ x))
  constructor
  · rintro (h₀ | ⟨hp | hr, hi⟩)
    · exact Or.inl h₀
    · have hx : x = ULift.up.{u} j.castSucc :=
        le_antisymm (p.le_right x hp) (le_trans (show ULift.up.{u} j.castSucc ≤ ULift.up i.castSucc from hji) hi)
      exact Or.inr ⟨Or.inr (hx.symm ▸ r.left), hi⟩
    · exact Or.inr ⟨Or.inr hr, hi⟩
  · rintro (h₀ | ⟨h₀ | hr, hi⟩)
    · exact Or.inl h₀
    · exact Or.inl h₀
    · exact Or.inr ⟨Or.inr hr, hi⟩

/-- Each original generating front-prefix relation has exactly the same whole first-maximum reduced chain. -/
theorem relation_normalize {q : SimplexCategoryᵒᵖ}
    {a b : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q}
    (h : RightCubeRelations.Relation n a b) : normalize a = normalize b := by
  cases h with
  | composition j p r =>
    have ha : initialMaximum (p.prod' r ⋙ composeFunctor.{u} j) = maximum j (r.obj 0) :=
      maximum_compose 0 j (p.obj 0) (r.obj 0)
    have hb : initialMaximum (r ⋙ prependFunctor j) = maximum j (r.obj 0) :=
      RightCubeMaximum.maximum_prepend j (r.obj 0)
    refine Functor.ext (fun k => ?_) ?_
    · apply SimplicialThickening.Path.ext
      change {ULift.up.{u} (0 : Fin (n + 2))} ∪
        {x | x ∈ (p.obj k).I ∪ (r.obj k).I ∧
          ULift.up.{u} (initialMaximum (p.prod' r ⋙ composeFunctor.{u} j)).castSucc ≤ x} =
        {ULift.up.{u} (0 : Fin (n + 2))} ∪
          {x | x ∈ ({ULift.up.{u} (0 : Fin (n + 2))} ∪ (r.obj k).I) ∧
            ULift.up.{u} (initialMaximum (r ⋙ prependFunctor j)).castSucc ≤ x}
      rw [ha, hb]
      exact trim_prefix (maximum j (r.obj 0)) j (source_le_maximum j (r.obj 0)) (p.obj k) (r.obj k)
    · intro k l f
      apply InducedCategory.Hom.ext
      exact Subsingleton.elim _ _

/-- The actual generated cube equivalence relation preserves the same whole normal form in every scalar degree. -/
theorem setoid_normalize {q : SimplexCategoryᵒᵖ}
    {a b : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q}
    (h : (setoid.{u} n q).r a b) : normalize a = normalize b := by
  induction h with
  | rel a b h => exact relation_normalize h
  | refl a => rfl
  | symm a b h ih => exact ih.symm
  | trans a b c h h' ih ih' => exact ih.trans ih'

/-- Two actual original chain representatives define the same cube class exactly when their whole reduced
  original chains agree. -/
theorem setoid_iff_normalize_eq {q : SimplexCategoryᵒᵖ}
    (a b : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q) :
    (setoid.{u} n q).r a b ↔ normalize a = normalize b := by
  constructor
  · exact setoid_normalize
  · intro h
    exact Relation.EqvGen.trans _ _ _ (related_normalize a)
      (Relation.EqvGen.symm _ _ (h.symm ▸ related_normalize b))

/-- The actual first-maximum reduction is idempotent on the whole original scalar chain. -/
theorem normalize_idempotent {q : SimplexCategoryᵒᵖ}
    (a : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q) : normalize (normalize a) = normalize a :=
  (setoid_normalize (related_normalize a)).symm

end CategoryTheory.CoherentRealization.RightCubeNormalForms
