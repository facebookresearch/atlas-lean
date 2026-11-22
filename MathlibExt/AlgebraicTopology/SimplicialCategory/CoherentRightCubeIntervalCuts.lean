/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeZeroPrefix

/-!
# Actual original prefix and suffix cuts of right-cube chains

A specified original front vertex belonging to every path splits each
whole chain into an actual prefix and last interval. Their original
union is the same whole chain, with all scalar operators retained.
This uses actual membership of that vertex, not a quotient normal-form
or relative-frame outcome.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.RightCubeIntervalCuts
open PathLastMaximum RightCubePrefixCylinder
variable {n : ℕ}

/-- The actual original part at or below the supplied front vertex, with the same original zero source. -/
def cutPrefix (i : Fin (n + 1)) (p : LastPath.{u} (0 : Fin (n + 1)))
    (hi : ULift.up.{u} i.castSucc ∈ p.I) : Prefix.{u} i where
  I := {x | x ∈ p.I ∧ x ≤ ULift.up i.castSucc}
  left := ⟨p.left, Fin.zero_le _⟩
  right := ⟨hi, le_rfl⟩
  left_le x _ := Fin.zero_le x.down
  le_right _ hx := hx.2

/-- The actual original part at or above the supplied front vertex, retaining the original last target. -/
def suffix (i : Fin (n + 1)) (p : LastPath.{u} (0 : Fin (n + 1)))
    (hi : ULift.up.{u} i.castSucc ∈ p.I) : LastPath.{u} i where
  I := {x | x ∈ p.I ∧ ULift.up i.castSucc ≤ x}
  left := ⟨hi, le_rfl⟩
  right := ⟨p.right, Fin.le_last _⟩
  left_le _ hx := hx.2
  le_right x hx := p.le_right x hx.1

/-- The actual original prefix and suffix reunite by the same coherent path union. -/
theorem reunion (i : Fin (n + 1)) (p : LastPath.{u} (0 : Fin (n + 1)))
    (hi : ULift.up.{u} i.castSucc ∈ p.I) : compose 0 i (cutPrefix i p hi) (suffix i p hi) = p := by
  apply SimplicialThickening.Path.ext
  ext x
  change ((x ∈ p.I ∧ x ≤ ULift.up i.castSucc) ∨ (x ∈ p.I ∧ ULift.up i.castSucc ≤ x)) ↔ x ∈ p.I
  constructor
  · rintro (hx | hx)
    · exact hx.1
    · exact hx.1
  · intro hx
    rcases le_total x (ULift.up i.castSucc) with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩

/-- The original whole prefix chain at a specified vertex belonging to every actual path. -/
def prefixChain (i : Fin (n + 1)) {q : SimplexCategoryᵒᵖ}
    (p : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q)
    (hi : ∀ k, ULift.up.{u} i.castSucc ∈ (p.obj k).I) : (nerve (Prefix.{u} i)).obj q where
  obj k := cutPrefix i (p.obj k) (hi k)
  map f := ⟨homOfLE (fun x hx => ⟨(p.map f).hom.down.down hx.1, hx.2⟩)⟩

/-- The original whole suffix chain at the same specified vertex and literal last target. -/
def suffixChain (i : Fin (n + 1)) {q : SimplexCategoryᵒᵖ}
    (p : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q)
    (hi : ∀ k, ULift.up.{u} i.castSucc ∈ (p.obj k).I) : (nerve (LastPath.{u} i)).obj q where
  obj k := suffix i (p.obj k) (hi k)
  map f := ⟨homOfLE (fun x hx => ⟨(p.map f).hom.down.down hx.1, hx.2⟩)⟩

/-- Their original whole coherent union is exactly the original scalar chain, not merely a class or
  objectwise comparison. -/
theorem chain_reunion (i : Fin (n + 1)) {q : SimplexCategoryᵒᵖ}
    (p : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q)
    (hi : ∀ k, ULift.up.{u} i.castSucc ∈ (p.obj k).I) :
    (prefixChain i p hi).prod' (suffixChain i p hi) ⋙ composeFunctor i = p := by
  refine Functor.ext (fun k => reunion i (p.obj k) (hi k)) ?_
  intro k l f
  apply InducedCategory.Hom.ext
  exact Subsingleton.elim _ _

end CategoryTheory.CoherentRealization.RightCubeIntervalCuts
