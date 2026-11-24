/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomObjects
import Mathlib.CategoryTheory.Pi.Basic

/-!
# Actual interval-subset coherent Hom coordinates

The original coherent paths between supplied ordered vertices are
identified with subsets of their strict interior. This is a genuine
isomorphism of their Hom nerves, retaining the endpoints and the entire
scalar simplex data. No Kan or comparison outcome is an input.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.IntervalHom
variable {J : Type u} [LinearOrder J] (i j : J)

/-- The actual strict interior of the supplied original coherent interval. -/
abbrev Interior := {k : J // i < k ∧ k < j}

private instance (a b : SimplicialThickening.Path i j) : Subsingleton (a ⟶ b) where
  allEq f g := by
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _

/-- Restrict an actual endpoint-containing path to its strict interior coordinates. -/
def restrictPath : SimplicialThickening.Path i j ⥤ Set (Interior i j) where
  obj p := {k | k.val ∈ p.I}
  map f := homOfLE (fun _ hk => f.hom.down.down hk)

variable {i j}

/-- Reinsert exactly the two original endpoints into the supplied strict interior subset. -/
def reinsert (hij : i ≤ j) (S : Set (Interior i j)) : SimplicialThickening.Path i j where
  I := {i} ∪ {j} ∪ (Subtype.val '' S)
  left := by simp
  right := by simp
  left_le k hk := by
    rcases hk with (h | h) | h
    · subst k; exact le_rfl
    · subst k; exact hij
    · obtain ⟨l, _, rfl⟩ := h
      exact l.property.1.le
  le_right k hk := by
    rcases hk with (h | h) | h
    · subst k; exact hij
    · subst k; exact le_rfl
    · obtain ⟨l, _, rfl⟩ := h
      exact l.property.2.le

/-- The same endpoint reinsertion is a genuine functor on the strict interior subset poset. -/
def reinsertFunctor (hij : i ≤ j) : Set (Interior i j) ⥤ SimplicialThickening.Path i j where
  obj := reinsert hij
  map f := ⟨homOfLE (by
    intro k hk
    rcases hk with h | h
    · exact Or.inl h
    · obtain ⟨l, hl, rfl⟩ := h
      exact Or.inr ⟨l, f.down.down hl, rfl⟩)⟩

/-- Restriction after actual endpoint reinsertion returns every original strict interior subset. -/
theorem restrict_reinsert (hij : i ≤ j) (S : Set (Interior i j)) :
    (restrictPath i j).obj (reinsert hij S) = S := by
  ext k
  constructor
  · intro hk
    rcases hk with (h | h) | h
    · exact False.elim (k.property.1.ne' h)
    · exact False.elim (k.property.2.ne h)
    · obtain ⟨l, hl, h⟩ := h
      have e : l = k := Subtype.ext h
      simpa only [e] using hl
  · intro hk
    exact Or.inr ⟨k, hk, rfl⟩

/-- Reinserted restriction is the whole original coherent path, including both individual
endpoints. -/
theorem reinsert_restrict (hij : i ≤ j) (p : SimplicialThickening.Path i j) :
    reinsert hij ((restrictPath i j).obj p) = p := by
  apply SimplicialThickening.Path.ext
  ext k
  constructor
  · rintro ((h | h) | h)
    · subst k; exact p.left
    · subst k; exact p.right
    · obtain ⟨l, hl, rfl⟩ := h
      exact hl
  · intro hk
    by_cases hki : k = i
    · exact Or.inl (Or.inl hki)
    by_cases hkj : k = j
    · exact Or.inl (Or.inr hkj)
    exact Or.inr ⟨⟨k, lt_of_le_of_ne (p.left_le k hk) (Ne.symm hki),
      lt_of_le_of_ne (p.le_right k hk) hkj⟩, hk, rfl⟩

/-- The restriction and reinsertion functors are actual inverses on the entire original path
category. -/
theorem restrict_reinsert_functor (hij : i ≤ j) :
    restrictPath i j ⋙ reinsertFunctor hij = 𝟭 (SimplicialThickening.Path i j) := by
  refine CategoryTheory.Functor.ext (fun p => reinsert_restrict hij p) ?_
  intro p q f
  exact Subsingleton.elim _ _

/-- The same actual functors are inverses on the strict interior subset category. -/
theorem reinsert_restrict_functor (hij : i ≤ j) :
    reinsertFunctor hij ⋙ restrictPath i j = 𝟭 (Set (Interior i j)) := by
  refine CategoryTheory.Functor.ext (fun S => restrict_reinsert hij S) ?_
  intro p q f
  exact Subsingleton.elim _ _

/-- The entire original coherent Hom nerve is the nerve of its strict interior subset cube. -/
def intervalNerveIso (hij : i ≤ j) :
    nerve (SimplicialThickening.Path i j) ≅ nerve (Set (Interior i j)) where
  hom := nerveMap (restrictPath i j)
  inv := nerveMap (reinsertFunctor hij)
  hom_inv_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro p
    change (p ⋙ restrictPath i j) ⋙ reinsertFunctor hij = p
    refine CategoryTheory.Functor.ext (fun k => reinsert_restrict hij (p.obj k)) ?_
    intro a b f
    exact Subsingleton.elim _ _
  inv_hom_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro p
    change (p ⋙ reinsertFunctor hij) ⋙ restrictPath i j = p
    refine CategoryTheory.Functor.ext (fun k => restrict_reinsert hij (p.obj k)) ?_
    intro a b f
    exact Subsingleton.elim _ _

end CategoryTheory.CoherentRealization.IntervalHom
