/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ColimitMarking
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Category.ULift

/-!
# Exact original markings of an actual marked pushout

A marked edge in the native pushout comes from a marked edge on one of
its two original sides. Central source edges already map to those sides.
This keeps the original pushout maps and full edge data, with no fibrancy
or model premise.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- Native marked pushout edges are exactly images of original marked side edges. -/
theorem mem_marking_of_isPushout_iff {A X Y P : Marked.{u}}
    {f : A ⟶ X} {g : A ⟶ Y} {i : X ⟶ P} {j : Y ⟶ P}
    (h : IsPushout f g i j) (e : P.toSSet _⦋1⦌) :
    e ∈ P.marking ↔
      (∃ x : X.toSSet _⦋1⦌, x ∈ X.marking ∧ i.hom.app (op ⦋1⦌) x = e) ∨
      (∃ y : Y.toSSet _⦋1⦌, y ∈ Y.marking ∧ j.hom.app (op ⦋1⦌) y = e) := by
  constructor
  · intro he
    let q : AsSmall.{u} WalkingSpan ≌ WalkingSpan := AsSmall.equiv.symm
    let c := h.cocone.whisker q.functor
    have hc : IsColimit c := h.isColimit.whiskerEquivalence q
    obtain ⟨s, a, ha, he⟩ := (mem_marking_of_isColimit_iff hc e).mp he
    cases s with
    | up s =>
      cases s with
      | none =>
          left
          refine ⟨f.hom.app (op ⦋1⦌) a, f.preserve ha, ?_⟩
          exact he
      | some s =>
          cases s with
          | left => exact Or.inl ⟨a, ha, he⟩
          | right => exact Or.inr ⟨a, ha, he⟩
  · rintro (⟨x, hx, h⟩ | ⟨y, hy, h⟩)
    · exact h ▸ i.preserve hx
    · exact h ▸ j.preserve hy

end SSet.Marked
