/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontCollapse

/-!
# The SAME original zero-dimensional fixed-front quotient is the walking arrow

The original front of Δ[1] consists of the single original source
vertex in every scalar degree. Its original quotient relation is
therefore equality. Both full inverse maps retain the actual original
projection, every simplex and all scalar operators.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFixedFrontContraction

open FixedFrontCollapse

/-- Every original zero-front pair has its SAME original simplex equality. -/
theorem zero_front_eq {q : SimplexCategoryᵒᵖ} (a b : (Δ[1] : SSet.{u}).obj q)
    (ha : InFront (n := 0) a) (hb : InFront (n := 0) b) : a = b := by
  apply SSet.stdSimplex.ext
  intro i
  have ha' := ha i
  have hb' := hb i
  apply Fin.ext
  change (a.down.toOrderHom i).val = (b.down.toOrderHom i).val
  have hai := (a.down.toOrderHom i).isLt
  have hbi := (b.down.toOrderHom i).isLt
  change (a.down.toOrderHom i).val < 2 at hai
  change (b.down.toOrderHom i).val < 2 at hbi
  have hax : (a.down.toOrderHom i).val ≠ 1 := fun h => ha' (Fin.ext h)
  have hbx : (b.down.toOrderHom i).val ≠ 1 := fun h => hb' (Fin.ext h)
  omega

/-- The actual whole original inverse from the zero-front quotient retains every original
simplex. -/
def zeroObjectInverse : FixedFrontCollapse.object.{u} 0 ⟶ (Δ[1] : SSet.{u}) where
  app q := ↾_root_.Quotient.lift id (by
    rintro a b (h | hab)
    · exact h
    · exact zero_front_eq a b hab.1 hab.2)
  naturality _q _r _θ := by
    apply ConcreteCategory.hom_ext
    intro p
    induction p using _root_.Quotient.inductionOn' with
    | h a => rfl

/-- Both inverse maps identify the SAME original zero-front quotient with the original
walking arrow. -/
def zeroObjectIso : FixedFrontCollapse.object.{u} 0 ≅ (Δ[1] : SSet.{u}) where
  hom := zeroObjectInverse
  inv := projection 0
  hom_inv_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro p
    induction p using _root_.Quotient.inductionOn' with
    | h a => rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro a
    rfl

/-- The SAME zero-front inverse is literally the original complete quotient projection. -/
theorem zeroObjectIso_inv : zeroObjectIso.{u}.inv = projection.{u} 0 := rfl

end CategoryTheory.CoherentRealization.OriginalFixedFrontContraction
