/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.NerveCrossUniverse
public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveEquivalenceWeakEquivalence

/-!
# Genuine nerve weakness with independent Hom universes

The SAME canonical native chain maps of an actual categorical
equivalence give realization weak equivalences without changing either
original category's Hom types. Both full inverse maps and the original
natural unit and counit are retained in a common ambient object universe.
-/

@[expose] public section

noncomputable section

universe w v₁ v₂

open CategoryTheory Opposite

namespace CategoryTheory

/-- The SAME native equivalence map on nerves is genuinely weak with independent original
Hom universes. -/
theorem nerveMapHomDown_mem_realizationWeakEquivalences_of_isEquivalence
    {C D : Type (max w v₁ v₂)} [Category.{v₁} C] [Category.{v₂} D]
    (F : C ⥤ D) [F.IsEquivalence] :
    SSet.realizationWeakEquivalences (nerveMapHomDown.{w, v₁, v₂} F) := by
  let E := F.asEquivalence
  have hleft : SSet.Homotopy
      (nerveMapHomDown.{w, v₁, v₂} E.functor ≫ nerveMapHomDown.{w, v₂, v₁} E.inverse)
      (𝟙 (nerve C)) := by
    have hcomp : nerveMapHomDown.{w, v₁, v₂} E.functor ≫ nerveMapHomDown.{w, v₂, v₁} E.inverse =
        nerveMapHomDown.{max w v₂, v₁, v₁} (E.functor ⋙ E.inverse) := by
      ext d X
      rfl
    rw [hcomp]
    simpa only [nerveMapHomDown_id] using
      NatTrans.nerveHomotopyHomDown.{max w v₂, v₁, v₁} E.unitInv
  have hright : SSet.Homotopy
      (nerveMapHomDown.{w, v₂, v₁} E.inverse ≫ nerveMapHomDown.{w, v₁, v₂} E.functor)
      (𝟙 (nerve D)) := by
    have hcomp : nerveMapHomDown.{w, v₂, v₁} E.inverse ≫ nerveMapHomDown.{w, v₁, v₂} E.functor =
        nerveMapHomDown.{max w v₁, v₂, v₂} (E.inverse ⋙ E.functor) := by
      ext d X
      rfl
    rw [hcomp]
    simpa only [nerveMapHomDown_id] using
      NatTrans.nerveHomotopyHomDown.{max w v₁, v₂, v₂} E.counit
  let e := SSet.realizedHomotopyEquiv (nerve C) (nerve D)
    (nerveMapHomDown.{w, v₁, v₂} E.functor) (nerveMapHomDown.{w, v₂, v₁} E.inverse) hleft hright
  change TopCat.weakHomotopyEquivalences (SSet.toTop.map (nerveMapHomDown.{w, v₁, v₂} E.functor))
  exact TopCat.mem_of_eq_toFun e rfl

end CategoryTheory
