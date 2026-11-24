/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The quotient universal property of general cofiber sequences

The quotient map of a cofiber sequence is an epimorphism. If `C` also has
zero morphisms, the supplied cofiber pushout produces a colimit witness for
the cofork of its particular quotient map. Conversely, a cofibration
`f : X ⟶ Y`, a map `g : Y ⟶ Z`, a proof `w : f ≫ g = 0`, and
a colimit witness for `CokernelCofork.ofπ g w` give the cofiber pushout.
Existence of some unrelated cokernel is not the reverse hypothesis.
No additive or exact-category structure is used.
-/

public section

open CategoryTheory Limits
open scoped ZeroObject

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The quotient map of an actual cofiber row is an epimorphism, by the
original pushout universal property and zero-object uniqueness. -/
theorem IsCofiberSequence.epi {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hSeq : IsCofiberSequence f g) : Epi g := by
  obtain ⟨_, z, u, hPushout⟩ := hSeq
  constructor
  intro W a b h
  apply hPushout.hom_ext
  · exact (isZero_zero C).eq_of_src _ _
  · exact h

section ZeroMorphisms

variable [HasZeroMorphisms C]

/-- Let `C` have zero morphisms, a zero object, and a Waldhausen structure
without gluing. If `(f : X ⟶ Y, g : Y ⟶ Z)` is a cofiber sequence, its
quotient map `g` gives a colimit witness for the specified cokernel cofork
`CokernelCofork.ofπ g hSeq.comp_eq_zero`. This uses the supplied maps and
their zero composite, not a separately chosen cokernel object. -/
noncomputable def isColimitCokernelCoforkOfCofiberSequence
    {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hSeq : IsCofiberSequence f g) :
    IsColimit (CokernelCofork.ofπ g hSeq.comp_eq_zero) :=
  Classical.choice <| by
    obtain ⟨_, z, u, hPushout⟩ := hSeq
    refine ⟨CokernelCofork.IsColimit.ofπ g _
      (fun {W} k hk => hPushout.desc (0 : (0 : C) ⟶ W) k (by
        simp only [comp_zero, hk])) ?_ ?_⟩
    · intro W k hk
      exact hPushout.inr_desc _ _ _
    · intro W k hk m hm
      apply hPushout.hom_ext
      · exact (isZero_zero C).eq_of_src _ _
      · exact hm.trans (hPushout.inr_desc _ _ _).symm

/-- Let `C` have zero morphisms, a zero object, and a Waldhausen structure
without gluing. For a cofibration `f : X ⟶ Y` and a supplied map
`g : Y ⟶ Z`, assume `w : f ≫ g = 0` and a colimit witness
`hg : IsColimit (CokernelCofork.ofπ g w)` for this particular cofork.
Then `(f, g)` is a cofiber sequence through the selected zero object.
Existence of some other cokernel, without a witness for `g`, is not the
hypothesis. -/
theorem isCofiberSequenceOfCofibrationAndCokernel
    {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsCofibration f) (w : f ≫ g = 0)
    (hg : IsColimit (CokernelCofork.ofπ g w)) :
    IsCofiberSequence f g := by
  refine ⟨hf, (0 : X ⟶ (0 : C)), (0 : (0 : C) ⟶ Z), ?_⟩
  refine IsPushout.mk' ?_ ?_ ?_
  · simp only [zero_comp, w]
  · intro W a b _ hquotient
    exact Cofork.IsColimit.hom_ext hg hquotient
  · intro W a b hab
    have hb : f ≫ b = 0 := by
      simpa only [zero_comp] using hab.symm
    let d : Z ⟶ W := hg.desc (CokernelCofork.ofπ b hb)
    refine ⟨d, ?_, ?_⟩
    · exact (isZero_zero C).eq_of_src _ _
    · exact Cofork.IsColimit.π_desc hg

end ZeroMorphisms

end CategoryTheory
