/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MarkingCoverage
import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Whole marked arrow comparisons through inherited markings

The supplied original source isomorphism and marked target isomorphism
compare the full underlying arrow square. Mark coverage and monicity
identify the original source marking with the target-inherited marking,
so this square lifts to the same marked arrow isomorphism. No lifting or
weak-class conclusion is included in the input.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- Preserve both original arrow components when an actual monic source covers its whole target marking. -/
def comapArrowIso {X Y T : Marked.{u}} {A : SSet.{u}} (f : X ⟶ Y) [Mono f]
    (hf : MarkingSurjective f) (g : A ⟶ T.toSSet)
    (s : X.toSSet ≅ A) (t : Y ≅ T)
    (hsq : s.hom ≫ g = f.hom ≫ t.hom.hom) :
    Arrow.mk f ≅ Arrow.mk (comapHom T g) := by
  let e : X ≅ comap T g := isoMk s (fun a => by
    change a ∈ X.marking ↔ g.app (op ⦋1⦌) (s.hom.app (op ⦋1⦌) a) ∈ T.marking
    have h : g.app (op ⦋1⦌) (s.hom.app (op ⦋1⦌) a) =
        t.hom.hom.app (op ⦋1⦌) (f.hom.app (op ⦋1⦌) a) :=
      ConcreteCategory.congr_hom (congr_app hsq (op ⦋1⦌)) a
    rw [h]
    constructor
    · intro ha
      exact t.hom.preserve (f.preserve ha)
    · intro ha
      exact hf.reflect a ((mem_marking_iff_of_iso t _).mpr ha))
  exact Arrow.isoMk e t (Hom.ext hsq)

/-- The source of the whole marked arrow isomorphism retains the supplied original simplicial map. -/
@[simp]
theorem comapArrowIso_hom_left {X Y T : Marked.{u}} {A : SSet.{u}} (f : X ⟶ Y) [Mono f]
    (hf : MarkingSurjective f) (g : A ⟶ T.toSSet) (s : X.toSSet ≅ A) (t : Y ≅ T)
    (hsq : s.hom ≫ g = f.hom ≫ t.hom.hom) :
    (comapArrowIso f hf g s t hsq).hom.left.hom = s.hom := rfl

/-- The target of the whole marked arrow comparison is precisely the supplied original marked isomorphism. -/
@[simp]
theorem comapArrowIso_hom_right {X Y T : Marked.{u}} {A : SSet.{u}} (f : X ⟶ Y) [Mono f]
    (hf : MarkingSurjective f) (g : A ⟶ T.toSSet) (s : X.toSSet ≅ A) (t : Y ≅ T)
    (hsq : s.hom ≫ g = f.hom ≫ t.hom.hom) :
    (comapArrowIso f hf g s t hsq).hom.right = t.hom := rfl

end SSet.Marked
