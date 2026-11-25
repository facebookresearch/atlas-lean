/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Embedding.StupidTrunc

/-!
# Inverse naturality for stupid-truncation components

The inverse component isomorphisms of stupid truncation commute with
chain maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w₁ w₂ v u

namespace HomologicalComplex

variable {I : Type w₁} {J : Type w₂}
variable {c : ComplexShape I} {d : ComplexShape J}
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C]
variable {K L : HomologicalComplex C d} (e : c.Embedding d)
  [e.IsRelIff]

/-- Inverse naturality for the component isomorphisms of stupid
truncation. -/
@[reassoc (attr := simp)]
lemma stupidTruncXIso_inv_naturality (f : K ⟶ L)
    {i : I} {j : J} (h : e.f i = j) :
    f.f j ≫ (L.stupidTruncXIso e h).inv =
      (K.stupidTruncXIso e h).inv ≫ (stupidTruncMap f e).f j := by
  rw [Iso.comp_inv_eq, Category.assoc,
    stupidTruncMap_stupidTruncXIso_hom, Iso.inv_hom_id_assoc]

end HomologicalComplex
