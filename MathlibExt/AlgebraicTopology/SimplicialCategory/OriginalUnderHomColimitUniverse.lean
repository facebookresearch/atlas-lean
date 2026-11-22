/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalUnderHomColimitReadback
import Mathlib.CategoryTheory.EssentiallySmall

/-!
# The SAME original Hom colimit at independent small diagram universes

A genuine indexing equivalence resizes only the diagram presentation.
Every actual original object, full Hom, map and cocone remains unchanged.
The genuine final-equivalence universal property returns the result for
the SAME original mapped cocone at its original independent universes.
-/

noncomputable section
universe u v w
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.OriginalUnderHomColimit

/-- Full original under-root Hom evaluation retains genuine filtered colimits at independent small diagram universes. -/
def originalIsColimitUnivLE {C : Carrier.{u}} {J : Type v} [Category.{w} J]
    [IsFiltered J] [UnivLE.{v, u}] [UnivLE.{w, u}]
    (U : J ⥤ Under C) (s : Cocone U) (hs : IsColimit s) (x y : C)
    (h : ∀ {i j : J} (f : i ⟶ j), Function.Injective (U.map f).right.obj) :
    IsColimit ((OriginalUnderHom.functor C x y).mapCocone s) := by
  let e := ((ShrinkHoms.equivalence.{u} J).trans (Shrink.equivalence _)).symm
  let _ := IsFiltered.of_equivalence e.symm
  have ht := originalIsColimit (e.functor ⋙ U) (s.whisker e.functor)
    (hs.whiskerEquivalence e) x y (fun f => h (e.functor.map f))
  exact (Functor.Final.isColimitWhiskerEquiv e.functor
    ((OriginalUnderHom.functor C x y).mapCocone s)) ht

end CategoryTheory.SimplicialEnrichment.OriginalUnderHomColimit
