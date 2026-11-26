/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerFreeObjects

/-!
# Two-label consumers of the free-object adjunction

The unit sends each Boolean label to its own coproduct vertex. The counit
on the two-object codiscrete enrichment returns each supplied Boolean object,
and the free-object construction keeps the two labels distinct.
-/

noncomputable section

open CategoryTheory CategoryTheory.SimplicialEnrichment
open BergnerFreeObjects

namespace MathlibExtTest.AlgebraicTopology.SimplicialCategory.BergnerFreeObjectsTest

example (b : Bool) :
    ((adjunction.{0}).unit.app Bool).hom b = vertex Bool b := by
  rw [unit_app]
  rfl

example (b : Bool) :
    ((adjunction.{0}).counit.app (CodiscreteEnrichment.object Bool)).obj
      (vertex (CodiscreteEnrichment.object Bool : Type) b) = b := by
  rw [counit_app]
  exact desc_vertex (CodiscreteEnrichment.object Bool : Type)
    (C := CodiscreteEnrichment.object Bool) id b

example : vertex Bool false ≠ vertex Bool true := by
  intro h
  have e := congrArg
    (fun x : object Bool =>
      (desc Bool (C := CodiscreteEnrichment.object Bool) id).obj x) h
  have h₀ := desc_vertex Bool (C := CodiscreteEnrichment.object Bool) id false
  have h₁ := desc_vertex Bool (C := CodiscreteEnrichment.object Bool) id true
  have e' : (false : Bool) = true := h₀.symm.trans (e.trans h₁)
  exact Bool.noConfusion e'

end MathlibExtTest.AlgebraicTopology.SimplicialCategory.BergnerFreeObjectsTest
