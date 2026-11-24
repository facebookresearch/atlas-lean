/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OrderedJFSRawFamilies

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial
open SimplicialPresheaf.OrderedJFS

example : IsEmpty (FullGenerator 0) := inferInstance
example : IsEmpty (Generator 0) := inferInstance
example : IsEmpty (ConstancyIndex 1) := inferInstance
example (n : ℕ) : Small.{u} (FullGenerator n) := inferInstance
example (n : ℕ) : Small.{u} (Generator n) := inferInstance

-- The source's full arity-one member is the original spine Arrow, not a definition by id.
private def unaryFullSegal : FullSegalIndex 1 := ⟨0, 1, by decide, fun _ => 0⟩

example : fullSegalComponents.{u} unaryFullSegal 0 =
    Arrow.mk (SSet.Rezk.segalMap 1) := fullSegal_selected unaryFullSegal

-- Arbitrary other coordinates survive the selected finite-K construction.
example (n : ℕ) (c : CompletenessIndex n) (j : Fin n) (h : j ≠ c.coord) :
    completenessComponents.{u} c j =
      Arrow.mk (𝟙 (SSet.Rezk.representable (c.otherIndex ⟨j, h⟩))) :=
  completeness_other c j h

-- At height two the ordered generator is idF(0) × collapse(1).
private def twoConstancy : FullConstancyIndex 2 where
  coord := 0
  earlierIndex j := False.elim ((Nat.not_lt_zero _) j.property)
  laterIndex _ := 1

example : fullConstancyComponents.{u} twoConstancy 0 =
    Arrow.mk (𝟙 (SSet.Rezk.representable 0)) := fullConstancy_selected twoConstancy

example : fullConstancyComponents.{u} twoConstancy 1 =
    Arrow.mk (SSet.Rezk.FiniteCompleteness.representableCollapse 1) :=
  fullConstancy_later twoConstancy 1 (by decide)

-- The normalized value is the literal original full Arrow at the forgotten label.
example (n : ℕ) (g : Generator n) :
    originalFamily.{u} n g = fullOriginalFamily n (normalizedToFull g) :=
  originalFamily_toFull n g

-- Both genuine whole-Arrow transport directions retain the SAME original maps.
example (n : ℕ) (g : FullGenerator n) :
    let E := FinitePowerSite.diagramEquiv n SSet.{u}
    let e := (Functor.mapArrowEquivalence E).counitIso.app (fullMultiFamily g)
    e.hom.left ≫ (fullMultiFamily g).hom =
        E.functor.map (fullOriginalFamily n g).hom ≫ e.hom.right ∧
      e.inv.left ≫ E.functor.map (fullOriginalFamily n g).hom =
        (fullMultiFamily g).hom ≫ e.inv.right := fullTransportCounit n g
