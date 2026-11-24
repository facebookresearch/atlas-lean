/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftRealizationWeak
public import MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftStandardIso
public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveLiftRealization
public import MathlibExt.CategoryTheory.NerveCrossUniverse
public import Mathlib.CategoryTheory.Category.ULift

/-!
# Original point-map weakness under the canonical object-lifted nerve

The existing `SSet.nerveULiftIso` keeps every original object and arrow
inside the actual category universe lift. Its inverse identifies the
original point maps, so their weakness is preserved and reflected.
-/

@[expose] public section


noncomputable section

universe u v w

open CategoryTheory Opposite
open scoped Simplicial

attribute [local instance] CategoryTheory.uliftCategory

namespace CategoryTheory

/-- The SAME original terminal point property is preserved and reflected by the canonical
full category object lift. -/
theorem nerveULiftObject_point_weak_iff (C : Type u) [Category.{v} C] :
    SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from (nerve (ULift.{w} C))) ↔
      SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from (nerve C)) := by
  let e := (SSet.nerveULiftIso.{u,v,w} C).symm
  let p := SSet.stdSimplex.isTerminalObj₀.from (nerve C)
  let q := SSet.stdSimplex.isTerminalObj₀.from (nerve (ULift.{w} C))
  let d := SSet.uliftStandardSimplexIso.{max u v,w} ⦋0⦌
  have he : e.hom ≫ q = SSet.uliftFunctor.map p ≫ d.hom :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  constructor
  · intro hq
    have hc := SSet.realizationWeakEquivalences.comp_mem e.hom q
      (SSet.realizationWeakEquivalences.of_isIso _) hq
    have hL := (SSet.realizationWeakEquivalences.cancel_right_of_respectsIso
      (SSet.uliftFunctor.map p) d.hom).mp (he ▸ hc)
    exact (SSet.realizationWeak_ulift_map_iff p).mp hL
  · intro hp
    have hL := (SSet.realizationWeak_ulift_map_iff p).mpr hp
    have hc := SSet.realizationWeakEquivalences.comp_mem (SSet.uliftFunctor.map p) d.hom hL
      (SSet.realizationWeakEquivalences.of_isIso _)
    exact (SSet.realizationWeakEquivalences.cancel_left_of_respectsIso e.hom q).mp (he.symm ▸ hc)

end CategoryTheory
