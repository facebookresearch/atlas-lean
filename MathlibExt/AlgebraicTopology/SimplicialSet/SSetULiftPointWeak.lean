/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftRealizationWeak
public import MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftStandardIso

/-!
# The same original point-map weakness under coefficient universe lift

The actual universe lift preserves and reflects every original weak
map. Its full standard-point isomorphism identifies the unique point
maps at both original coefficient universes.
-/

@[expose] public section


noncomputable section

universe u v

open CategoryTheory
open scoped Simplicial

namespace SSet

/-- The same original point-map weak property is preserved and reflected by the actual coefficient universe lift. -/
theorem realizationWeak_ulift_point_iff (X : SSet.{u}) :
    realizationWeakEquivalences (stdSimplex.isTerminalObj₀.from (uliftFunctor.{v,u}.obj X)) ↔
      realizationWeakEquivalences (stdSimplex.isTerminalObj₀.from X) := by
  let p := stdSimplex.isTerminalObj₀.from X
  let e := uliftStandardSimplexIso.{u,v} ⦋0⦌
  have he : uliftFunctor.map p ≫ e.hom =
      stdSimplex.isTerminalObj₀.from (uliftFunctor.{v,u}.obj X) := stdSimplex.isTerminalObj₀.hom_ext _ _
  have h := (realizationWeakEquivalences.cancel_right_of_respectsIso (uliftFunctor.map p) e.hom).trans
    (realizationWeak_ulift_map_iff p)
  exact he ▸ h

end SSet
