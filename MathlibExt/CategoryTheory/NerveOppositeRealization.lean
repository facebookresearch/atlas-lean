/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ToTopReversal
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalence
public import MathlibExt.CategoryTheory.NerveOppositeNaturality

/-!
# Realization weak equivalences of the original nerve and its opposite

The existing natural nerve-opposite comparison and realization reversal
preserve the same original nerve-map predicate. This neutral module is
shared by right-comma Quillen A and the two-sided Grothendieck comparison.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
open CategoryTheory

namespace SSet.OppositeRealization

/-- The existing natural nerve-opposite comparison preserves the actual nerve-map predicate. -/
theorem nerveMap_op_mem_iff {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D) :
    SSet.realizationWeakEquivalences (nerveMap F.op) ↔
      SSet.realizationWeakEquivalences (nerveMap F) := by
  let e : Arrow.mk (nerveMap F.op) ≅
      Arrow.mk (SimplicialObject.opFunctor.map (nerveMap F)) :=
    Arrow.isoMk (nerveOppositeSimplicialIso C) (nerveOppositeSimplicialIso D)
      (nerveOppositeSimplicialIso_naturality F)
  exact (SSet.realizationWeakEquivalences.arrow_mk_iso_iff e).trans
    (realizationWeakEquivalences_op_map_iff (nerveMap F))

end SSet.OppositeRealization
