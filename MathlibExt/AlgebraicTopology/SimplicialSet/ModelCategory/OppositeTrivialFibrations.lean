/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.HoFunctorTrivialFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.Op
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-!
# Genuine boundary RLP under the original simplicial opposite

The actual simplicial opposite is a self-adjoint equivalence. It preserves
monomorphisms, so its genuine adjunction lifting correspondence preserves
the full boundary right lifting class. This transports actual trivial
fibrations, not only fibrancy or a condition on their vertex components.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory

namespace SSet.modelCategoryQuillen

/-- The original simplicial opposite preserves the full genuine boundary RLP of the same original map. -/
theorem op_map_mem_I_rlp {X Y : SSet.{u}} (p : X ⟶ Y) (hp : I.rlp p) :
    I.rlp (opFunctor.map p) := by
  rw [← rlp_monomorphisms]
  intro A B i hi
  let _ : Mono i := hi
  let _ : opFunctor.{u}.IsRightAdjoint := opEquivalence.toAdjunction.isRightAdjoint
  let _ : Mono (opFunctor.map i) := inferInstance
  have hL : HasLiftingProperty (opFunctor.map i) p :=
    (rlp_monomorphisms_of_rlp_I hp) (opFunctor.map i)
      (MorphismProperty.monomorphisms.infer_property (opFunctor.map i))
  exact (opEquivalence.toAdjunction.hasLiftingProperty_iff i p).mp hL

end SSet.modelCategoryQuillen
