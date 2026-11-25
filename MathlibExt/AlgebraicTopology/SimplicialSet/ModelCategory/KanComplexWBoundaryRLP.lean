/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.WFibrationBoundaryLifting

/-!
# Boundary lifting for weak-equivalence Kan fibrations

A simplicial Kan fibration in `SSet.KanComplex.W` has the right lifting property with respect to
every boundary inclusion. This file only aggregates the fixed-top lifting theorem over the
generating boundary inclusions; it does not construct a model-category or weak-equivalence
instance.
-/

@[expose] public section

open CategoryTheory HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace SSet.modelCategoryQuillen

/-- A Kan fibration which is a `KanComplex.W` equivalence has the right lifting property with
respect to every boundary inclusion. -/
theorem J_rlp_inf_W_le_I_rlp :
    J.{u}.rlp ⊓ SSet.KanComplex.W.{u} ≤ I.{u}.rlp := by
  rintro X Y f ⟨hfJ, hfW⟩
  let _ : SSet.KanComplex X := hfW.kanComplex_source
  let _ : SSet.KanComplex Y := hfW.kanComplex_target
  let _ : Fibration f := (fibration_iff f).2 hfJ
  rintro _ _ _ ⟨n⟩
  exact ⟨fun _ => hfW.hasLiftingPropertyFixedTop _ _ _⟩

end SSet.modelCategoryQuillen
