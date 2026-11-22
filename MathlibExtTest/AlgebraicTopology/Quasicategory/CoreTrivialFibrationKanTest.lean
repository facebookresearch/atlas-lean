/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.Quasicategory.CoreTrivialFibrationKan
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure

/-!
# Cores of trivial fibrations in the actual native Kan model
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MorphismProperty HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SSet

/-- A quasicategory codomain and all-monomorphism RLP give both core Kan
structures and a trivial fibration in the actual native Kan model. -/
example {X Y : SSet.{u}} {p : X ⟶ Y} [Quasicategory Y]
    (hp : (monomorphisms SSet.{u}).rlp p) :
    KanComplex (core X : SSet.{u}) ∧ KanComplex (core Y : SSet.{u}) ∧
      trivialFibrations SSet.{u} (core.map p) := by
  have hc := core_map_mem_J_rlp_inf_W_of_rlp_monomorphisms hp
  let _ : KanComplex (core X : SSet.{u}) := hc.2.kanComplex_source
  let _ : KanComplex (core Y : SSet.{u}) := hc.2.kanComplex_target
  refine ⟨inferInstance, inferInstance, ?_⟩
  change modelCategoryQuillen.J.rlp (core.map p) ∧
    realizationWeakEquivalences (core.map p)
  exact ⟨hc.1, (KanComplex.W_iff_realizationWeakEquivalence (core.map p)).mp hc.2⟩

/-- The boundary-RLP input used by native model dictionaries has the
same quasicategory-codomain consequence. -/
example {X Y : SSet.{u}} {p : X ⟶ Y} [Quasicategory Y]
    (hp : modelCategoryQuillen.I.rlp p) : KanComplex.W (core.map p) := by
  have hpMono : (monomorphisms SSet.{u}).rlp p := by
    rwa [rlp_monomorphisms]
  exact (core_map_mem_J_rlp_inf_W_of_rlp_monomorphisms hpMono).2

end SSet
