/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.Quasicategory.CoreTrivialFibration
public import MathlibExt.AlgebraicTopology.Quasicategory.SpecialOuterHornGeneral
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexBoundaryRLPRecognition

/-!
# The Kan interpretation of cores of trivial fibrations

For a map with right lifting against all monomorphisms and quasicategory
codomain, its source is a quasicategory by inner lifting. The core map is a
Kan fibration and a Kan weak equivalence; the weak-equivalence predicate also
asserts that both literal endpoint cores are Kan complexes.

This is the core trivial-fibration step in the proof of Cisinski's Theorem
3.6.8, *Higher Categories and Homotopical Algebra*.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MorphismProperty
open scoped SSet.modelCategoryQuillen

namespace SSet

/-- With quasicategory codomain, the core of an all-monomorphism-RLP map
is a Kan fibration and Kan weak equivalence. Both endpoint Kan assertions
are contained in `KanComplex.W`. -/
theorem core_map_mem_J_rlp_inf_W_of_rlp_monomorphisms
    {X Y : SSet.{u}} {p : X ⟶ Y} [Quasicategory Y]
    (hp : (monomorphisms SSet.{u}).rlp p) :
    (modelCategoryQuillen.J.rlp ⊓ KanComplex.W) (core.map p) := by
  let _ : InnerFibration p :=
    ⟨antitone_rlp innerHornInclusions_le_monomorphisms _ hp⟩
  let _ : Quasicategory X := quasicategory_of_innerFibration p
  let _ : KanComplex (core X : SSet.{u}) := inferInstance
  let _ : KanComplex (core Y : SSet.{u}) := inferInstance
  have hc := core_map_mem_rlp_monomorphisms hp
  refine ⟨antitone_rlp modelCategoryQuillen.J_le_monomorphisms _ hc, ?_⟩
  apply KanComplex.W.of_rlp_I
  rwa [← rlp_monomorphisms]

end SSet
