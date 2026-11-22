/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.OppositeTrivialFibrations
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure
public import MathlibExt.AlgebraicTopology.ModelCategory.FibrantBrown

/-!
# Original simplicial opposite preserves weak maps between Kan complexes

The genuine full boundary RLP is preserved by the actual opposite functor.
Brown's lemma in the proved Kan–Quillen model therefore preserves weak
maps between Kan objects. The original double-opposite natural isomorphism
gives the converse, retaining the same entire original map.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SSet.modelCategoryQuillen

attribute [local instance] modelCategory

/-- The actual opposite functor preserves genuine whole Kan–Quillen trivial fibrations. -/
theorem op_map_trivialFibration {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : trivialFibrations SSet.{u} p) :
    trivialFibrations SSet.{u} (opFunctor.map p) := by
  have hI : I.rlp p := by
    rw [← cofibrations_rlp] at hp
    change (MorphismProperty.monomorphisms SSet.{u}).rlp p at hp
    rwa [rlp_monomorphisms] at hp
  rw [← cofibrations_rlp]
  change (MorphismProperty.monomorphisms SSet.{u}).rlp (opFunctor.map p)
  rw [rlp_monomorphisms]
  exact op_map_mem_I_rlp p hI

/-- Opposite preserves weakness of the same original map between genuine Kan complexes. -/
theorem op_map_weak {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    {f : X ⟶ Y} (hf : realizationWeakEquivalences f) :
    realizationWeakEquivalences (opFunctor.map f) := by
  let _ : IsFibrant X := inferInstance
  let _ : IsFibrant Y := inferInstance
  let _ : WeakEquivalence f := (weakEquivalence_iff f).mpr hf
  change weakEquivalences SSet.{u} (opFunctor.map f)
  exact opFunctor.map_mem_of_weakEquivalence_of_fibrant (weakEquivalences SSet.{u})
    (MorphismProperty.isomorphisms_le_of_containsIdentities (weakEquivalences SSet.{u}))
    (by
      intro A B p _ _ hp
      exact (op_map_trivialFibration p hp).2) f

/-- The actual original opposite map is weak exactly when the same original Kan-complex map is weak. -/
theorem op_map_weak_iff {X Y : SSet.{u}} [KanComplex X] [KanComplex Y] (f : X ⟶ Y) :
    realizationWeakEquivalences (opFunctor.map f) ↔ realizationWeakEquivalences f := by
  constructor
  · intro h
    have hh := op_map_weak h
    have e : Arrow.mk (opFunctor.map (opFunctor.map f)) ≅ Arrow.mk f :=
      Arrow.isoMk (opFunctorCompOpFunctorIso.app X) (opFunctorCompOpFunctorIso.app Y)
        (opFunctorCompOpFunctorIso.hom.naturality f).symm
    exact (realizationWeakEquivalences.arrow_mk_iso_iff e).mp hh
  · exact op_map_weak

end SSet.modelCategoryQuillen
