/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryFactorization
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CategoricalFibrations
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.HoPreNatIso
public import MathlibExt.CategoryTheory.MorphismProperty.WeakFactorizationSystem

/-!
# Genuine trivial categorical fibrations

The genuine categorical fibrations which are weak categorical equivalences
are exactly the maps with boundary RLP. The proof uses the boundary weak
factorization system and the general one-WFS right-class identity, before
any choice of a Joyal model structure.
-/

@[expose] public section

universe u

open CategoryTheory MorphismProperty

namespace SSet

/-- The intersection of genuine categorical fibrations and categorical
equivalences is the boundary right lifting class, for arbitrary simplicial
sets in the value universe. -/
theorem categoricalFibrations_inf_categoricalEquivalences :
    categoricalFibrations.{u} ⊓ categoricalEquivalences = modelCategoryQuillen.I.rlp := by
  have hRW : (monomorphisms SSet.{u}).rlp ≤ categoricalEquivalences := by
    rw [rlp_monomorphisms]
    exact modelCategoryQuillen_I_rlp_le_categoricalEquivalences
  have : categoricalEquivalences.HasOfPostcompProperty (monomorphisms SSet.{u}).rlp :=
    HasOfPostcompProperty.of_le categoricalEquivalences categoricalEquivalences hRW
  change (monomorphisms SSet.{u} ⊓ categoricalEquivalences).rlp ⊓
    categoricalEquivalences = modelCategoryQuillen.I.rlp
  rw [← rlp_monomorphisms]
  exact IsWeakFactorizationSystem.rlp_inf_inf_eq (monomorphisms SSet.{u})
    (monomorphisms SSet.{u}).rlp categoricalEquivalences
    isWeakFactorizationSystem_monomorphisms hRW

/-- A map is both a genuine categorical fibration and a categorical
equivalence exactly when it has boundary RLP. -/
theorem categoricalFibrations_and_categoricalEquivalences_iff {X Y : SSet.{u}}
    (p : X ⟶ Y) :
    categoricalFibrations p ∧ categoricalEquivalences p ↔ modelCategoryQuillen.I.rlp p := by
  change (categoricalFibrations ⊓ categoricalEquivalences) p ↔ modelCategoryQuillen.I.rlp p
  rw [categoricalFibrations_inf_categoricalEquivalences]

end SSet
