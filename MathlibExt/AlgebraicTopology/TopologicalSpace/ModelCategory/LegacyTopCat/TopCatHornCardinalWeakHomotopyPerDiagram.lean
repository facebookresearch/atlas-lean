/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexW
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHornSequentialSmallObject
public import
  MathlibExt.Topology.Category.TopCat.Embedding.TopCatHornCoproductClosedT1
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHornCoproductPushoutProperty
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyTransfiniteClosed
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyEquivalence

/-!
# Actual-cardinal and sequential horn closure using per-diagram singular preservation

This file is part of the KQ3 layer, at exact base
`0ac4b23289d86403f3cd7e195e6533b2eb53e5b5`.

It combines `horn_rlp_llp_eq_cardinalOrd` or `horn_rlp_llp_eq_sequential`,
horn-coproduct closed-`T1` inclusion, and
`TopCat.weakHomotopyEquivalences.of_transfiniteComposition_closedT1`
to prove `realizedHornInclusions.rlp.llp ≤ weakHomotopyEquivalences` without any
global `PreservesColimitsOfShape` premise, delegating per-diagram preservation
and well-order continuity to the provider.

Remaining premise (either route suffices): `SSet.KanComplex.W` transfinite
stability for the actual cardinal ordinal or the sequential (`ℕ`) shape.
No global preservation, no model structure, no KQ4 content.
-/

@[expose] public section

open CategoryTheory Limits MorphismProperty

universe u

namespace TopCat

/-- Horn left-class maps are weak equivalences, conditional only on `W`
stability for the actual cardinal ordinal. -/
theorem horn_llp_le_weakHomotopyEquivalences_of_cardinalOrd_perDiagram
    [(SSet.KanComplex.W :
      MorphismProperty SSet.{u}).IsStableUnderTransfiniteCompositionOfShape
      realizedGeneratorCardinal.{u}.ord.ToType] :
    realizedHornInclusions.{u}.rlp.llp ≤
      weakHomotopyEquivalences.{u} := by
  rw [horn_rlp_llp_eq_cardinalOrd]
  refine retracts_le_iff.mpr ?_
  intro X Y f hf
  obtain ⟨hT⟩ := hf
  have hW0 := hT.ofLE (le_inf coproducts_pushouts_le_weakHomotopyEquivalences
    pushouts_coproducts_realizedHornInclusions_le_closedT1Embeddings)
  exact TopCat.weakHomotopyEquivalences.of_transfiniteComposition_closedT1 hW0

/-- Horn left-class maps are weak equivalences, conditional only on `W`
stability for the sequential (`ℕ`) shape. -/
theorem horn_llp_le_weakHomotopyEquivalences_of_sequential_perDiagram
    [(SSet.KanComplex.W :
      MorphismProperty SSet.{0}).IsStableUnderTransfiniteCompositionOfShape
      ℕ] :
    realizedHornInclusions.{0}.rlp.llp ≤ weakHomotopyEquivalences := by
  rw [horn_rlp_llp_eq_sequential]
  refine retracts_le_iff.mpr ?_
  intro X Y f hf
  obtain ⟨hT⟩ := hf
  have hW0 := hT.ofLE (le_inf coproducts_pushouts_le_weakHomotopyEquivalences
    pushouts_coproducts_realizedHornInclusions_le_closedT1Embeddings)
  exact TopCat.weakHomotopyEquivalences.of_transfiniteComposition_closedT1 hW0

end TopCat
