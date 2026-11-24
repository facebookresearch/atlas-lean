/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.MachineLearning.GraphicalModels.PCOrientation

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

/-- An answer table for the chain `0 → 1 → 2` that is Markov and adjacency-faithful but not
orientation-faithful: besides the chain's separation `0 ⫫ 2 | {1}` it declares `0 ⫫ 2 | ∅`. -/
def chainSpurious : CIOracle 3 where
  Indep i j S := ({i, j} : Finset (Fin 3)) = {0, 2} ∧ (S = ∅ ∨ S = {1})
  decIndep _ _ _ := inferInstance

/-- The answer table of the chain `0 → 1 → 2` on endpoint-free queries of distinct nodes:
`0` and `2` are independent exactly given `{1}`. -/
def chainTrue : CIOracle 3 where
  Indep i j S := ({i, j} : Finset (Fin 3)) = {0, 2} ∧ S = {1}
  decIndep _ _ _ := inferInstance

/-- Markov plus adjacency-faithfulness does not suffice: on the spurious table PC deletes `0 - 2`
in round 0 with the empty separator and orients the false collider `0 → 1 ← 2`. -/
example : (pcAdjacency chainSpurious).IsCollider 0 1 2 := by
  decide

/-- On the chain's own table PC records the separator `{1}` and leaves `0 - 1 - 2` unoriented. -/
example : ¬ (pcAdjacency chainTrue).IsCollider 0 1 2 := by
  decide

/-- On the XOR answer table the adjacency phase deletes every edge, so nothing is oriented. -/
example : ∀ a c d : Fin 3, ¬ (pcAdjacency PCSkeleton.xorTable).IsCollider a c d := by
  decide

end Cslib.MachineLearning.GraphicalModels

namespace Cslib.MachineLearning.GraphicalModels

open BayesianDirichlet

/-- Headline: the collider rule orients exactly the v-structures. -/
example {α : Type*} {n : ℕ} {b : BayesNet α n} {O : CIOracle n} (hM : b.MarkovOracle O)
    (hA : b.AdjacencyFaithful O) (hOr : b.OrientationFaithful O) (a c d : Fin n) :
    (pcAdjacency O).IsCollider a c d ↔ IsVStructure b.toPa a c d :=
  pcAdjacency_isCollider_iff hM hA hOr a c d

/-- Headline: with the true graph's d-separation oracle, no faithfulness
hypothesis is needed. -/
example {α : Type*} {n : ℕ} (b : BayesNet α n) (a c d : Fin n) :
    (pcAdjacency b.dsepOracle).IsCollider a c d ↔ IsVStructure b.toPa a c d :=
  pcAdjacency_dsepOracle_isCollider_iff b a c d

end Cslib.MachineLearning.GraphicalModels
