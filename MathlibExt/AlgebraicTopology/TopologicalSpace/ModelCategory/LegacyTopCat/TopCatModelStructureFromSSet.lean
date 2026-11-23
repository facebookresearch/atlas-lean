/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelStructureConditional
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelCompatibilityFromSSet

/-!
# Conditional `TopCat` model structure from simplicial inputs

This file is part of the KQ3 layer. It assembles in every universe the
`ModelCategory TopCat` from exactly three explicit inputs: KQ3 horn-cell
closure `realizedHornInclusions.rlp.llp ≤ weakHomotopyEquivalences`,
the Kan-restricted boundary-RLP premise
`∀ {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y] {f : X ⟶ Y},
SSet.modelCategoryQuillen.I.{u}.rlp f → SSet.KanComplex.W.{u} f`
(identities on non-Kan simplicial sets lie in `I.rlp` but not in `W`,
so no universal `I.rlp ≤ W` is claimed), and
`SSet.modelCategoryQuillen.J.rlp ⊓ SSet.KanComplex.W ≤
SSet.modelCategoryQuillen.I.rlp`.

It reuses the staged bridge
`TopCat.boundaryRLP_le_weakHomotopyEquivalences_of_kanRestricted_Irlp_le_W`, the direct
first recognition `TopCat.hornRLP_inf_W_le_boundaryRLP_of_sSet`, the direct
second recognition `TopCat.boundaryLLP_inf_W_le_hornLLP_of_sSet`, the
conditional equalities `TopCat.hornRLP_inf_W_eq_boundaryRLP` and
`TopCat.boundaryLLP_inf_W_eq_hornLLP`, and `TopCat.modelCategoryConditional`;
no proof is duplicated here.

The conclusion is only the `noncomputable abbrev` below, never a global
instance. It supplies none of the three hypotheses and makes no
unconditional model-structure claim.
-/

@[expose] public section

open CategoryTheory HomotopicalAlgebra MorphismProperty

universe u

namespace TopCat

/-- Conditional assembly of the `TopCat` model structure in every universe.

From horn-cell closure, the Kan-restricted boundary-RLP premise, and the
J-recognition input, derives
the two compatibility equalities and packages `ModelCategory TopCat.{u}`
via `TopCat.modelCategoryConditional`. Without all three inputs, no
structure is claimed. -/
noncomputable abbrev modelCategoryFromSSet
    (hHorn : realizedHornInclusions.{u}.rlp.llp ≤ weakHomotopyEquivalences)
    (hI : ∀ {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y]
      {f : X ⟶ Y},
      SSet.modelCategoryQuillen.I.{u}.rlp f → SSet.KanComplex.W.{u} f)
    (hJ : SSet.modelCategoryQuillen.J.{u}.rlp ⊓ SSet.KanComplex.W.{u} ≤
      SSet.modelCategoryQuillen.I.{u}.rlp) :
    ModelCategory TopCat.{u} := by
  have hFib : (realizedHornInclusions.{u}.rlp ⊓ weakHomotopyEquivalences :
      MorphismProperty TopCat.{u}) = realizedBoundaryInclusions.{u}.rlp :=
    hornRLP_inf_W_eq_boundaryRLP_of_sSet hHorn hI hJ
  have hCof : (realizedBoundaryInclusions.{u}.rlp.llp ⊓ weakHomotopyEquivalences :
      MorphismProperty TopCat.{u}) = realizedHornInclusions.{u}.rlp.llp :=
    boundaryLLP_inf_W_eq_hornLLP_of_sSet hHorn hJ
  exact modelCategoryConditional hFib hCof

end TopCat
