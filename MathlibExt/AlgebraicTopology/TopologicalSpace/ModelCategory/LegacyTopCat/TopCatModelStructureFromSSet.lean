/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelStructureConditional
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelCompatibilityFromSSet

/-!
# Topological model structure from simplicial lifting inputs

Let `H` be the realized horn inclusions and `W` the weak homotopy equivalences on
`TopCat.{u}`. Assume `H.rlp.llp≤W`. On simplicial sets, assume boundary-right-lifting maps
between Kan complexes are Kan weak equivalences and `J.rlp ⊓ KanComplex.W ≤ I.rlp`, where `I`
and `J` are the simplicial boundary and horn generator classes. These three inputs give the
topological compatibility equalities and hence the model structure with boundary-generated
cofibrations, horn-right-lifting fibrations, and weak homotopy equivalences.
-/

@[expose] public section

open CategoryTheory HomotopicalAlgebra MorphismProperty

universe u

namespace TopCat

/-- In universe `u`, assume `(TopCat.realizedHornInclusions.{u}).rlp.llp ≤
TopCat.weakHomotopyEquivalences`. Also assume that every `f:X→Y` between Kan simplicial sets
with `SSet.modelCategoryQuillen.I.{u}.rlp f` lies in `SSet.KanComplex.W.{u}`, and that
`SSet.modelCategoryQuillen.J.{u}.rlp ⊓ SSet.KanComplex.W.{u} ≤
SSet.modelCategoryQuillen.I.{u}.rlp`. These inputs give `ModelCategory TopCat.{u}` with weak
homotopy equivalences, boundary-generated cofibrations, and horn-right-lifting fibrations. -/
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
