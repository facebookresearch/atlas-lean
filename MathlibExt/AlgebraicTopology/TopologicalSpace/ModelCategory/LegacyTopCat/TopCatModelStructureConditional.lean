/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatBoundaryWFS
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHornWFS
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyCategory
public import Mathlib.AlgebraicTopology.ModelCategory.Basic

/-!
# Model structure from compatibility of boundary and horn lifting classes

In `TopCat.{u}`, let `B=realizedBoundaryInclusions`, `H=realizedHornInclusions`, and
`W=weakHomotopyEquivalences`. Suppose `H.rlp ⊓ W = B.rlp` and `B.rlp.llp ⊓ W = H.rlp.llp`.
Together with the boundary and horn weak factorization systems and the weak-equivalence
axioms, these equalities give a model structure with cofibrations `B.rlp.llp`, fibrations
`H.rlp`, and weak equivalences `W`.
-/

@[expose] public section

open CategoryTheory HomotopicalAlgebra MorphismProperty

universe u

namespace TopCat

/-- Let `B=TopCat.realizedBoundaryInclusions.{u}`, `H=TopCat.realizedHornInclusions.{u}`, and
`W=TopCat.weakHomotopyEquivalences` on `TopCat.{u}`. Assume `hFib : H.rlp ⊓ W = B.rlp` and
`hCof : B.rlp.llp ⊓ W = H.rlp.llp`. Then `modelCategoryConditional hFib hCof : ModelCategory
TopCat.{u}` uses weak equivalences `W`, cofibrations `B.rlp.llp`, and fibrations `H.rlp`. The
compatibility equalities are the two supplied hypotheses. -/
noncomputable abbrev modelCategoryConditional
    (hFib : (realizedHornInclusions.rlp ⊓ weakHomotopyEquivalences :
      MorphismProperty TopCat.{u}) = realizedBoundaryInclusions.rlp)
    (hCof : (realizedBoundaryInclusions.rlp.llp ⊓ weakHomotopyEquivalences :
      MorphismProperty TopCat.{u}) = realizedHornInclusions.rlp.llp) :
    ModelCategory TopCat.{u} := by
  letI : CategoryWithWeakEquivalences TopCat.{u} :=
    ⟨weakHomotopyEquivalences⟩
  letI : CategoryWithCofibrations TopCat.{u} :=
    ⟨realizedBoundaryInclusions.rlp.llp⟩
  letI : CategoryWithFibrations TopCat.{u} :=
    ⟨realizedHornInclusions.rlp⟩
  haveI : (weakEquivalences TopCat.{u}).HasTwoOutOfThreeProperty :=
    inferInstanceAs (weakHomotopyEquivalences.HasTwoOutOfThreeProperty)
  have hTF : trivialFibrations TopCat.{u} =
      realizedBoundaryInclusions.rlp := by
    have h0 : trivialFibrations TopCat.{u} =
        (realizedHornInclusions.rlp ⊓ weakHomotopyEquivalences :
          MorphismProperty TopCat.{u}) := rfl
    rw [h0]
    exact hFib
  have hTC : trivialCofibrations TopCat.{u} =
      realizedHornInclusions.rlp.llp := by
    have h0 : trivialCofibrations TopCat.{u} =
        (realizedBoundaryInclusions.rlp.llp ⊓ weakHomotopyEquivalences :
          MorphismProperty TopCat.{u}) := rfl
    rw [h0]
    exact hCof
  haveI : IsWeakFactorizationSystem (cofibrations TopCat.{u})
      (trivialFibrations TopCat.{u}) := by
    have hcof : cofibrations TopCat.{u} =
        realizedBoundaryInclusions.rlp.llp := rfl
    rw [hcof, hTF]
    infer_instance
  haveI : IsWeakFactorizationSystem (trivialCofibrations TopCat.{u})
      (fibrations TopCat.{u}) := by
    have hfib : fibrations TopCat.{u} = realizedHornInclusions.rlp := rfl
    rw [hTC, hfib]
    infer_instance
  exact ModelCategory.mk' TopCat.{u}

end TopCat
