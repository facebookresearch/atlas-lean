/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatBoundaryWFS
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHornWFS
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyCategory
public import Mathlib.AlgebraicTopology.ModelCategory.Basic

/-!
# Conditional TopCat model-structure assembly

This file is part of the KQ3 layer. It packages the smallest conditional
assembly of the intended `TopCat` model structure in every universe from the
existing KQ3 providers: the boundary/horn weak factorization systems
(`TopCatBoundaryWFS`, `TopCatHornWFS`) and weak homotopy equivalences
(`TopCatWeakHomotopyCategory`), via the pinned `ModelCategory.mk'`
constructor.

The two explicit hypotheses are the constructor-required compatibility
equalities, stated as infima of the concrete generator classes (definitionally
the trivial classes once the local cofibration/fibration instances below are
in scope):

* `hFib`: horn-RLP inf weak equivalences equals boundary-RLP
  (trivial fibrations equal boundary-RLP);
* `hCof`: boundary-left inf weak equivalences equals horn-left
  (trivial cofibrations equal horn-left).

Neither equality is proved here. No unconditional global `ModelCategory`
instance is created; the conclusion is a definition returning the packaged
structure only under both hypotheses. This proves no weak-equivalence,
fibration, or cofibration identification and adds no KQ4 statement.
-/

@[expose] public section

open CategoryTheory HomotopicalAlgebra MorphismProperty

universe u

namespace TopCat

/-- Conditional assembly of the `TopCat` model structure in every universe.

Given the two compatibility equalities, packages `ModelCategory TopCat.{u}`
with weak equivalences `weakHomotopyEquivalences`, cofibrations
`realizedBoundaryInclusions.rlp.llp`, and fibrations
`realizedHornInclusions.rlp`, via `ModelCategory.mk'`. Neither hypothesis is
proved here; without both, no model structure is claimed. -/
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
