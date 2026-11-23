/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Exact.Extension.SplitExactAuxiliaryRealizationConull

/-! # Direct clients of the original split-exact auxiliary realization -/

universe u v

noncomputable section

open CategoryTheory CategoryTheory.ExactCategory CategoryTheory.Limits
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory Simplicial Topology
open AlgebraicKTheory AlgebraicKTheory.AuxiliaryExtension

attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction

#check @AlgebraicKTheory.AuxiliaryExtension.splitExactAuxiliary_realization_pathConnected
#print axioms AlgebraicKTheory.AuxiliaryExtension.splitExactAuxiliary_realization_pathConnected
#check @AlgebraicKTheory.AuxiliaryExtension.splitExactAuxiliary_realization_positiveGroup_subsingleton_at
#print axioms AlgebraicKTheory.AuxiliaryExtension.splitExactAuxiliary_realization_positiveGroup_subsingleton_at
#check @AlgebraicKTheory.AuxiliaryExtension.splitExactAuxiliary_realization_conull
#print axioms AlgebraicKTheory.AuxiliaryExtension.splitExactAuxiliary_realization_conull
#check @AlgebraicKTheory.AuxiliaryExtension.splitExactAuxiliary_realization_full
#print axioms AlgebraicKTheory.AuxiliaryExtension.splitExactAuxiliary_realization_full
#check @AlgebraicKTheory.AuxiliaryExtension.canonicalSplitAuxiliary_realization_full
#print axioms AlgebraicKTheory.AuxiliaryExtension.canonicalSplitAuxiliary_realization_full

section OriginalExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

-- Arbitrary original C, original exact structure and arbitrary X; no Ring specialization.
example
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting)
    (X : C) :
    PathConnectedSpace (SSet.toTop.obj (nerve (Auxiliary C X))) ∧
      (∀ (n : ℕ) (y : SSet.toTop.obj (nerve (Auxiliary C X))),
        Subsingleton (HomotopyGroup.Pi (n + 1)
          (SSet.toTop.obj (nerve (Auxiliary C X))) y)) ∧
      TopCat.weakHomotopyEquivalences
        (terminal.from (SSet.toTop.obj (nerve (Auxiliary C X)))) := by
  exact splitExactAuxiliary_realization_full hSplit X

-- A positive group at any actual realized point, rather than only a nerve vertex.
example
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting)
    (X : C) (n : ℕ) (y : SSet.toTop.obj (nerve (Auxiliary C X)))
    (a b : HomotopyGroup.Pi (n + 1) (SSet.toTop.obj (nerve (Auxiliary C X))) y) : a = b := by
  exact (splitExactAuxiliary_realization_positiveGroup_subsingleton_at hSplit X n y).elim a b

-- The exact selected topological terminal map remains the map being checked.
example
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting)
    (X : C) : TopCat.weakHomotopyEquivalences
      (terminal.from (SSet.toTop.obj (nerve (Auxiliary C X)))) := by
  exact splitExactAuxiliary_realization_conull hSplit X

end OriginalExactStructure

-- The canonical split structure supplies row splittings; no ExactCategory or splitness
-- witness is an outer input to this client.
example {C : Type u} [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] (X : C) :
    letI : ExactCategory C := CategoryTheory.ExactCategory.splitExactCategory
    PathConnectedSpace (SSet.toTop.obj (nerve (Auxiliary C X))) ∧
      (∀ (n : ℕ) (y : SSet.toTop.obj (nerve (Auxiliary C X))),
        Subsingleton (HomotopyGroup.Pi (n + 1)
          (SSet.toTop.obj (nerve (Auxiliary C X))) y)) ∧
      TopCat.weakHomotopyEquivalences
        (terminal.from (SSet.toTop.obj (nerve (Auxiliary C X)))) := by
  exact canonicalSplitAuxiliary_realization_full X

end
