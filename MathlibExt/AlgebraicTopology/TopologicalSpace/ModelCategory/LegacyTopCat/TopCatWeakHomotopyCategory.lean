/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyIdentities

/-! # Category instance for TopCat weak homotopy equivalences

Staged KQ3 packet at universe zero. The sibling providers
`LegacyTopCat.TopCatWeakHomotopyEquivalence`
(supplying `TopCat.weakHomotopyEquivalences`) and
`LegacyTopCat.TopCatWeakHomotopyIdentities`
(supplying `ContainsIdentities` at `TopCat.{0}`) are staged; this file defines no fallback.

Provides only the `CategoryWithWeakEquivalences TopCat.{0}` instance with
`weakEquivalences := weakHomotopyEquivalences`, reusing the already proved
`ContainsIdentities` instance. No model structure, product theorem,
or KQ4 statement is added.

Mathematical source: Goerss--Jardine, Simplicial Homotopy Theory, I.3.
-/

@[expose] public section

open CategoryTheory

namespace TopCat

/-- Weak homotopy equivalences give the `CategoryWithWeakEquivalences`
instance on `TopCat.{0}`. -/
@[nolint defsWithUnderscore]
instance : HomotopicalAlgebra.CategoryWithWeakEquivalences TopCat.{0} where
  weakEquivalences := weakHomotopyEquivalences

/-- Bridge identities to the installed weak-equivalence class. -/
instance : (HomotopicalAlgebra.weakEquivalences TopCat.{0}).ContainsIdentities :=
  inferInstanceAs ((weakHomotopyEquivalences : MorphismProperty TopCat.{0}).ContainsIdentities)

end TopCat
