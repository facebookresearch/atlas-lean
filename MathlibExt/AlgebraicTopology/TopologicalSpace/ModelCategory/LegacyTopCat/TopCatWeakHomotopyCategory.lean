/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyIdentities

/-!
# Topological spaces with weak homotopy equivalences

On `TopCat.{0}`, the category-with-weak-equivalences structure uses
`TopCat.weakHomotopyEquivalences`. This is the inverse image of `SSet.KanComplex.W` under the
singular functor. The identity maps belong to this weak-equivalence class.

See Goerss–Jardine, *Simplicial Homotopy Theory*, I.3.
-/

@[expose] public section

open CategoryTheory

namespace TopCat

/-- The `CategoryWithWeakEquivalences` structure on `TopCat.{0}` has `weakEquivalences :=
TopCat.weakHomotopyEquivalences`, equivalently the maps whose singular images lie in
`SSet.KanComplex.W`. -/
@[nolint defsWithUnderscore]
instance : HomotopicalAlgebra.CategoryWithWeakEquivalences TopCat.{0} where
  weakEquivalences := weakHomotopyEquivalences

/-- For the weak-equivalence structure on `TopCat.{0}` given by weak homotopy equivalences, every
identity morphism belongs to `HomotopicalAlgebra.weakEquivalences TopCat.{0}`. -/
instance : (HomotopicalAlgebra.weakEquivalences TopCat.{0}).ContainsIdentities :=
  inferInstanceAs ((weakHomotopyEquivalences : MorphismProperty TopCat.{0}).ContainsIdentities)

end TopCat
