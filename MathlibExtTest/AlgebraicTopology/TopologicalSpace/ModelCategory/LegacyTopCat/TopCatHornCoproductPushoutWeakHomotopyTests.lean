/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHornCoproductPushoutWeakHomotopy

@[expose] public section

/-!
# Horn-coproduct pushout weak-homotopy-equivalence client

Thin public client for `TopCat.hornCoproduct_pushout_inr_mem_weakHomotopyEquivalences`
by term application only. Forwards the horn family and every pushout hypothesis
unchanged and invokes the provider directly. Supplies no premise, adds no instance,
and claims no property-level coproduct/pushout inclusion, transfinite closure, or
model structure.
-/

set_option autoImplicit false

open CategoryTheory Limits

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatHornCoproductPushoutWeakHomotopyTests

/-- Pushout leg of a horn-coproduct inclusion as given by the provider. -/
theorem hornCoproduct_pushout_inr_client {J : Type 0} {n : J → ℕ}
    {k : ∀ j, Fin (n j + 1)} {hn : ∀ j, 0 < n j} {Y P : TopCat.{0}}
    {f : (∐ fun j => TopCat.hornSDRDomain J n k j) ⟶ Y}
    {g : (∐ fun j => TopCat.hornSDRSimplex J n j) ⟶ P} {j : Y ⟶ P}
    (h : IsPushout (Limits.Sigma.map (fun j => TopCat.hornSDRIncl J n k j)) f g j) :
    TopCat.weakHomotopyEquivalences j :=
  TopCat.hornCoproduct_pushout_inr_mem_weakHomotopyEquivalences (hn := hn) h

#check @TopCat.hornCoproduct_pushout_inr_mem_weakHomotopyEquivalences
#print axioms TopCat.hornCoproduct_pushout_inr_mem_weakHomotopyEquivalences
#print axioms hornCoproduct_pushout_inr_client

end MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatHornCoproductPushoutWeakHomotopyTests
