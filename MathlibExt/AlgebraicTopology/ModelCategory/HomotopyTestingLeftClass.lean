/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyTestingLifting
public import MathlibExt.AlgebraicTopology.ModelCategory.NaiveFibrantTargetLifting

/-!
# The full testing left class

The monomorphism-restricted lifting classifier and the independent monicity
theorem identify the whole class of monic testing equivalences with left
lifting against naive fibrations whose codomains are naive fibrant.

This strengthens Cisinski, *Higher Categories and Homotopical Algebra*,
July 30, 2026, Proposition 2.4.30 (printed pp.61–62 / PDF pp.77–78), by
using the proved monicity supplement. No fibrancy of either original object
or model structure is assumed.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace HomotopicalAlgebra.Precylinder.IsAnodyneSystem

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasPushouts C]
  [HasInitial C] [InitialMonoClass C] [HasTerminal C]
  (P : Precylinder (𝟭 C)) [P.IsExact.{w}]
  (An : MorphismProperty C) [P.IsAnodyneSystem.{w} An]
  [MorphismProperty.HasFactorization An An.rlp]

/-- The whole class of monic testing equivalences is the left lifting class
of naive fibrations with naive fibrant codomain. -/
theorem testingTrivialCofibrations_eq_llp_naiveFibrantCodomain :
    P.testingTrivialCofibrations An =
      (An.naiveFibrations ⊓
        MorphismProperty.ofObjectProperty ⊤ An.naiveFibrantObjects).llp := by
  rw [testingTrivialCofibrations_eq_inf_llp_naiveFibrantCodomain P An]
  exact inf_eq_right.mpr
    (MorphismProperty.llp_naiveFibrantCodomain_le_monomorphisms An
      (le_monomorphisms (P := P) (An := An)))

end HomotopicalAlgebra.Precylinder.IsAnodyneSystem
