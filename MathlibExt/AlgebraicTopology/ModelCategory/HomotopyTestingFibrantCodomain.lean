/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyTestingLifting

/-!
# Testing fibrations at naive fibrant codomains

The right lifting class of monic testing equivalences lies in the naive
right class for all maps. At a naive fibrant codomain, the converse follows
from the actual monic lifting classifier. No source fibrancy is assumed.

Cisinski, Higher Categories and Homotopical Algebra, July 30, 2026,
Theorem 2.4.19 states the comparison between fibrant objects. The
codomain-only comparison below is derived from Proposition 2.4.30 and
the anodyne inclusion, before model existence.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace HomotopicalAlgebra.Precylinder.IsAnodyneSystem

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasPushouts C]
  [HasTerminal C] (P : Precylinder (𝟭 C)) [P.IsExact.{w}]
  (An : MorphismProperty C) [P.IsAnodyneSystem.{w} An]

/-- The actual testing right class is naive at arbitrary source and codomain,
without an initial-object, factorization or object-fibrancy assumption. -/
theorem testingFibrations_le_naiveFibrations :
    P.testingFibrations An ≤ An.naiveFibrations := by
  have hAn : An ≤ P.testingTrivialCofibrations An := by
    change An ≤ MorphismProperty.monomorphisms C ⊓ P.testingEquivalences An
    exact le_inf (le_monomorphisms (P := P) (An := An))
      (anodyne_le_testingEquivalences P An)
  exact MorphismProperty.antitone_rlp hAn

variable [HasInitial C] [InitialMonoClass C]
  [MorphismProperty.HasFactorization An An.rlp]

/-- Testing and naive right lifting agree when the actual codomain is naive
fibrant, with no separate naive-fibrancy premise on the source. -/
theorem testingFibrations_iff_naiveFibrations_of_naiveFibrant
    {X Y : C} (p : X ⟶ Y) (hY : An.naiveFibrantObjects Y) :
    P.testingFibrations An p ↔ An.naiveFibrations p := by
  constructor
  · exact testingFibrations_le_naiveFibrations P An p
  · intro hp
    rw [P.testingFibrations_iff An p]
    intro A B i hmono hw
    have : Mono i := hmono
    exact ((testingEquivalences_iff_llp_naiveFibrantCodomain P An i).mp hw) p
      ⟨hp, trivial, hY⟩

end HomotopicalAlgebra.Precylinder.IsAnodyneSystem
