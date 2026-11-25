/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.AnodyneTesting
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyTestingTwoOutOfThree
public import MathlibExt.AlgebraicTopology.ModelCategory.NaiveWeakTrivialFibrations
public import Mathlib.CategoryTheory.MorphismProperty.RetractArgument

/-!
# Monic testing equivalences with naive fibrant codomain

Factor the original monomorphism as an anodyne map followed by a naive
fibration. Two-out-of-three makes the latter weak; its naive fibrant
codomain then makes it trivial. The original monomorphism lifts against
this factor, and the native arrow retract retains the strict diagonal.

This is Cisinski, *Higher Categories and Homotopical Algebra*, July 30,
2026, Corollary 2.4.29 (printed p.61 / PDF p.77), with the stated generic
factorization hypotheses. No naive fibrancy of the source is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace HomotopicalAlgebra.Precylinder.IsAnodyneSystem

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasPushouts C]
  [HasInitial C] [InitialMonoClass C] [HasTerminal C]
  (P : Precylinder (𝟭 C)) [P.IsExact.{w}]
  (An : MorphismProperty C) [P.IsAnodyneSystem.{w} An]
  [MorphismProperty.HasFactorization An An.rlp]

/-- For an original monomorphism with naive fibrant codomain, testing
equivalence is exactly membership in the specified anodyne class. -/
theorem testingEquivalences_iff_anodyne_of_mono_of_naiveFibrant
    {X Y : C} (i : X ⟶ Y) [Mono i] (hY : An.naiveFibrantObjects Y) :
    P.testingEquivalences An i ↔ An i := by
  constructor
  · intro hi
    let d := MorphismProperty.factorizationData An An.rlp i
    have hj : P.testingEquivalences An d.i := anodyne_le_testingEquivalences P An d.i d.hi
    have hp : P.testingEquivalences An d.p :=
      (P.testingEquivalences An).of_precomp d.i d.p hj (by simpa only [d.fac] using hi)
    have htrivial : (MorphismProperty.monomorphisms C).rlp d.p :=
      (testingEquivalences_iff_rlp_monomorphisms_of_naiveFibration P An d.p d.hp hY).mp hp
    have : HasLiftingProperty i d.p := htrivial i (by infer_instance)
    have hleft : An.rlp.llp d.i := by
      simpa only [llp_rlp_eq P An] using d.hi
    rw [← llp_rlp_eq P An]
    exact MorphismProperty.of_retract (RetractArrow.ofLeftLiftingProperty d.fac) hleft
  · exact anodyne_le_testingEquivalences P An i

end HomotopicalAlgebra.Precylinder.IsAnodyneSystem
