/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatBaseHomologyEquivalence

/-! # Tests for TopCat local-coefficient homology-equivalence closure -/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe uX

namespace MathlibExtTest.AlgebraicTopology.LocalCoefficient.TopCatBaseHomologyEquivalenceTests

section Identity

variable (X : TopCat.{uX})

example : TopCat.IsLocalCoefficientHomologyEquivalence (𝟙 X) :=
  TopCat.isLocalCoefficientHomologyEquivalence_id X

end Identity

section Composition

variable {X Y Z : TopCat.{uX}} {f : X ⟶ Y} {g : Y ⟶ Z}
variable (hf : TopCat.IsLocalCoefficientHomologyEquivalence f)
variable (hg : TopCat.IsLocalCoefficientHomologyEquivalence g)

example : TopCat.IsLocalCoefficientHomologyEquivalence (f ≫ g) :=
  hf.comp hg

example (L : TopCat.LocalSystem ℤ Z) (n : ℕ) :
    IsIso (TopCat.localCoefficientPullbackHomologyMap (f ≫ g) L n) :=
  hf.comp hg L n

example (L : TopCat.LocalSystem ℤ Z) (n : ℕ) :
    IsIso
      (TopCat.localCoefficientPullbackHomologyMap
        f (L.pullback g) n) :=
  hf (L.pullback g) n

end Composition

section NonidentityComposition

variable {X : TopCat.{uX}} {f g : X ⟶ X}
variable (hf : TopCat.IsLocalCoefficientHomologyEquivalence f)
variable (hg : TopCat.IsLocalCoefficientHomologyEquivalence g)

example (hfne : f ≠ 𝟙 X) (hgne : g ≠ 𝟙 X) :
    f ≠ 𝟙 X ∧ g ≠ 𝟙 X ∧
      TopCat.IsLocalCoefficientHomologyEquivalence (f ≫ g) :=
  ⟨hfne, hgne, hf.comp hg⟩

end NonidentityComposition

section RaisedUniverse

variable {X Y Z : TopCat.{2}} {f : X ⟶ Y} {g : Y ⟶ Z}
variable (hf : TopCat.IsLocalCoefficientHomologyEquivalence f)
variable (hg : TopCat.IsLocalCoefficientHomologyEquivalence g)

example : TopCat.IsLocalCoefficientHomologyEquivalence (f ≫ g) :=
  hf.comp hg

end RaisedUniverse

section StoppingBoundary

#guard_msgs (error, substring := true) in
#check TopCat.IsLocalCoefficientHomologyEquivalence.two_out_of_three

#guard_msgs (error, substring := true) in
#check TopCat.IsLocalCoefficientHomologyEquivalence.of_weakEquivalence

#guard_msgs (error, substring := true) in
#check TopCat.IsLocalCoefficientHomologyEquivalence.isAcyclic

#guard_msgs (error, substring := true) in
#check TopCat.IsLocalCoefficientHomologyEquivalence.isPlusConstructionAlong

#guard_msgs (error, substring := true) in
#check TopCat.localCoefficientHomologyEquivalences

#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.StableGL.liftedFiniteBGLTelescopeLocalCoefficientHomologyPlusCandidate

end StoppingBoundary

#print axioms TopCat.isLocalCoefficientHomologyEquivalence_id
#print axioms TopCat.IsLocalCoefficientHomologyEquivalence.comp

end MathlibExtTest.AlgebraicTopology.LocalCoefficient.TopCatBaseHomologyEquivalenceTests
