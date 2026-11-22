/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalAnodyneClass
public import MathlibExt.AlgebraicTopology.ModelCategory.NaiveFibrations

/-!
# Naive fibrations for the actual finite-interval system

These concrete predicates select the accepted auxiliary anodyne class
in the generic right-lifting and terminal-map APIs. The right lifting
class is exactly that of the actual inner horns and finite-interval
endpoint corners, by the accepted Galois equality.

They are auxiliary naive predicates. No equality with the genuine Joyal
fibration class over arbitrary bases, or ambient model/fibration instance,
is installed.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace SSet.joyalInterval

/-- The naive right lifting class of the specified finite-interval anodyne maps. -/
def auxiliaryNaiveFibrations : MorphismProperty SSet.{u} :=
  auxiliaryAnodyneExtensions.naiveFibrations

/-- Objects whose terminal maps lie in the specified auxiliary naive class. -/
def auxiliaryNaiveFibrantObjects : ObjectProperty SSet.{u} :=
  auxiliaryAnodyneExtensions.naiveFibrantObjects

/-- The concrete naive class is exactly right lifting against the actual generators. -/
lemma auxiliaryNaiveFibrations_eq_generatorRlp :
    auxiliaryNaiveFibrations.{u} = auxiliaryGenerators.{u}.rlp :=
  auxiliaryAnodyneExtensions.rlp_eq

end SSet.joyalInterval
