/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalAnodyneClass
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalGeneratorProperties
public import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryFactorization

/-!
# Auxiliary anodyne maps are monomorphisms

The actual generators are monic. Every map lifting against all
monomorphisms therefore lifts against these generators. Antitonicity of
left lifting and the independent monomorphism weak factorization system
then make every map in the auxiliary double lifting closure monic.

This proves the monicity requirement for the specified finite-interval
class before construction of its cylinder axioms or a model structure.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

universe u

namespace SSet.joyalInterval

/-- The auxiliary double lifting closure consists of actual monomorphisms. -/
theorem auxiliaryAnodyneExtensions_le_monomorphisms :
    auxiliaryAnodyneExtensions.{u} ≤ MorphismProperty.monomorphisms SSet := by
  change auxiliaryGenerators.rlp.llp ≤ MorphismProperty.monomorphisms SSet
  calc
    _ ≤ (MorphismProperty.monomorphisms SSet).rlp.llp :=
      MorphismProperty.antitone_llp
        (MorphismProperty.antitone_rlp auxiliaryGenerators_le_monomorphisms)
    _ = MorphismProperty.monomorphisms SSet :=
      SSet.isWeakFactorizationSystem_monomorphisms.llp

/-- Membership in the auxiliary anodyne class supplies monicity. -/
lemma auxiliaryAnodyneExtensions.mono {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : auxiliaryAnodyneExtensions f) : Mono f :=
  auxiliaryAnodyneExtensions_le_monomorphisms f hf

end SSet.joyalInterval
