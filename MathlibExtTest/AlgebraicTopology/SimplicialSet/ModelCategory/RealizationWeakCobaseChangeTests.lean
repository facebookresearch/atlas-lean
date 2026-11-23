/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakCobaseChange

/-!
# Realization weak cobase-change tests

These tests pin the pushed-leg orientation, exact stability instance, generic
`of_isPushout` client, and the identity-pushout boundary case. They make no
global TopCat model-category or unrestricted cobase-change claim.
-/

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.RealizationWeakCobaseChangeTests

/-- The conclusion is the pushed leg `f'`, not the other pushout leg. -/
example {A B X Y : SSet.{u}}
    {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout i f f' j) [Mono i]
    (hf : SSet.realizationWeakEquivalences f) :
    SSet.realizationWeakEquivalences f' :=
  SSet.realizationWeakEquivalences.of_isPushout_mono sq hf

example :
    SSet.realizationWeakEquivalences.IsStableUnderCobaseChangeAgainst
      (MorphismProperty.monomorphisms SSet.{u}) :=
  inferInstance

/-- The generic cobase-change API sees the same orientation. -/
example {A B X Y : SSet.{u}}
    {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout i f f' j) [Mono i]
    (hf : SSet.realizationWeakEquivalences f) :
    SSet.realizationWeakEquivalences f' := by
  exact
    (inferInstance :
      SSet.realizationWeakEquivalences.IsStableUnderCobaseChangeAgainst
        (MorphismProperty.monomorphisms SSet.{u})).of_isPushout
      sq (MorphismProperty.monomorphisms.infer_property i) hf

/-- Pushing an identity along a mono gives the identity on the target. -/
example {A B : SSet.{u}} (i : A ⟶ B) [Mono i] :
    SSet.realizationWeakEquivalences (𝟙 B) := by
  exact SSet.realizationWeakEquivalences.of_isPushout_mono
    (IsPushout.of_id_snd (f := i))
    (SSet.realizationWeakEquivalences.id_mem A)

section UniverseOne

example {A B X Y : SSet.{1}}
    {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout i f f' j) [Mono i]
    (hf : SSet.realizationWeakEquivalences f) :
    SSet.realizationWeakEquivalences f' :=
  SSet.realizationWeakEquivalences.of_isPushout_mono sq hf

example :
    SSet.realizationWeakEquivalences.IsStableUnderCobaseChangeAgainst
      (MorphismProperty.monomorphisms SSet.{1}) :=
  inferInstance

end UniverseOne

section UniverseZero

example {A B X Y : SSet.{0}}
    {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout i f f' j) [Mono i]
    (hf : SSet.realizationWeakEquivalences f) :
    SSet.realizationWeakEquivalences f' :=
  SSet.realizationWeakEquivalences.of_isPushout_mono sq hf

example :
    SSet.realizationWeakEquivalences.IsStableUnderCobaseChangeAgainst
      (MorphismProperty.monomorphisms SSet.{0}) :=
  inferInstance

end UniverseZero

section NegativeBoundaries

example : True := by
  fail_if_success let _ : ModelCategory TopCat.{u} := inferInstance
  fail_if_success let _ : ModelCategory TopCat.{1} := inferInstance
  fail_if_success let _ : ModelCategory TopCat.{0} := inferInstance
  fail_if_success
    let _ : SSet.realizationWeakEquivalences.{u}.IsStableUnderCobaseChange :=
      inferInstance
  trivial

end NegativeBoundaries

end MathlibExtTest.AlgebraicTopology.SimplicialSet.RealizationWeakCobaseChangeTests
