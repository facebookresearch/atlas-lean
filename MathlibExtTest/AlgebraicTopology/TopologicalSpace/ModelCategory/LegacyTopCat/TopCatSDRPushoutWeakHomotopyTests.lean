/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatSDRPushoutWeakHomotopy

@[expose] public section

/-!
# SDR pushout weak-homotopy-equivalence client

Thin public client for `TopCat.sdr_pushout_inr_mem_weakHomotopyEquivalences` by term
application only. Preserves the explicit pushout, retraction, homotopy, and pointwise
fixed-subspace hypotheses and invokes the provider directly. Supplies no premise, adds no
instance, and claims no arbitrary weak-equivalence pushout stability or model structure.
-/

set_option autoImplicit false

open CategoryTheory Limits

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatSDRPushoutWeakHomotopyTests

/-- Pushout leg of a strong deformation retract as given by the provider. -/
theorem sdr_pushout_inr_client {A X Y P : TopCat.{0}} {i : A ⟶ X} {f : A ⟶ Y}
    {g : X ⟶ P} {j : Y ⟶ P} (h : IsPushout i f g j) (r : X ⟶ A)
    (retract : i ≫ r = 𝟙 A) (H : TopCat.Homotopy (𝟙 X) (r ≫ i))
    (stat : ∀ (t : unitInterval) (a : A), H (t, i a) = i a) :
    TopCat.weakHomotopyEquivalences j :=
  TopCat.sdr_pushout_inr_mem_weakHomotopyEquivalences h r retract H stat

#print axioms TopCat.sdr_pushout_inr_mem_weakHomotopyEquivalences
#print axioms sdr_pushout_inr_client

end MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatSDRPushoutWeakHomotopyTests
