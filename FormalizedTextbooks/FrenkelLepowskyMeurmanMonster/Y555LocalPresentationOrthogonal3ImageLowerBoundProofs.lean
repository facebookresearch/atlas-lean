/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual local reflection-image lower bound from distinct source root transports. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3ParabolicLowerBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexRepresentativeValues

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Pointwise

/-- Distinct actual source root transports give the full local reflection image order bound. -/
theorem y322Orthogonal3Image_card_ge_of_distinct
    (hd : Function.Injective (fun i : Fin 3159 =>
      (y322Orthogonal3Hom (y322TCIndexRepresentative i))⁻¹ • y322Orthogonal3E7Roots)) :
    9170703360 ≤ Nat.card y322Orthogonal3Image := by
  let representative := fun i : Fin 3159 =>
    y322Orthogonal3Hom (y322TCIndexRepresentative i)
  have hrep (i : Fin 3159) : representative i ∈ y322Orthogonal3Image := ⟨_, rfl⟩
  have hle : y322Orthogonal3E7Image ≤ y322Orthogonal3Image := by
    rintro _ ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  have h := y322FiniteSubgroup_card_ge_of_orbit y322Orthogonal3E7Image
    y322Orthogonal3Image hle y322Orthogonal3E7Roots
    y322Orthogonal3E7Image_fixed representative hrep hd
  exact (Nat.mul_le_mul_right 3159 y322Orthogonal3E7Image_card_ge).trans h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
