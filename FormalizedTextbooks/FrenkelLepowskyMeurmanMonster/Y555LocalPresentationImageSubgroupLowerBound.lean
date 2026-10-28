/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Constructive subgroup image order bounds from actual finite transported fixed points. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationImageCosetLowerBound
public import Mathlib.Algebra.Group.Action.Hom

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Distinct fixed-point transports bound a finite subgroup order by a smaller subgroup order. -/
theorem y322FiniteSubgroup_card_ge_of_orbit {G X : Type*} [Group G] [Finite G]
    [MulAction G X] {size : ℕ} (K P : Subgroup G) (hKP : K ≤ P) (point : X)
    (fixed : ∀ k ∈ K, k • point = point) (representative : Fin size → G)
    (hrep : ∀ i, representative i ∈ P)
    (distinct : Function.Injective (fun i => (representative i)⁻¹ • point)) :
    Nat.card K * size ≤ Nat.card P := by
  let := MulAction.compHom X P.subtype
  let rep : Fin size → P := fun i => ⟨representative i, hrep i⟩
  have hf (k : P) (hk : k ∈ K.subgroupOf P) : k • point = point := fixed k.val hk
  have hd : Function.Injective (fun i => (rep i)⁻¹ • point) := distinct
  have h := y322FiniteGroup_card_ge_of_orbit (K.subgroupOf P) point hf rep hd
  have hc : Nat.card (K.subgroupOf P) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKP).toEquiv
  simpa only [hc] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
