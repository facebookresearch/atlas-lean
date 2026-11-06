/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisEnumerationLocal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisEnumerationFeasibleAnchor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionOrder

/-! Transporting the proved actual anchor sets to classification fiber counts.
The classification's first fiber must be identified with the indicated genuine
local orbit; no assertion about the other fibers or transitions is made. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Any actual axis classification identifying its first fiber with the proved
local orbit automatically has the exact 196560 anchor. -/
theorem generatedAxisClassification_anchor (r : GriessShortIndex) (c : ZMod 2)
    (κ : generatedVectorOrbit (conwayShortAxis r c) → Fin 12)
    (hκ : ∀ x, κ x = 0 ↔ x.val ∈ generatedAxisLocalOrbit r c) :
    classifiedOrbitCountVector κ 0 = 196560 := by
  have he : {x : generatedVectorOrbit (conwayShortAxis r c) // κ x = 0} ≃
      generatedAxisLocalAnchor r c :=
    Equiv.subtypeEquivRight (fun x => (hκ x).trans (by
      rw [generatedAxisLocalOrbit_eq_signed]))
  have hc := (Nat.card_congr he).trans (generatedAxisLocalAnchor_card r c)
  unfold classifiedOrbitCountVector
  exact_mod_cast hc

/-- Any actual feasible classification identifying its first fiber with the
proved local singleton automatically has anchor one. -/
theorem generatedFeasibleClassification_anchor (p : Fin 276)
    (κ : generatedFeasibleVectorOrbit (conwayShortAxis (Sum.inl (0, p)) 0)
      (conwayShortAxis (Sum.inl (0, p)) 1) → Fin 10)
    (hκ : ∀ x, κ x = 0 ↔ x.val ∈ generatedFeasibleLocalAnchorOrbit p) :
    classifiedOrbitCountVector κ 0 = 1 := by
  let e : generatedFeasibleLocalAnchorOrbit p ≃
      {x : generatedFeasibleVectorOrbit (conwayShortAxis (Sum.inl (0, p)) 0)
        (conwayShortAxis (Sum.inl (0, p)) 1) // κ x = 0} :=
    { toFun := fun x =>
        ⟨⟨x.val, generatedFeasibleLocalAnchorOrbit_subset p x.property⟩, (hκ _).mpr x.property⟩
      invFun := fun x => ⟨x.val.val, (hκ x.val).mp x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc := (Nat.card_congr e).symm.trans (generatedFeasibleLocalAnchorOrbit_card p)
  unfold classifiedOrbitCountVector
  exact_mod_cast hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
