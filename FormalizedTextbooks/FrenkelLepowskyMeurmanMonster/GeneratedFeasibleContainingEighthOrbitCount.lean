/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingEighthClassStabilizer

/-! The actual one-eighth A orbit, with its precise remaining stabilizer index.
An upper bound and an equivalence expose the whole-vector fixation obligation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The entire actual A stabilizer of the independently defined sixth destination. -/
def generatedFeasibleContainingEighthAStabilizer :
    Subgroup (localAxisStabilizer generatedFeasiblePhysicalRootPair) :=
  MulAction.stabilizer (localAxisStabilizer generatedFeasiblePhysicalRootPair)
    generatedFeasibleContainingNewDestination

/-- Genuine simultaneous fixers include into the actual entire first-axis stabilizer. -/
def generatedFeasibleContainingEighthNInclusion :
    generatedFeasibleContainingEighthNStabilizer →*
      generatedFeasibleContainingEighthAStabilizer where
  toFun h := ⟨⟨h.val.val, h.val.property.1⟩, h.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- No actual simultaneous fixer is identified with another by this inclusion. -/
theorem generatedFeasibleContainingEighthNInclusion_injective :
    Function.Injective generatedFeasibleContainingEighthNInclusion := by
  intro h k he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun x : generatedFeasibleContainingEighthAStabilizer => x.val.val) he

/-- The actual included simultaneous subgroup retains its exact proved order. -/
theorem generatedFeasibleContainingEighthNInclusion_range_card :
    Nat.card generatedFeasibleContainingEighthNInclusion.range = 1509949440 := by
  rw [← Nat.card_congr
    (MonoidHom.ofInjective generatedFeasibleContainingEighthNInclusion_injective).toEquiv]
  exact generatedFeasibleContainingEighthNStabilizer_card

/-- The entire actual A orbit differs from the expected count by precisely the remaining
index of simultaneous fixers in the full A stabilizer. -/
theorem generatedFeasibleContainingEighth_actual_A_orbit_index_equation :
    Nat.card (MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingNewDestination) *
        generatedFeasibleContainingEighthNInclusion.range.index = 470060236800 := by
  have hA := generatedFeasibleContainingEighthAStabilizer.card_mul_index
  rw [generatedFeasibleContainingEighthAStabilizer, MulAction.index_stabilizer,
    ← Nat.card_coe_set_eq,
    localAxisStabilizer_card_of_co1_card _ co1_card_exact] at hA
  have hN := generatedFeasibleContainingEighthNInclusion.range.card_mul_index
  rw [generatedFeasibleContainingEighthNInclusion_range_card] at hN
  apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 1509949440)
  calc
    1509949440 * (Nat.card (MulAction.orbit
        (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          generatedFeasibleContainingNewDestination) *
            generatedFeasibleContainingEighthNInclusion.range.index) =
      (1509949440 * generatedFeasibleContainingEighthNInclusion.range.index) *
        Nat.card (MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          generatedFeasibleContainingNewDestination) := by ring
    _ = 709767191322427392000 := by rw [hN]; exact hA
    _ = 1509949440 * 470060236800 := by decide

/-- The actual entire A orbit has at most 470,060,236,800 vectors. -/
theorem generatedFeasibleContainingEighth_actual_A_orbit_card_le :
    Nat.card (MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingNewDestination) ≤ 470060236800 := by
  have he := generatedFeasibleContainingEighth_actual_A_orbit_index_equation
  have hi : 1 ≤ generatedFeasibleContainingEighthNInclusion.range.index := by
    by_contra hn
    have hz : generatedFeasibleContainingEighthNInclusion.range.index = 0 := by omega
    rw [hz, mul_zero] at he
    contradiction
  calc
    _ = Nat.card (MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingNewDestination) * 1 := by omega
    _ ≤ _ := Nat.mul_le_mul_left _ hi
    _ = _ := he

/-- Full inclusion equality is exactly the substantive claim that every whole destination fixer
also fixes the original Omega vector, hence belongs to the simultaneous subgroup. -/
theorem generatedFeasibleContainingEighthNInclusion_range_eq_top_iff :
    generatedFeasibleContainingEighthNInclusion.range = ⊤ ↔
      ∀ h : generatedFeasibleContainingEighthAStabilizer, h.val.val ∈ localOmegaStabilizer := by
  rw [MonoidHom.range_eq_top]
  constructor
  · intro hs h
    obtain ⟨n, hn⟩ := hs h
    have hv := congrArg (fun x : generatedFeasibleContainingEighthAStabilizer => x.val.val) hn
    exact hv ▸ n.val.property.2
  · intro hfix h
    let n : generatedFeasibleContainingEighthNStabilizer :=
      ⟨⟨h.val.val, h.val.property, hfix h⟩, h.property⟩
    exact ⟨n, rfl⟩

/-- The desired numerical A count is equivalent to the actual whole-vector simultaneous-fixer
claim, rather than to recognition or the size of the outgoing coefficient fibre alone. -/
theorem generatedFeasibleContainingEighth_actual_A_orbit_card_iff :
    Nat.card (MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingNewDestination) = 470060236800 ↔
      ∀ h : generatedFeasibleContainingEighthAStabilizer, h.val.val ∈ localOmegaStabilizer := by
  rw [← generatedFeasibleContainingEighthNInclusion_range_eq_top_iff,
    ← Subgroup.index_eq_one]
  have he := generatedFeasibleContainingEighth_actual_A_orbit_index_equation
  constructor
  · intro hc
    rw [hc] at he
    omega
  · intro hi
    rw [hi, mul_one] at he
    exact he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
