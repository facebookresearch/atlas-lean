/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual central-involution eigenspaces and their generated-centralizer actions. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.CentralInvolution
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityFullProduct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFiniteness

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The full centralizer of the actual embedded central Q involution. -/
noncomputable def generatedCentralizer : Subgroup G :=
  Subgroup.centralizer {qIntoGenerated qCentralInvolution}

/-- The actual +1 and -1 spaces, defined from the constructed involution itself. -/
noncomputable def generatedCentralPlus : Submodule ℝ GriessSpace :=
  (localCentralGriess.toLinearMap - LinearMap.id).ker
/-- The actual tensor eigenspace on which the embedded central involution acts as −1. -/
noncomputable def generatedCentralMinus : Submodule ℝ GriessSpace :=
  (localCentralGriess.toLinearMap + LinearMap.id).ker

theorem mem_generatedCentralPlus (x : GriessSpace) :
    x ∈ generatedCentralPlus ↔ localCentralGriess x = x := by
  change localCentralGriess x - x = 0 ↔ _
  exact sub_eq_zero

theorem mem_generatedCentralMinus (x : GriessSpace) :
    x ∈ generatedCentralMinus ↔ localCentralGriess x = -x := by
  change localCentralGriess x + x = 0 ↔ _
  exact add_eq_zero_iff_eq_neg

/-- The actual fixed space is exactly the matrix-plus-short part of Conway coordinates. -/
theorem mem_generatedCentralPlus_iff_tensor_zero (x : GriessSpace) :
    x ∈ generatedCentralPlus ↔ (griessConwayEncode x).2.2 = 0 := by
  rw [mem_generatedCentralPlus]
  constructor
  · intro h
    have he := congrArg griessConwayEncode h
    rw [localCentralGriess_encode] at he
    have ht := congrArg (fun b : ConwayRawSpace => b.2.2) he
    funext t i
    have hc := congrFun (congrFun ht t) i
    dsimp only [Pi.neg_apply] at hc
    change (griessConwayEncode x).2.2 t i = 0
    linarith
  · intro h
    have he : griessConwayEncode (localCentralGriess x) = griessConwayEncode x := by
      rw [localCentralGriess_encode]
      exact Prod.ext rfl (Prod.ext rfl (by rw [h,neg_zero]))
    have hd := congrArg griessConwayDecode he
    simpa only [griessConwayDecode_encode] using hd

/-- The actual negative space is exactly the physical spin tensor part. -/
theorem mem_generatedCentralMinus_iff_matrix_short_zero (x : GriessSpace) :
    x ∈ generatedCentralMinus ↔
      (griessConwayEncode x).1 = 0 ∧ (griessConwayEncode x).2.1 = 0 := by
  rw [mem_generatedCentralMinus]
  constructor
  · intro h
    have he := congrArg griessConwayEncode h
    rw [localCentralGriess_encode] at he
    change _ = griessConwayEncodeLinear (-x) at he
    rw [map_neg] at he
    change ((griessConwayEncode x).1, (griessConwayEncode x).2.1,
      -(griessConwayEncode x).2.2) = -(griessConwayEncode x) at he
    constructor
    · funext i j
      have hc := congrArg (fun b : ConwayRawSpace => b.1 i j) he
      change (griessConwayEncode x).1 i j = -(griessConwayEncode x).1 i j at hc
      change (griessConwayEncode x).1 i j = 0
      linarith
    · funext r
      have hc := congrArg (fun b : ConwayRawSpace => b.2.1 r) he
      change (griessConwayEncode x).2.1 r = -(griessConwayEncode x).2.1 r at hc
      change (griessConwayEncode x).2.1 r = 0
      linarith
  · rintro ⟨hM,hX⟩
    have he : griessConwayEncode (localCentralGriess x) = griessConwayEncodeLinear (-x) := by
      rw [localCentralGriess_encode, map_neg]
      change ((griessConwayEncode x).1, (griessConwayEncode x).2.1,
        -(griessConwayEncode x).2.2) = -griessConwayEncode x
      apply Prod.ext
      · change (griessConwayEncode x).1 = -(griessConwayEncode x).1
        rw [hM,neg_zero]
      · apply Prod.ext
        · change (griessConwayEncode x).2.1 = -(griessConwayEncode x).2.1
          rw [hX,neg_zero]
        · rfl
    have hd := congrArg griessConwayDecode he
    rw [griessConwayDecode_encode] at hd
    change localCentralGriess x = griessConwayDecode (griessConwayEncode (-x)) at hd
    rw [griessConwayDecode_encode] at hd
    exact hd

theorem generatedCentralizer_commutes (g : generatedCentralizer) :
    g.val.val * localCentralGriess = localCentralGriess * g.val.val := by
  have h := Subgroup.mem_centralizer_singleton_iff.mp g.property
  exact congrArg (fun a : G => a.val) h

/-- Every element of the genuine full centralizer preserves the actual positive space. -/
theorem generatedCentralizer_preserves_plus (g : generatedCentralizer)
    (x : GriessSpace) (hx : x ∈ generatedCentralPlus) : g.val.val x ∈ generatedCentralPlus := by
  rw [mem_generatedCentralPlus] at hx ⊢
  have hc := congrArg (fun e : GriessSpace ≃ₗ[ℝ] GriessSpace => e x)
    (generatedCentralizer_commutes g)
  change g.val.val (localCentralGriess x) = localCentralGriess (g.val.val x) at hc
  rw [← hc,hx]

/-- Every element of the full centralizer preserves the actual 98304-dimensional tensor space. -/
theorem generatedCentralizer_preserves_minus (g : generatedCentralizer)
    (x : GriessSpace) (hx : x ∈ generatedCentralMinus) : g.val.val x ∈ generatedCentralMinus := by
  rw [mem_generatedCentralMinus] at hx ⊢
  have hc := congrArg (fun e : GriessSpace ≃ₗ[ℝ] GriessSpace => e x)
    (generatedCentralizer_commutes g)
  change g.val.val (localCentralGriess x) = localCentralGriess (g.val.val x) at hc
  rw [← hc,hx,map_neg]

/-- The involution's eigenspace grading follows from the proved actual multiplication. -/
theorem generatedCentralPlus_mul_minus (x y : GriessSpace)
    (hx : x ∈ generatedCentralPlus) (hy : y ∈ generatedCentralMinus) :
    griessProd x y ∈ generatedCentralMinus := by
  rw [mem_generatedCentralPlus] at hx
  rw [mem_generatedCentralMinus] at hy ⊢
  have hz := rhoLocal_product (inclQ qCentralInvolution) x y
  change localCentralGriess (griessProd x y) =
    griessProd (localCentralGriess x) (localCentralGriess y) at hz
  rw [hz,hx,hy,map_neg]

/-- The local subgroup inclusion uses the actual involution and the constructed maps. -/
theorem localIntoGenerated_range_le_generatedCentralizer :
    localIntoGenerated.range ≤ generatedCentralizer := localIntoGenerated_range_le_centralizer

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
