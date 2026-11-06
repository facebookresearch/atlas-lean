/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionFiberEquivalences

/-! Genuine vector/coset transition balance, before any source orbit classification. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private noncomputable def uniformFiberPreimageEquiv {α β γ : Type*}
    (f : α → β) (s : Set β) (hf : ∀ b, {a // f a = b} ≃ γ) :
    (f ⁻¹' s) ≃ s × γ := by
  let e : α ≃ β × γ := (Equiv.sigmaFiberEquiv f).symm.trans
    (Equiv.sigmaEquivProdOfEquiv hf)
  exact (Equiv.subtypeEquiv e (fun _ => Iff.rfl)).trans
    Equiv.prodSubtypeFstEquivSubtypeProd

private theorem uniformFiberPreimage_card {α β γ : Type*}
    (f : α → β) (s : Set β)
    (hf : ∀ b, {a // f a = b} ≃ γ) :
    Nat.card (f ⁻¹' s) = Nat.card s * Nat.card γ := by
  rw [Nat.card_congr (uniformFiberPreimageEquiv f s hf), Nat.card_prod]

/-- Actual first-orbit axes whose genuine triality image has the specified actual local class. -/
noncomputable def generatedAxisTransitionAxisFiber (c : generatedAxisLocalOrbitSpace) :
    Set generatedSignedShortAxes :=
  {x | Quotient.mk (MulAction.orbitRel H GriessSpace) (sExtra x.val) = c}

/-- The actual transition counting equation comes from two genuine uniform group fibers.
The local class is an actual orbit, with no prescribed classification label or table entry. -/
theorem generatedAxisTransition_fiber_balance (p : Fin 276)
    (c : generatedAxisLocalOrbitSpace) :
    Nat.card (generatedAxisTransitionDestination p ⁻¹' {c}) * Nat.card localOmegaStabilizer =
      Nat.card (generatedAxisTransitionAxisFiber c) * Nat.card (localAxisStabilizer p) := by
  have hcos := uniformFiberPreimage_card
    (fun h : H => Quotient.mk (QuotientGroup.rightRel localOmegaStabilizer) h)
    (generatedAxisTransitionDestination p ⁻¹' {c}) generatedAxisTransitionCosetFiberEquiv
  have haxis := uniformFiberPreimage_card (generatedAxisLocalLabelMap p)
    (generatedAxisTransitionAxisFiber c) (generatedAxisLocalLabelFiberEquiv p)
  have hs : (fun h : H => Quotient.mk (QuotientGroup.rightRel localOmegaStabilizer) h) ⁻¹'
      (generatedAxisTransitionDestination p ⁻¹' {c}) =
        generatedAxisLocalLabelMap p ⁻¹' generatedAxisTransitionAxisFiber c := by
    ext h
    rfl
  rw [hs] at hcos
  exact hcos.symm.trans haxis

/-- With the proved actual group orders, the vector/coset balance has ratio 675/8. -/
theorem generatedAxisTransition_fiber_balance_normalized (p : Fin 276)
    (c : generatedAxisLocalOrbitSpace) :
    8 * Nat.card (generatedAxisTransitionDestination p ⁻¹' {c}) =
      675 * Nat.card (generatedAxisTransitionAxisFiber c) := by
  have h := generatedAxisTransition_fiber_balance p c
  have hn : Nat.card localOmegaStabilizer = 8412055600858398720 := by
    rw [localOmegaStabilizer_card, co1OmegaFrameStabilizer_card]
    norm_num
  have ha : Nat.card (localAxisStabilizer p) = 709767191322427392000 := by
    rw [localAxisStabilizer_card, co2Short_card_exact]
    norm_num
  rw [hn, ha] at h
  have he : (8 * Nat.card (generatedAxisTransitionDestination p ⁻¹' {c})) *
      1051506950107299840 =
        (675 * Nat.card (generatedAxisTransitionAxisFiber c)) * 1051506950107299840 := by
    calc
      _ = Nat.card (generatedAxisTransitionDestination p ⁻¹' {c}) * 8412055600858398720 := by ring
      _ = _ := h
      _ = _ := by ring
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 1051506950107299840) he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
