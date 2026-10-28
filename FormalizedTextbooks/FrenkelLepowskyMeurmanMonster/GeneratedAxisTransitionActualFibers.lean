/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionReversibility

/-! Actual triality destination fibers for every local vector orbit, with uniform-fiber balance. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every genuine vector defines a destination map on the actual transition cosets. -/
def generatedAxisActualTransitionDestination (a : GriessSpace) :
    generatedAxisTransitionCosetSpace → generatedAxisLocalOrbitSpace :=
  Quotient.lift
    (fun h : H => Quotient.mk (MulAction.orbitRel H GriessSpace) (sExtra (rhoLocal h a)))
    (by
      intro u v huv
      have hn : v * u⁻¹ ∈ localOmegaStabilizer := QuotientGroup.rightRel_apply.mp huv
      obtain ⟨h, hh⟩ := localOmegaStabilizer_triality_orbit ⟨v * u⁻¹, hn⟩ (rhoLocal u a)
      apply Quotient.sound'
      rw [MulAction.orbitRel_apply]
      apply MulAction.mem_orbit_symm.mp
      refine ⟨h, ?_⟩
      change rhoLocal h (sExtra (rhoLocal u a)) = sExtra (rhoLocal v a)
      rw [hh]
      apply congrArg sExtra
      rw [← LinearEquiv.mul_apply, ← rhoLocal.map_mul, inv_mul_cancel_right])

/-- Genuine transition cosets taking the local orbit of a to the local orbit of b. -/
def generatedAxisActualTransitionCosets (a b : GriessSpace) :
    Set generatedAxisTransitionCosetSpace :=
  generatedAxisActualTransitionDestination a ⁻¹'
    {Quotient.mk (MulAction.orbitRel H GriessSpace) b}

/-- The actual H orbit map, with its genuine orbit subtype as codomain. -/
def generatedAxisActualOrbitMap (a : GriessSpace) (h : H) : MulAction.orbit H a :=
  ⟨rhoLocal h a, ⟨h, rfl⟩⟩

/-- Every point of the actual H orbit is reached by the actual H orbit map. -/
theorem generatedAxisActualOrbitMap_surjective (a : GriessSpace) :
    Function.Surjective (generatedAxisActualOrbitMap a) := by
  rintro ⟨x, hx⟩
  obtain ⟨h, hh⟩ := hx
  exact ⟨h, Subtype.ext hh⟩

/-- Each actual orbit-map fiber is a copy of the genuine point stabilizer. -/
def generatedAxisActualOrbitFiberEquiv (a : GriessSpace) (x : MulAction.orbit H a) :
    {h : H // generatedAxisActualOrbitMap a h = x} ≃ MulAction.stabilizer H a := by
  let u := Classical.choose (generatedAxisActualOrbitMap_surjective a x)
  have hu : generatedAxisActualOrbitMap a u = x :=
    Classical.choose_spec (generatedAxisActualOrbitMap_surjective a x)
  have huv : rhoLocal u a = x.val := congrArg Subtype.val hu
  refine
    { toFun := fun h => ⟨u⁻¹ * h.val, ?_⟩
      invFun := fun g => ⟨u * g.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · change rhoLocal (u⁻¹ * h.val) a = a
    rw [rhoLocal.map_mul]
    change rhoLocal u⁻¹ (rhoLocal h.val a) = a
    have hv : rhoLocal h.val a = x.val := congrArg Subtype.val h.property
    rw [hv, ← huv, rhoLocal.map_inv]
    exact (rhoLocal u).symm_apply_apply _
  · apply Subtype.ext
    change rhoLocal (u * g.val) a = x.val
    rw [rhoLocal.map_mul]
    change rhoLocal u (rhoLocal g.val a) = x.val
    have hg : rhoLocal g.val a = a := g.property
    rw [hg, huv]
  · intro h
    apply Subtype.ext
    exact mul_inv_cancel_left _ _
  · intro g
    apply Subtype.ext
    exact inv_mul_cancel_left _ _

private def generatedAxisActualTransitionOrbitFiber (a b : GriessSpace) :
    Set (MulAction.orbit H a) := {x | sExtra x.val ∈ MulAction.orbit H b}

private def generatedAxisActualTransitionVectorEquiv (a b : GriessSpace) :
    generatedAxisActualTransitionOrbitFiber a b ≃ generatedAxisTransitionVectors a b where
  toFun x := ⟨x.val.val, x.val.property, x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def generatedAxisActualUniformPreimageEquiv {α β γ : Type*}
    (f : α → β) (s : Set β) (hf : ∀ b, {a // f a = b} ≃ γ) :
    (f ⁻¹' s) ≃ s × γ := by
  let e : α ≃ β × γ := (Equiv.sigmaFiberEquiv f).symm.trans
    (Equiv.sigmaEquivProdOfEquiv hf)
  exact (Equiv.subtypeEquiv e (fun _ => Iff.rfl)).trans
    Equiv.prodSubtypeFstEquivSubtypeProd

private theorem generatedAxisActualUniformPreimageCard {α β γ : Type*}
    (f : α → β) (s : Set β) (hf : ∀ b, {a // f a = b} ≃ γ) :
    Nat.card (f ⁻¹' s) = Nat.card s * Nat.card γ := by
  rw [Nat.card_congr (generatedAxisActualUniformPreimageEquiv f s hf), Nat.card_prod]

/-- Every actual local-orbit transition satisfies the genuine vector/coset balance. -/
theorem generatedAxisActualTransition_fiber_balance (a b : GriessSpace) :
    Nat.card (generatedAxisActualTransitionCosets a b) * Nat.card localOmegaStabilizer =
      Nat.card (generatedAxisTransitionVectors a b) * Nat.card (MulAction.stabilizer H a) := by
  have hcos := generatedAxisActualUniformPreimageCard
    (fun h : H => Quotient.mk (QuotientGroup.rightRel localOmegaStabilizer) h)
    (generatedAxisActualTransitionCosets a b) generatedAxisTransitionCosetFiberEquiv
  have horb := generatedAxisActualUniformPreimageCard (generatedAxisActualOrbitMap a)
    (generatedAxisActualTransitionOrbitFiber a b) (generatedAxisActualOrbitFiberEquiv a)
  have hs : (fun h : H => Quotient.mk (QuotientGroup.rightRel localOmegaStabilizer) h) ⁻¹'
      generatedAxisActualTransitionCosets a b =
        generatedAxisActualOrbitMap a ⁻¹' generatedAxisActualTransitionOrbitFiber a b := by
    ext h
    constructor
    · intro hc
      have hc' : Quotient.mk (MulAction.orbitRel H GriessSpace) (sExtra (rhoLocal h a)) =
          Quotient.mk (MulAction.orbitRel H GriessSpace) b := hc
      exact MulAction.orbitRel_apply.mp (Quotient.exact' hc')
    · intro hc
      have hc' : sExtra (rhoLocal h a) ∈ MulAction.orbit H b := hc
      exact Quotient.sound' (MulAction.orbitRel_apply.mpr hc')
  rw [hs] at hcos
  rw [Nat.card_congr (generatedAxisActualTransitionVectorEquiv a b)] at horb
  exact hcos.symm.trans horb

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
