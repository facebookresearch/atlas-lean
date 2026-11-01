/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
    FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleTransitionReversibility

/-! Actual feasible vector and transition coset fibers have uniform stabilizer sizes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
variable (p : Fin 276)

/-- The original local representation restricted to the actual pair-axis stabilizer. -/
def generatedFeasibleLocalRepresentation :
    localAxisStabilizer p →* (GriessSpace ≃ₗ[ℝ] GriessSpace) :=
  rhoLocal.comp (localAxisStabilizer p).subtype

/-- Every actual feasible transition coset is a copy of the genuine transition subgroup. -/
def generatedFeasibleTransitionCosetFiberEquiv
    (c : generatedFeasibleTransitionCosetSpace p) :
    {h : localAxisStabilizer p //
      Quotient.mk (QuotientGroup.rightRel (localFeasibleTransitionSubgroup p)) h = c} ≃
      localFeasibleTransitionSubgroup p := by
  let a : localAxisStabilizer p := Quotient.out c
  have ha : Quotient.mk (QuotientGroup.rightRel (localFeasibleTransitionSubgroup p)) a = c :=
    Quotient.out_eq c
  refine
    { toFun := fun h => ⟨h.val * a⁻¹, ?_⟩
      invFun := fun n => ⟨n.val * a, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact QuotientGroup.rightRel_apply.mp (Quotient.exact' (ha.trans h.property.symm))
  · have he : Quotient.mk (QuotientGroup.rightRel (localFeasibleTransitionSubgroup p)) a =
        Quotient.mk (QuotientGroup.rightRel (localFeasibleTransitionSubgroup p)) (n.val * a) := by
      apply Quotient.sound'
      rw [QuotientGroup.rightRel_apply, mul_inv_cancel_right]
      exact n.property
    exact he.symm.trans ha
  · intro h
    apply Subtype.ext
    exact inv_mul_cancel_right _ _
  · intro n
    apply Subtype.ext
    exact mul_inv_cancel_right _ _

/-- Genuine transition cosets taking the local orbit of a to the local orbit of b. -/
def generatedFeasibleActualTransitionCosets (a b : GriessSpace) :
    Set (generatedFeasibleTransitionCosetSpace p) :=
  generatedFeasibleTransitionDestination p a ⁻¹'
    {Quotient.mk (MulAction.orbitRel (localAxisStabilizer p) GriessSpace) b}

/-- The genuine orbit map of the actual first-axis stabilizer. -/
def generatedFeasibleActualOrbitMap (a : GriessSpace) (h : localAxisStabilizer p) :
    MulAction.orbit (localAxisStabilizer p) a :=
  ⟨(generatedFeasibleLocalRepresentation p) h a, ⟨h, rfl⟩⟩

/-- The genuine local orbit map reaches every vector of its actual orbit. -/
theorem generatedFeasibleActualOrbitMap_surjective (a : GriessSpace) :
    Function.Surjective (generatedFeasibleActualOrbitMap p a) := by
  rintro ⟨x, hx⟩
  obtain ⟨h, hh⟩ := hx
  exact ⟨h, Subtype.ext hh⟩

/-- Each actual orbit-map fiber is a copy of the genuine point stabilizer. -/
def generatedFeasibleActualOrbitFiberEquiv (a : GriessSpace) (x : MulAction.orbit
    (localAxisStabilizer p) a) :
    {h : (localAxisStabilizer p) // generatedFeasibleActualOrbitMap p a h = x} ≃
        MulAction.stabilizer (localAxisStabilizer p) a := by
  let u := Classical.choose (generatedFeasibleActualOrbitMap_surjective p a x)
  have hu : generatedFeasibleActualOrbitMap p a u = x :=
    Classical.choose_spec (generatedFeasibleActualOrbitMap_surjective p a x)
  have huv : (generatedFeasibleLocalRepresentation p) u a = x.val := congrArg Subtype.val hu
  refine
    { toFun := fun h => ⟨u⁻¹ * h.val, ?_⟩
      invFun := fun g => ⟨u * g.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · change (generatedFeasibleLocalRepresentation p) (u⁻¹ * h.val) a = a
    rw [(generatedFeasibleLocalRepresentation p).map_mul]
    change (generatedFeasibleLocalRepresentation p) u⁻¹ ((generatedFeasibleLocalRepresentation
        p) h.val a) = a
    have hv : (generatedFeasibleLocalRepresentation p) h.val a = x.val := congrArg Subtype.val
        h.property
    rw [hv, ← huv, (generatedFeasibleLocalRepresentation p).map_inv]
    exact ((generatedFeasibleLocalRepresentation p) u).symm_apply_apply _
  · apply Subtype.ext
    change (generatedFeasibleLocalRepresentation p) (u * g.val) a = x.val
    rw [(generatedFeasibleLocalRepresentation p).map_mul]
    change (generatedFeasibleLocalRepresentation p) u ((generatedFeasibleLocalRepresentation p)
        g.val a) = x.val
    have hg : (generatedFeasibleLocalRepresentation p) g.val a = a := g.property
    rw [hg, huv]
  · intro h
    apply Subtype.ext
    exact mul_inv_cancel_left _ _
  · intro g
    apply Subtype.ext
    exact inv_mul_cancel_left _ _

private def generatedFeasibleActualTransitionOrbitFiber (a b : GriessSpace) :
    Set (MulAction.orbit (localAxisStabilizer p) a) := {x | sExtra x.val ∈ MulAction.orbit
        (localAxisStabilizer p) b}

private def generatedFeasibleActualTransitionVectorEquiv (a b : GriessSpace) :
    generatedFeasibleActualTransitionOrbitFiber p a b ≃ generatedFeasibleTransitionVectors p a
        b where
  toFun x := ⟨x.val.val, x.val.property, x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def generatedFeasibleActualUniformPreimageEquiv {α β γ : Type*}
    (f : α → β) (s : Set β) (hf : ∀ b, {a // f a = b} ≃ γ) :
    (f ⁻¹' s) ≃ s × γ := by
  let e : α ≃ β × γ := (Equiv.sigmaFiberEquiv f).symm.trans
    (Equiv.sigmaEquivProdOfEquiv hf)
  exact (Equiv.subtypeEquiv e (fun _ => Iff.rfl)).trans
    Equiv.prodSubtypeFstEquivSubtypeProd

private theorem generatedFeasibleActualUniformPreimageCard {α β γ : Type*}
    (f : α → β) (s : Set β) (hf : ∀ b, {a // f a = b} ≃ γ) :
    Nat.card (f ⁻¹' s) = Nat.card s * Nat.card γ := by
  rw [Nat.card_congr (generatedFeasibleActualUniformPreimageEquiv f s hf), Nat.card_prod]

/-- Every actual local-orbit transition satisfies the genuine vector/coset balance. -/
theorem generatedFeasibleActualTransition_fiber_balance (a b : GriessSpace) :
    Nat.card (generatedFeasibleActualTransitionCosets p a b) * Nat.card
        (localFeasibleTransitionSubgroup p) =
      Nat.card (generatedFeasibleTransitionVectors p a b) * Nat.card (MulAction.stabilizer
          (localAxisStabilizer p) a) := by
  have hcos := generatedFeasibleActualUniformPreimageCard
    (fun h : (localAxisStabilizer p) => Quotient.mk (QuotientGroup.rightRel
        (localFeasibleTransitionSubgroup p)) h)
    (generatedFeasibleActualTransitionCosets p a b) (generatedFeasibleTransitionCosetFiberEquiv p)
  have horb := generatedFeasibleActualUniformPreimageCard (generatedFeasibleActualOrbitMap p a)
    (generatedFeasibleActualTransitionOrbitFiber p a b) (generatedFeasibleActualOrbitFiberEquiv p a)
  have hs : (fun h : (localAxisStabilizer p) => Quotient.mk (QuotientGroup.rightRel
      (localFeasibleTransitionSubgroup p)) h) ⁻¹'
      generatedFeasibleActualTransitionCosets p a b =
        generatedFeasibleActualOrbitMap p a ⁻¹' generatedFeasibleActualTransitionOrbitFiber p a
            b := by
    ext h
    constructor
    · intro hc
      have hc' : Quotient.mk (MulAction.orbitRel (localAxisStabilizer p) GriessSpace) (sExtra
          ((generatedFeasibleLocalRepresentation p) h a)) =
          Quotient.mk (MulAction.orbitRel (localAxisStabilizer p) GriessSpace) b := hc
      exact MulAction.orbitRel_apply.mp (Quotient.exact' hc')
    · intro hc
      have hc' : sExtra ((generatedFeasibleLocalRepresentation p) h a) ∈ MulAction.orbit
          (localAxisStabilizer p) b := hc
      exact Quotient.sound' (MulAction.orbitRel_apply.mpr hc')
  rw [hs] at hcos
  rw [Nat.card_congr (generatedFeasibleActualTransitionVectorEquiv p a b)] at horb
  exact hcos.symm.trans horb

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
