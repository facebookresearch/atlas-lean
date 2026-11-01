/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionFiberEquivalences

/-! Genuine transition counting equations for every actual local axis orbit.
The equalities use the actual local stabilizers and actual transition fibers;
no source table, prescribed orbit order, or global coverage is an input. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual local orbit map for an arbitrary vector. -/
noncomputable def generatedAxisGlobalLocalLabelMap (v : GriessSpace) (h : H) :
    MulAction.orbit H v := ⟨rhoLocal h v, h, rfl⟩

/-- Every actual local orbit point is attained by the local orbit map. -/
theorem generatedAxisGlobalLocalLabelMap_surjective (v : GriessSpace) :
    Function.Surjective (generatedAxisGlobalLocalLabelMap v) := by
  rintro ⟨x, h, hh⟩
  exact ⟨h, Subtype.ext hh⟩

/-- Every orbit-map fiber is genuinely a copy of the actual vector stabilizer. -/
noncomputable def generatedAxisGlobalLocalLabelFiberEquiv (v : GriessSpace)
    (x : MulAction.orbit H v) :
    {h : H // generatedAxisGlobalLocalLabelMap v h = x} ≃ MulAction.stabilizer H v := by
  let a := Classical.choose (generatedAxisGlobalLocalLabelMap_surjective v x)
  have ha := Classical.choose_spec (generatedAxisGlobalLocalLabelMap_surjective v x)
  have hav : rhoLocal a v = x.val := congrArg Subtype.val ha
  refine
    { toFun := fun h => ⟨a⁻¹ * h.val, ?_⟩
      invFun := fun k => ⟨a * k.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · change rhoLocal (a⁻¹ * h.val) v = v
    rw [rhoLocal.map_mul]
    change rhoLocal a⁻¹ (rhoLocal h.val v) = v
    have hv : rhoLocal h.val v = x.val := congrArg Subtype.val h.property
    rw [hv, ← hav, rhoLocal.map_inv]
    exact (rhoLocal a).symm_apply_apply _
  · apply Subtype.ext
    change rhoLocal (a * k.val) v = x.val
    rw [rhoLocal.map_mul]
    change rhoLocal a (rhoLocal k.val v) = x.val
    have hk : rhoLocal k.val v = v := k.property
    rw [hk, hav]
  · intro h
    apply Subtype.ext
    exact mul_inv_cancel_left _ _
  · intro k
    apply Subtype.ext
    exact inv_mul_cancel_left _ _

private noncomputable def globalTransitionUniformPreimageEquiv {α β γ : Type*}
    (f : α → β) (s : Set β) (hf : ∀ b, {a // f a = b} ≃ γ) :
    (f ⁻¹' s) ≃ s × γ := by
  let e : α ≃ β × γ := (Equiv.sigmaFiberEquiv f).symm.trans
    (Equiv.sigmaEquivProdOfEquiv hf)
  exact (Equiv.subtypeEquiv e (fun _ => Iff.rfl)).trans
    Equiv.prodSubtypeFstEquivSubtypeProd

private theorem globalTransitionUniformPreimageCard {α β γ : Type*}
    (f : α → β) (s : Set β) (hf : ∀ b, {a // f a = b} ≃ γ) :
    Nat.card (f ⁻¹' s) = Nat.card s * Nat.card γ := by
  rw [Nat.card_congr (globalTransitionUniformPreimageEquiv f s hf), Nat.card_prod]

/-- Actual points of a local orbit whose triality image has a specified actual local class. -/
noncomputable def generatedAxisGlobalTransitionAxisFiber (v : GriessSpace)
    (c : generatedAxisLocalOrbitSpace) : Set (MulAction.orbit H v) :=
  {x | Quotient.mk (MulAction.orbitRel H GriessSpace) (sExtra x.val) = c}

/-- The all-family transition equation follows from the two actual uniform
fibers, independently of all expected numerical stabilizer orders. -/
theorem generatedAxisGlobalTransition_fiber_balance (v : GriessSpace)
    (c : generatedAxisLocalOrbitSpace) :
    Nat.card (generatedAxisGlobalDestination v ⁻¹' {c}) * Nat.card localOmegaStabilizer =
      Nat.card (generatedAxisGlobalTransitionAxisFiber v c) *
        Nat.card (MulAction.stabilizer H v) := by
  have hcos := globalTransitionUniformPreimageCard
    (fun h : H => Quotient.mk (QuotientGroup.rightRel localOmegaStabilizer) h)
    (generatedAxisGlobalDestination v ⁻¹' {c}) generatedAxisTransitionCosetFiberEquiv
  have haxis := globalTransitionUniformPreimageCard (generatedAxisGlobalLocalLabelMap v)
    (generatedAxisGlobalTransitionAxisFiber v c) (generatedAxisGlobalLocalLabelFiberEquiv v)
  have hs : (fun h : H => Quotient.mk (QuotientGroup.rightRel localOmegaStabilizer) h) ⁻¹'
      (generatedAxisGlobalDestination v ⁻¹' {c}) =
        generatedAxisGlobalLocalLabelMap v ⁻¹' generatedAxisGlobalTransitionAxisFiber v c := by
    ext h
    rfl
  rw [hs] at hcos
  exact hcos.symm.trans haxis

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
