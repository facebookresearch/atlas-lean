/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionDestinations

/-! The two genuine uniform fibers behind the actual transition counting equations. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual local orbit map, with values in the proved signed-short axis set. -/
noncomputable def generatedAxisLocalLabelMap (p : Fin 276) (h : H) :
    generatedSignedShortAxes :=
  ⟨rhoLocal h (conwayAxis p), by
    rw [← generatedAxisLocalActual_orbit_eq_signed p]
    exact ⟨h, rfl⟩⟩

/-- The genuine local orbit map covers all actual signed-short axes. -/
theorem generatedAxisLocalLabelMap_surjective (p : Fin 276) :
    Function.Surjective (generatedAxisLocalLabelMap p) := by
  rintro ⟨x, hx⟩
  rw [← generatedAxisLocalActual_orbit_eq_signed p] at hx
  obtain ⟨h, hh⟩ := hx
  exact ⟨h, Subtype.ext hh⟩

/-- Each fiber of the actual local orbit map is equivalent to its actual axis stabilizer. -/
noncomputable def generatedAxisLocalLabelFiberEquiv (p : Fin 276)
    (x : generatedSignedShortAxes) :
    {h : H // generatedAxisLocalLabelMap p h = x} ≃ localAxisStabilizer p := by
  let a := Classical.choose (generatedAxisLocalLabelMap_surjective p x)
  have ha : generatedAxisLocalLabelMap p a = x :=
    Classical.choose_spec (generatedAxisLocalLabelMap_surjective p x)
  have hav : rhoLocal a (conwayAxis p) = x.val := congrArg Subtype.val ha
  refine
    { toFun := fun h => ⟨a⁻¹ * h.val, ?_⟩
      invFun := fun k => ⟨a * k.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · change rhoLocal (a⁻¹ * h.val) (conwayAxis p) = conwayAxis p
    rw [rhoLocal.map_mul]
    change rhoLocal a⁻¹ (rhoLocal h.val (conwayAxis p)) = conwayAxis p
    have hv : rhoLocal h.val (conwayAxis p) = x.val := congrArg Subtype.val h.property
    rw [hv, ← hav, rhoLocal.map_inv]
    exact (rhoLocal a).symm_apply_apply _
  · apply Subtype.ext
    change rhoLocal (a * k.val) (conwayAxis p) = x.val
    rw [rhoLocal.map_mul]
    change rhoLocal a (rhoLocal k.val (conwayAxis p)) = x.val
    rw [k.property, hav]
  · intro h
    apply Subtype.ext
    exact mul_inv_cancel_left _ _
  · intro k
    apply Subtype.ext
    exact inv_mul_cancel_left _ _

/-- Each genuine left Ω coset contains exactly a copy of the actual Ω subgroup. -/
noncomputable def generatedAxisTransitionCosetFiberEquiv
    (c : generatedAxisTransitionCosetSpace) :
    {h : H // Quotient.mk (QuotientGroup.rightRel localOmegaStabilizer) h = c} ≃
      localOmegaStabilizer := by
  let a : H := Quotient.out c
  have ha : Quotient.mk (QuotientGroup.rightRel localOmegaStabilizer) a = c :=
    Quotient.out_eq c
  refine
    { toFun := fun h => ⟨h.val * a⁻¹, ?_⟩
      invFun := fun n => ⟨n.val * a, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact QuotientGroup.rightRel_apply.mp (Quotient.exact' (ha.trans h.property.symm))
  · have he : Quotient.mk (QuotientGroup.rightRel localOmegaStabilizer) a =
        Quotient.mk (QuotientGroup.rightRel localOmegaStabilizer) (n.val * a) := by
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

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
