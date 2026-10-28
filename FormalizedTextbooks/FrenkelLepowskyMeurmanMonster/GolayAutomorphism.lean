/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayCode
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-! Genuine coordinate-permutation automorphisms of the published Golay code.
The subgroup is defined by preservation of the actual encoder range. No group
order, transitivity, or stabilizer size is included in its definition. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The twelve coefficient bits enumerate the actual encoder range bijectively. -/
noncomputable def golayCodeEquiv : (Fin 12 → ZMod 2) ≃ ↥golayCode :=
  (LinearEquiv.ofInjective golayEncoder golayEncoder_injective).toEquiv

theorem golayCode_card : Nat.card golayCode = 4096 := by
  rw [← Nat.card_congr golayCodeEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

/-- Relabeling coordinates by a permutation, with the usual left-action convention. -/
def golayPermute (p : Equiv.Perm (Fin 24)) (c : Fin 24 → ZMod 2) :
    Fin 24 → ZMod 2 := fun i => c (p.symm i)

@[simp] theorem golayPermute_one (c : Fin 24 → ZMod 2) : golayPermute 1 c = c := rfl

@[simp] theorem golayPermute_mul (p q : Equiv.Perm (Fin 24)) (c : Fin 24 → ZMod 2) :
    golayPermute (p * q) c = golayPermute p (golayPermute q c) := rfl

@[simp] theorem golayPermute_inv (p : Equiv.Perm (Fin 24)) (c : Fin 24 → ZMod 2) :
    golayPermute p⁻¹ (golayPermute p c) = c := by
  funext i
  change c (p.symm (p i)) = c i
  rw [p.symm_apply_apply]

/-- The actual permutation automorphism group of the binary Golay code. -/
def golayAutomorphismSubgroup : Subgroup (Equiv.Perm (Fin 24)) where
  carrier := {p | ∀ c, c ∈ golayCode ↔ golayPermute p c ∈ golayCode}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := by
    intro p q hp hq c
    rw [golayPermute_mul]
    exact (hq c).trans (hp (golayPermute q c))
  inv_mem' := by
    intro p hp c
    have h := hp (golayPermute p⁻¹ c)
    rw [← golayPermute_mul, mul_inv_cancel, golayPermute_one] at h
    exact h.symm

/-- Finiteness comes from the ambient finite permutation group. -/
theorem golayAutomorphism_finite : Finite golayAutomorphismSubgroup := by
  infer_instance

set_option maxHeartbeats 4000000 in
-- Check all pairs of the 24 coordinate columns against the twelve generator rows.
/-- The code action is faithful: its range contains words separating every pair
of coordinates. This finite prerequisite is verified against the generator table. -/
theorem golayGenerators_separate_coordinates : ∀ i j : Fin 24, i ≠ j →
    ∃ k : Fin 12, (golayGeneratorBit k i : ZMod 2) ≠
      (golayGeneratorBit k j : ZMod 2) := by
  decide +kernel

/-- A generator row is genuinely in the linear code defined by the encoder. -/
theorem golayGenerator_mem (k : Fin 12) :
    (fun i => (golayGeneratorBit k i : ZMod 2)) ∈ golayCode := by
  refine ⟨Pi.single k 1, ?_⟩
  ext i
  simp [golayEncoder, Pi.single_apply, ite_mul]

/-- Acting on actual Golay words distinguishes all coordinate automorphisms. -/
theorem golayAutomorphism_code_action_injective : Function.Injective
    (fun p : golayAutomorphismSubgroup => fun c : golayCode => golayPermute p.val c.val) := by
  intro p q hpq
  apply Subtype.ext
  have h : p.val.symm = q.val.symm := by
    apply Equiv.ext
    intro i
    by_contra hi
    obtain ⟨k, hk⟩ := golayGenerators_separate_coordinates (p.val.symm i) (q.val.symm i) hi
    have hh := congrFun (congrFun hpq
      ⟨fun j => (golayGeneratorBit k j : ZMod 2), golayGenerator_mem k⟩) i
    exact hk hh
  simpa using congrArg Equiv.symm h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
