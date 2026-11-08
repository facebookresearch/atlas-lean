/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.GroupAction.FixedPoints

@[expose] public section

/-!
# Poles of a group action

A pole of a group action is a point fixed by some nonidentity element of the
group. The group action permutes the set of poles: acting by `g` sends a pole
to a pole, since the stabilizer of `g • p` is the conjugate of the stabilizer
of `p`.

Source: `v1/Atlas/AlgebraNotes/code/SylowTheorems.lean`
(`SylowTheorems.poles`, `SylowTheorems.smul_mem_poles`, fully proved there),
formalizing a lemma used in the book's proof of the Sylow theorems (Proofs and
Applications of the Sylow Theorems, Section on Stabilizer): if `p` is a pole
and `g` is in `G`, then `g • p` is a pole.

## Main results

* `MulAction.poles`: the set of poles of a group action.
* `MulAction.smul_mem_poles`: the action sends poles to poles.
* `MulAction.image_smul_poles`: the action by any `g` permutes the set of poles.
* `MulAction.poles_eq_iUnion_fixedBy`: the poles are the union of the fixed-point
  sets of the nonidentity elements.
-/

namespace MulAction

variable {G X : Type*} [Group G] [MulAction G X]

/-- A pole of a group action is a point fixed by some nonidentity element. -/
def poles (G : Type*) (X : Type*) [Group G] [MulAction G X] : Set X :=
  {x : X | ∃ g : G, g ≠ 1 ∧ g • x = x}

/-- Membership in the poles unfolds to the defining condition. -/
theorem mem_poles {p : X} : p ∈ poles G X ↔ ∃ g : G, g ≠ 1 ∧ g • p = p :=
  Iff.rfl

/-- The group action sends poles to poles: if `p` is fixed by some
nonidentity `h`, then `g • p` is fixed by the conjugate `g * h * g⁻¹`. -/
theorem smul_mem_poles (g : G) {p : X} (hp : p ∈ poles G X) :
    g • p ∈ poles G X := by
  obtain ⟨h, hne, hfix⟩ := hp
  refine ⟨g * h * g⁻¹, ?_, ?_⟩
  · intro heq
    apply hne
    have hconj : h = g⁻¹ * (g * h * g⁻¹) * g := by simp [mul_assoc]
    rw [hconj, heq, mul_one, inv_mul_cancel]
  · calc (g * h * g⁻¹) • (g • p)
        = g • (h • (g⁻¹ • (g • p))) := by rw [mul_smul, mul_smul]
      _ = g • (h • p) := by rw [inv_smul_smul]
      _ = g • p := by rw [hfix]

/-- Acting by any `g` permutes the set of poles. -/
theorem image_smul_poles (g : G) : (g • ·) '' poles G X = poles G X := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact smul_mem_poles g hy
  · intro hx
    exact ⟨g⁻¹ • x, smul_mem_poles g⁻¹ hx, smul_inv_smul g x⟩

/-- The poles are the union of the fixed-point sets of the nonidentity elements. -/
theorem poles_eq_iUnion_fixedBy :
    poles G X = ⋃ g ∈ {g : G | g ≠ 1}, MulAction.fixedBy X g := by
  ext p
  constructor
  · rintro ⟨g, hg, hfix⟩
    exact Set.mem_iUnion₂.mpr ⟨g, hg, MulAction.mem_fixedBy.mpr hfix⟩
  · intro hp
    obtain ⟨g, hg, hfix⟩ := Set.mem_iUnion₂.mp hp
    exact ⟨g, hg, MulAction.mem_fixedBy.mp hfix⟩

end MulAction

end
