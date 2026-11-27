/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.FrattiniCenterFirstCohomologyKourovka17Problem2
import Mathlib.Algebra.Group.PUnit

@[expose] public section

/-!
# Tests for vanishing `H¹(G/Φ(G), Z(Φ(G)))` (Kourovka Notebook Problem 17.2)

Exercises the proved statement `nonabelianPGroupFrattiniCenterH1Trivial_holds`, the
`InFrattiniCenter` predicate at the identity, and the `FrattiniCenterH1Trivial` property on the
trivial group.
-/

open MathlibExt.GroupTheory.FrattiniCenterFirstCohomologyKourovka17Problem2Wanted

/-- The proved statement has the stated type. -/
example : nonabelianPGroupFrattiniCenterH1Trivial :=
  nonabelianPGroupFrattiniCenterH1Trivial_holds

-- On the witness group, every inflated cocycle vanishes on the whole centre.
example : ∃ (p : ℕ) (G : Type) (_ : Group G) (_ : Finite G), p.Prime ∧ IsPGroup p G ∧
    (∃ a b : G, a * b ≠ b * a) ∧ ∀ δ : G → G, (∀ g, InFrattiniCenter (δ g)) →
      (∀ g h, δ (g * h) = δ g * (g * δ h * g⁻¹)) → (∀ g ∈ frattini G, δ g = 1) →
      ∀ g ∈ Subgroup.center G, δ g = 1 := by
  obtain ⟨p, G, inst, fin, hp, hG, hab, hH1⟩ := nonabelianPGroupFrattiniCenterH1Trivial_holds
  refine ⟨p, G, inst, fin, hp, hG, hab, ?_⟩
  intro δ hcen hcoc hφ g hg
  obtain ⟨a, _, ha⟩ := hH1 δ hcen hcoc hφ
  rw [ha, ← Subgroup.mem_center_iff.mp hg a]
  simp [mul_assoc]

/-- The identity lies in the centre of the Frattini subgroup of any group. -/
example {G : Type*} [Group G] : InFrattiniCenter (1 : G) :=
  ⟨Subgroup.one_mem _, fun y _ => by simp⟩

/-- The first cohomology property holds for the trivial group. -/
example : FrattiniCenterH1Trivial PUnit := by
  intro δ hcen hcoc hφ
  refine ⟨1, ?_, fun g => ?_⟩
  · exact ⟨Subgroup.one_mem _, fun y _ => by simp⟩
  · have h1 : δ g = 1 := Subsingleton.elim _ _
    have h2 : g * (1 : PUnit) * g⁻¹ * (1 : PUnit)⁻¹ = 1 := Subsingleton.elim _ _
    rw [h1, h2]
