/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The genuine source two-orbit line relation is preserved by the actual Conway action. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryConjugation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryLines

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Actual point two-core orbits transport by literal Conway conjugation. -/
theorem monsterCo1GeometryPointTwoCore_orbit_transport (g : Co1)
    (p q r : MonsterCo1GeometryPoint) :
    g • r ∈ MulAction.orbit (monsterCo1GeometryPointTwoCore (g • p)) (g • q) ↔
      r ∈ MulAction.orbit (monsterCo1GeometryPointTwoCore p) q := by
  rw [monsterCo1GeometryPointTwoCore_conjugation]
  constructor
  · rintro ⟨h, hh⟩
    obtain ⟨k, hk, he⟩ := h.property
    refine ⟨⟨k, hk⟩, ?_⟩
    change k • q = r
    have hv : h.val = g * k * g⁻¹ := he.symm
    change h.val • (g • q) = g • r at hh
    rw [hv] at hh
    simpa only [mul_smul, inv_smul_smul, smul_left_cancel_iff] using hh
  · rintro ⟨k, hk⟩
    change k.val • q = r at hk
    refine ⟨⟨g * k.val * g⁻¹, ?_⟩, ?_⟩
    · exact ⟨k.val, k.property, rfl⟩
    · change (g * k.val * g⁻¹) • (g • q) = g • r
      simpa only [mul_smul, inv_smul_smul] using congrArg (fun x => g • x) hk

/-- Every original two-orbit anchored line remains a genuine anchored line under Conway action. -/
theorem monsterCo1GeometryAnchoredLine_smul (g : Co1)
    (p q r : MonsterCo1GeometryPoint) (h : monsterCo1GeometryAnchoredLine p q r) :
    monsterCo1GeometryAnchoredLine (g • p) (g • q) (g • r) := by
  refine ⟨(MulAction.injective g).ne h.1, (MulAction.injective g).ne h.2.1,
    (MulAction.injective g).ne h.2.2.1, ?_⟩
  ext x
  have hx : x = g • (g⁻¹ • x) := (smul_inv_smul g x).symm
  rw [hx, monsterCo1GeometryPointTwoCore_orbit_transport, h.2.2.2]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, smul_left_cancel_iff]

/-- The unordered original source line relation is invariant under the actual Conway group. -/
theorem monsterCo1GeometryLine_smul (g : Co1) (p q r : MonsterCo1GeometryPoint)
    (h : monsterCo1GeometryLine p q r) :
    monsterCo1GeometryLine (g • p) (g • q) (g • r) := by
  rcases h with hp | hq | hr
  · exact Or.inl (monsterCo1GeometryAnchoredLine_smul g p q r hp)
  · exact Or.inr (Or.inl (monsterCo1GeometryAnchoredLine_smul g q p r hq))
  · exact Or.inr (Or.inr (monsterCo1GeometryAnchoredLine_smul g r p q hr))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
