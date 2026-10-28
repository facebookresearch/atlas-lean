/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Genuine source lines are checked against generators of the full actual base-point two-core. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometrySignGeneration
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryLines

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Actual Conway operators preserving both members of a fixed source-point pair. -/
def monsterCo1GeometryPairPreserver (q r : MonsterCo1GeometryPoint) : Submonoid Co1 where
  carrier := {g | ∀ p ∈ ({q, r} : Set MonsterCo1GeometryPoint),
    g • p ∈ ({q, r} : Set MonsterCo1GeometryPoint)}
  one_mem' := by intro p hp; simpa only [one_smul] using hp
  mul_mem' := by
    intro g h hg hh p hp
    simpa only [mul_smul] using hg _ (hh p hp)

/-- Checking all twelve actual generators checks every element of the intrinsic two-core. -/
theorem monsterCo1GeometryPairPreserver_twoCore (q r : MonsterCo1GeometryPoint)
    (h : ∀ k : Fin 12, monsterCo1GeometryBasisSignClass k ∈
      monsterCo1GeometryPairPreserver q r) :
    ∀ g ∈ monsterCo1GeometryPointTwoCore monsterCo1GeometryBasePoint,
      g ∈ monsterCo1GeometryPairPreserver q r := by
  have : Finite Co1 := co1_finite
  have hc : Submonoid.closure (Set.range monsterCo1GeometryBasisSignClass) ≤
      monsterCo1GeometryPairPreserver q r := by
    apply Submonoid.closure_le.mpr
    rintro g ⟨k, rfl⟩
    exact h k
  rw [← Subgroup.closure_toSubmonoid_of_finite,
    monsterCo1GeometryBasisSignClass_closure] at hc
  exact fun g hg => hc hg

/-- A distinct pair preserved by all actual two-core generators, with one swapping witness,
is exactly a genuine length-two orbit, as required by the original source presentation. -/
theorem monsterCo1GeometryAnchoredLine_of_basis_signs (q r : MonsterCo1GeometryPoint)
    (hbq : monsterCo1GeometryBasePoint ≠ q) (hbr : monsterCo1GeometryBasePoint ≠ r)
    (hqr : q ≠ r)
    (hp : ∀ k : Fin 12, monsterCo1GeometryBasisSignClass k ∈
      monsterCo1GeometryPairPreserver q r)
    (hw : ∃ k : Fin 12, monsterCo1GeometryBasisSignClass k • q = r) :
    monsterCo1GeometryAnchoredLine monsterCo1GeometryBasePoint q r := by
  refine ⟨hbq, hbr, hqr, ?_⟩
  apply Set.Subset.antisymm
  · rintro p ⟨g, rfl⟩
    exact monsterCo1GeometryPairPreserver_twoCore q r hp g.val g.property q (by simp)
  · intro p hpq
    rcases hpq with rfl | hpq
    · exact ⟨1, one_smul _ _⟩
    · obtain ⟨k, hk⟩ := hw
      have hg := monsterCo1GeometrySign_mem_baseTwoCore k
      refine ⟨⟨monsterCo1GeometryBasisSignClass k, hg⟩, ?_⟩
      change monsterCo1GeometryBasisSignClass k • q = p
      exact hk.trans (Set.mem_singleton_iff.mp hpq).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
