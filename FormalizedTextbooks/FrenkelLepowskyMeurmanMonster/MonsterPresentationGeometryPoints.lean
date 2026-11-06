/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual 2B points and extraspecial incidence for the Ivanov–Shpectorov representation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOrderCounting
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerRecognition
public import Mathlib.Tactic.Group

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Points are the actual conjugates of the distinguished central involution in G.
See Ivanov–Shpectorov, Geometry of Sporadic Groups II, §§7.1–7.2. -/
abbrev MonsterGeometryPoint :=
  {p : G // IsConj generatedCentralInvolution p}

/-- The actual geometry has a finite point set by the proved Griess-product finiteness result. -/
theorem monsterGeometryPoints_finite : Finite MonsterGeometryPoint := by
  have : Finite G := generated_group_finite_of_triality_product sExtra_preserves_griessProd
  infer_instance

/-- The actual distinguished point, without an abstract Monster identification. -/
noncomputable def monsterGeometryBasePoint : MonsterGeometryPoint :=
  ⟨generatedCentralInvolution, IsConj.refl _⟩

/-- The source point set agrees with the previously defined actual conjugacy orbit. -/
theorem monsterGeometryPoint_mem_iff_orbit (p : G) :
    IsConj generatedCentralInvolution p ↔ p ∈ generatedCentralOrbit := by
  rw [isConj_iff, generatedCentralOrbit, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨ConjAct.toConjAct g, by simpa only [ConjAct.toConjAct_smul] using hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨ConjAct.ofConjAct g, by simpa only [← ConjAct.toConjAct_smul,
      ConjAct.toConjAct_ofConjAct] using hg⟩

/-- The actual involution has square one by the checked triality-sign action. -/
theorem monsterGeometryBasePoint_square :
    generatedCentralInvolution * generatedCentralInvolution = 1 := by
  apply Subtype.ext
  change localCentralGriess * localCentralGriess = 1
  rw [localCentralGriess_eq_trialityCentralSign]
  exact trialityCentralSign_square 0

/-- Every actual source point is an involution. -/
theorem monsterGeometryPoint_square (p : MonsterGeometryPoint) : p.val ^ 2 = 1 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp p.property
  rw [← hg]
  calc
    (g * generatedCentralInvolution * g⁻¹) ^ 2 =
        g * (generatedCentralInvolution * generatedCentralInvolution) * g⁻¹ := by
          simp only [pow_two]
          group
    _ = 1 := by rw [monsterGeometryBasePoint_square, mul_one, mul_inv_cancel]

/-- Exact source Q-incidence: the second point lies in the conjugated actual extraspecial
subgroup attached to the first. The existential retains a genuine conjugator in G. -/
def monsterGeometryQIncident (p q : MonsterGeometryPoint) : Prop :=
  ∃ g : G, g * generatedCentralInvolution * g⁻¹ = p.val ∧
    ∃ x : Q, g * qIntoGenerated x * g⁻¹ = q.val

/-- A source line has three distinct actual points, product one, and mutual Q-incidence.
This is the line condition of Ivanov–Shpectorov II §7.1, not arbitrary commutation. -/
def monsterGeometryLine (p q r : MonsterGeometryPoint) : Prop :=
  p ≠ q ∧ q ≠ r ∧ r ≠ p ∧ p.val * q.val * r.val = 1 ∧
    monsterGeometryQIncident p q ∧ monsterGeometryQIncident q p ∧
    monsterGeometryQIncident p r ∧ monsterGeometryQIncident r p ∧
    monsterGeometryQIncident q r ∧ monsterGeometryQIncident r q

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
