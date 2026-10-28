/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual conjugation preserves the precise source extraspecial point-line geometry. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryQIncidence

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Actual conjugation gives a permutation of the independently specified source points. -/
noncomputable def monsterGeometryPointConjugation (g : G) :
    MonsterGeometryPoint ≃ MonsterGeometryPoint where
  toFun p := ⟨g * p.val * g⁻¹, p.property.trans (isConj_iff.mpr ⟨g, rfl⟩)⟩
  invFun p := ⟨g⁻¹ * p.val * g, p.property.trans
    (isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]⟩)⟩
  left_inv p := by apply Subtype.ext; dsimp; group
  right_inv p := by apply Subtype.ext; dsimp; group

/-- The literal point value is its actual conjugate in G. -/
@[simp] theorem monsterGeometryPointConjugation_value (g : G) (p : MonsterGeometryPoint) :
    (monsterGeometryPointConjugation g p).val = g * p.val * g⁻¹ := rfl

/-- Actual conjugation transports a source Q-incidence witness without altering its Q element. -/
theorem monsterGeometryQIncident_conjugation (g : G) (p q : MonsterGeometryPoint)
    (h : monsterGeometryQIncident p q) :
    monsterGeometryQIncident (monsterGeometryPointConjugation g p)
      (monsterGeometryPointConjugation g q) := by
  obtain ⟨k, hp, x, hq⟩ := h
  refine ⟨g * k, ?_, x, ?_⟩
  · change (g * k) * generatedCentralInvolution * (g * k)⁻¹ = g * p.val * g⁻¹
    rw [← hp]
    group
  · change (g * k) * qIntoGenerated x * (g * k)⁻¹ = g * q.val * g⁻¹
    rw [← hq]
    group

/-- The exact source line predicate is invariant under all actual G conjugations. -/
theorem monsterGeometryLine_conjugation (g : G) (p q r : MonsterGeometryPoint)
    (h : monsterGeometryLine p q r) :
    monsterGeometryLine (monsterGeometryPointConjugation g p)
      (monsterGeometryPointConjugation g q) (monsterGeometryPointConjugation g r) := by
  obtain ⟨hpq, hqr, hrp, hprod, hpqQ, hqpQ, hprQ, hrpQ, hqrQ, hrqQ⟩ := h
  refine ⟨(monsterGeometryPointConjugation g).injective.ne hpq,
    (monsterGeometryPointConjugation g).injective.ne hqr,
    (monsterGeometryPointConjugation g).injective.ne hrp, ?_,
    monsterGeometryQIncident_conjugation g p q hpqQ,
    monsterGeometryQIncident_conjugation g q p hqpQ,
    monsterGeometryQIncident_conjugation g p r hprQ,
    monsterGeometryQIncident_conjugation g r p hrpQ,
    monsterGeometryQIncident_conjugation g q r hqrQ,
    monsterGeometryQIncident_conjugation g r q hrqQ⟩
  simp only [monsterGeometryPointConjugation_value]
  calc
    (g * p.val * g⁻¹) * (g * q.val * g⁻¹) * (g * r.val * g⁻¹) =
        g * (p.val * q.val * r.val) * g⁻¹ := by group
    _ = 1 := by rw [hprod, mul_one, mul_inv_cancel]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
