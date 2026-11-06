/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Original Monster line equations imply commuting involutory generator pairs. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryPresentation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryQIncidence
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1GeometryCommutatorData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Original point generators square to one in the independently presented Monster geometry. -/
theorem monsterGeometryPresentation_point_square (p : MonsterGeometryPoint) :
    (PresentedGroup.of p : MonsterGeometryPresentation) ^ 2 = 1 := by
  have h := PresentedGroup.one_of_mem (rels := monsterGeometryRelations)
    (x := FreeGroup.of p ^ 2) (Or.inl ⟨p, rfl⟩)
  simpa only [map_pow, PresentedGroup.of] using h

/-- Every original genuine Monster line has its literal three-generator product equal to one. -/
theorem monsterGeometryPresentation_line_product (p q r : MonsterGeometryPoint)
    (h : monsterGeometryLine p q r) :
    (PresentedGroup.of p : MonsterGeometryPresentation) * PresentedGroup.of q *
      PresentedGroup.of r = 1 := by
  have he := PresentedGroup.one_of_mem (rels := monsterGeometryRelations)
    (x := FreeGroup.of p * FreeGroup.of q * FreeGroup.of r) (Or.inr ⟨p, q, r, h, rfl⟩)
  simpa only [map_mul, PresentedGroup.of] using he

/-- Exchanging the last two points retains the exact six-incidence source line predicate. -/
theorem monsterGeometryLine_swap_last (p q r : MonsterGeometryPoint)
    (h : monsterGeometryLine p q r) : monsterGeometryLine p r q := by
  obtain ⟨hpq, hqr, hrp, hprod, hpqQ, hqpQ, hprQ, hrpQ, hqrQ, hrqQ⟩ := h
  refine ⟨hrp.symm, hqr.symm, hpq.symm, ?_, hprQ, hrpQ, hpqQ, hqpQ, hrqQ, hqrQ⟩
  have hc := monsterGeometryQIncident_commute q r hqrQ
  calc
    p.val * r.val * q.val = p.val * (r.val * q.val) := mul_assoc _ _ _
    _ = p.val * (q.val * r.val) := by rw [hc]
    _ = 1 := by rw [← mul_assoc, hprod]

/-- Cyclic ordering retains the exact original Monster line incidences and product. -/
theorem monsterGeometryLine_cycle (p q r : MonsterGeometryPoint)
    (h : monsterGeometryLine p q r) : monsterGeometryLine q r p := by
  obtain ⟨hpq, hqr, hrp, hprod, hpqQ, hqpQ, hprQ, hrpQ, hqrQ, hrqQ⟩ := h
  refine ⟨hqr, hrp, hpq, ?_, hqrQ, hrqQ, hqpQ, hpqQ, hrpQ, hprQ⟩
  calc
    q.val * r.val * p.val = p.val⁻¹ * (p.val * q.val * r.val) * p.val := by group
    _ = 1 := by rw [hprod, mul_one, inv_mul_cancel]

/-- Last-two generator images commute by original squares and the genuine line relation. -/
theorem monsterGeometryPresentation_line_commute (p q r : MonsterGeometryPoint)
    (h : monsterGeometryLine p q r) :
    Commute (PresentedGroup.of q : MonsterGeometryPresentation) (PresentedGroup.of r) := by
  exact co1GeometryCommutator_line_commute _ _ _
    (by simpa only [pow_two] using monsterGeometryPresentation_point_square p)
    (by simpa only [pow_two] using monsterGeometryPresentation_point_square q)
    (by simpa only [pow_two] using monsterGeometryPresentation_point_square r)
    (monsterGeometryPresentation_line_product p q r h)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
