/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueLocalGroup

/-! The exact first-neighborhood quotient obeys genuine source line relations.
Identifying this representation with the M24 sextet residue is a separate geometric task. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The image of an actual neighbor point in the central point quotient. -/
def co1ResidueNeighborImage (p q : MonsterCo1GeometryPoint)
    (h : monsterCo1GeometryAdjacent p q) : Co1ResidueLocalQuotient p :=
  QuotientGroup.mk' (co1ResidueBaseKernel p)
    ⟨PresentedGroup.of q, co1ResidueLocal_neighbor_mem p q h⟩

/-- The distinguished central point has trivial image in the neighborhood quotient. -/
theorem co1ResidueBase_image_one (p : MonsterCo1GeometryPoint) :
    QuotientGroup.mk' (co1ResidueBaseKernel p) (co1ResidueBase p) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)

/-- Each actual neighbor image is still an involution in the residue representation. -/
theorem co1ResidueNeighborImage_mul_self (p q : MonsterCo1GeometryPoint)
    (h : monsterCo1GeometryAdjacent p q) :
    co1ResidueNeighborImage p q h * co1ResidueNeighborImage p q h = 1 := by
  let a : co1ResidueLocal p := ⟨PresentedGroup.of q, co1ResidueLocal_neighbor_mem p q h⟩
  have ha : a * a = 1 := Subtype.ext (co1UniversalPoint_mul_self q)
  exact (map_mul (QuotientGroup.mk' (co1ResidueBaseKernel p)) a a).symm.trans
    (by rw [ha, map_one])

/-- The two other points on a genuine line through the base define the same residue image. -/
theorem co1ResidueNeighborImage_eq_of_base_line (p q r : MonsterCo1GeometryPoint)
    (hq : monsterCo1GeometryAdjacent p q) (hr : monsterCo1GeometryAdjacent p r)
    (hline : monsterCo1GeometryLine p q r) :
    co1ResidueNeighborImage p q hq = co1ResidueNeighborImage p r hr := by
  let a : co1ResidueLocal p := ⟨PresentedGroup.of q, co1ResidueLocal_neighbor_mem p q hq⟩
  let b : co1ResidueLocal p := ⟨PresentedGroup.of r, co1ResidueLocal_neighbor_mem p r hr⟩
  have hab : co1ResidueBase p * a * b = 1 :=
    Subtype.ext (co1UniversalPoint_line p q r hline)
  have hm := congrArg (QuotientGroup.mk' (co1ResidueBaseKernel p)) hab
  rw [map_mul, map_mul, co1ResidueBase_image_one, one_mul, map_one] at hm
  have hs := co1ResidueNeighborImage_mul_self p q hq
  change co1ResidueNeighborImage p q hq * co1ResidueNeighborImage p r hr = 1 at hm
  exact mul_left_cancel (hs.trans hm.symm)

/-- A genuine original line entirely in the neighborhood retains its triple product relation
in the residue quotient. This uses the original line predicate, not binary collinearity. -/
theorem co1ResidueNeighborImage_line (p q r s : MonsterCo1GeometryPoint)
    (hq : monsterCo1GeometryAdjacent p q) (hr : monsterCo1GeometryAdjacent p r)
    (hs : monsterCo1GeometryAdjacent p s) (hline : monsterCo1GeometryLine q r s) :
    co1ResidueNeighborImage p q hq * co1ResidueNeighborImage p r hr *
      co1ResidueNeighborImage p s hs = 1 := by
  let a : co1ResidueLocal p := ⟨PresentedGroup.of q, co1ResidueLocal_neighbor_mem p q hq⟩
  let b : co1ResidueLocal p := ⟨PresentedGroup.of r, co1ResidueLocal_neighbor_mem p r hr⟩
  let c : co1ResidueLocal p := ⟨PresentedGroup.of s, co1ResidueLocal_neighbor_mem p s hs⟩
  have h : a * b * c = 1 := Subtype.ext (co1UniversalPoint_line q r s hline)
  have hm := congrArg (QuotientGroup.mk' (co1ResidueBaseKernel p)) h
  simpa only [map_mul, map_one, co1ResidueNeighborImage, a, b, c] using hm

/-- Actual neighbor images generate the entire neighborhood quotient; the base image has
already been killed by the central point kernel. -/
theorem co1ResidueNeighborImage_generates (p : MonsterCo1GeometryPoint) :
    Subgroup.closure (Set.range (fun q : {q // monsterCo1GeometryAdjacent p q} =>
      co1ResidueNeighborImage p q.val q.property)) = ⊤ := by
  let C : Subgroup (Co1ResidueLocalQuotient p) := Subgroup.closure
    (Set.range (fun q : {q // monsterCo1GeometryAdjacent p q} =>
      co1ResidueNeighborImage p q.val q.property))
  let f := QuotientGroup.mk' (co1ResidueBaseKernel p)
  have hle : co1ResidueLocal p ≤ (C.comap f).map (co1ResidueLocal p).subtype := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with rfl | ⟨q, hq, rfl⟩
    · apply Subgroup.mem_map.mpr
      refine ⟨co1ResidueBase p, ?_, rfl⟩
      change f (co1ResidueBase p) ∈ C
      rw [show f (co1ResidueBase p) = 1 from co1ResidueBase_image_one p]
      exact C.one_mem
    · apply Subgroup.mem_map.mpr
      refine ⟨⟨PresentedGroup.of q, co1ResidueLocal_neighbor_mem p q hq⟩, ?_, rfl⟩
      exact Subgroup.subset_closure ⟨⟨q, hq⟩, rfl⟩
  apply top_unique
  intro x _
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (co1ResidueBaseKernel p) x
  obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp (hle a.property)
  have heq : b = a := Subtype.ext hba
  exact heq ▸ hb

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
