/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectTorusNetMonotonicity

open SimpleGraph

namespace StatMech.FrontierD

noncomputable section


def fkRectClosedWindingSubgroup (R : FKRectTorus)
    (omega : R.Configuration) (x : R.Vertex) : AddSubgroup (Int × Int) where
  carrier := {u | ∃ p : (fkRectOpenGraph R omega).Walk x x,
    fkRectWalkWinding R p = u}
  zero_mem' := ⟨.nil, rfl⟩
  add_mem' := by
    rintro u v ⟨p, rfl⟩ ⟨q, rfl⟩
    refine ⟨p.append q, ?_⟩
    simpa using fkRectWalkWinding_append R p q
  neg_mem' := by
    rintro u ⟨p, rfl⟩
    refine ⟨p.reverse, ?_⟩
    simpa using fkRectWalkWinding_reverse R p

@[simp] theorem mem_fkRectClosedWindingSubgroup_iff
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex)
    (u : Int × Int) :
    u ∈ fkRectClosedWindingSubgroup R omega x ↔
      ∃ p : (fkRectOpenGraph R omega).Walk x x,
        fkRectWalkWinding R p = u :=
  Iff.rfl



theorem fkRectClosedWindingSubgroup_eq_of_reachable
    (R : FKRectTorus) (omega : R.Configuration) {x y : R.Vertex}
    (hxy : (fkRectOpenGraph R omega).Reachable x y) :
    fkRectClosedWindingSubgroup R omega x =
      fkRectClosedWindingSubgroup R omega y := by
  obtain ⟨r⟩ := hxy
  apply le_antisymm
  · rintro u ⟨p, hp⟩
    refine ⟨(r.reverse.append p).append r.reverse.reverse, ?_⟩
    rw [fkRectWalkWinding_conjugate]
    exact hp
  · rintro u ⟨q, hq⟩
    refine ⟨(r.append q).append r.reverse, ?_⟩
    rw [fkRectWalkWinding_conjugate]
    exact hq



def FKRectWindingSubgroupRankTwo (R : FKRectTorus)
    (omega : R.Configuration) (x : R.Vertex) : Prop :=
  ∃ u ∈ fkRectClosedWindingSubgroup R omega x,
    ∃ v ∈ fkRectClosedWindingSubgroup R omega x,
      FKRectWindingIndependent u v


theorem fkRectWindingSubgroupRankTwo_iff_of_reachable
    (R : FKRectTorus) (omega : R.Configuration) {x y : R.Vertex}
    (hxy : (fkRectOpenGraph R omega).Reachable x y) :
    FKRectWindingSubgroupRankTwo R omega x ↔
      FKRectWindingSubgroupRankTwo R omega y := by
  rw [FKRectWindingSubgroupRankTwo, FKRectWindingSubgroupRankTwo,
    fkRectClosedWindingSubgroup_eq_of_reachable R omega hxy]



theorem fkRectHasNet_iff_exists_windingSubgroup_rankTwo
    (R : FKRectTorus) (omega : R.Configuration) :
    FKRectHasNet R omega ↔
      ∃ x : R.Vertex, FKRectWindingSubgroupRankTwo R omega x := by
  constructor
  · rintro ⟨x, p, q, hpq⟩
    exact ⟨x, fkRectWalkWinding R p, ⟨p, rfl⟩,
      fkRectWalkWinding R q, ⟨q, rfl⟩, hpq⟩
  · rintro ⟨x, u, ⟨p, hp⟩, v, ⟨q, hq⟩, huv⟩
    refine ⟨x, p, q, ?_⟩
    simpa [hp, hq] using huv


theorem fkRectNetIndicator_eq_one_iff_exists_windingSubgroup_rankTwo
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectNetIndicator R omega = 1 ↔
      ∃ x : R.Vertex, FKRectWindingSubgroupRankTwo R omega x := by
  rw [fkRectNetIndicator_eq_one_iff,
    fkRectHasNet_iff_exists_windingSubgroup_rankTwo]

end

end StatMech.FrontierD
