/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamComponentExchangeUnitPacking










open Finset

namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent


def weightedCollisionEnds : Fin 4 → Sym2 (Fin 4)
  | 0 => s(0, 1)
  | 1 => s(0, 1)
  | 2 => s(0, 1)
  | 3 => s(0, 2)

theorem weightedCollisionEnds_loopless :
    ∀ i ∈ (Finset.univ : Finset (Fin 4)),
      ¬ (weightedCollisionEnds i).IsDiag := by
  intro i _
  fin_cases i <;> simp [weightedCollisionEnds, Sym2.mk_isDiag_iff]


def weightedCollisionLeftSupports : Finset (Finset (Fin 4)) :=
  {{0}, {1}, {2}, {0, 1, 2}}

theorem weightedCollisionLeftSupports_card :
    weightedCollisionLeftSupports.card = 4 := by
  decide

private theorem weightedCollision_zero_mem_ends (i : Fin 4) :
    (0 : Fin 4) ∈ weightedCollisionEnds i := by
  fin_cases i <;> simp [weightedCollisionEnds]

private theorem weightedCollision_three_not_mem_ends (i : Fin 4) :
    (3 : Fin 4) ∉ weightedCollisionEnds i := by
  fin_cases i <;> simp [weightedCollisionEnds]

private theorem weightedCollision_not_conn_three_zero (K : Finset (Fin 4)) :
    ¬ connK weightedCollisionEnds K 3 0 :=
  not_connK_of_no_incident (by decide) (fun i _ =>
    weightedCollision_three_not_mem_ends i)

private theorem weightedCollision_not_conn_zero_three (K : Finset (Fin 4)) :
    ¬ connK weightedCollisionEnds K 0 3 := by
  intro h
  exact weightedCollision_not_conn_three_zero K
    (connK_symm weightedCollisionEnds K h)

private theorem edgeComponent_mem_support
    {I W : Type*} [Fintype W] [DecidableEq W]
    {ends : I → Sym2 W} {K : Finset I} {u : W} {i : I}
    (hi : i ∈ edgeComponent ends K u) : i ∈ K := by
  classical
  rw [edgeComponent, Finset.mem_filter] at hi
  exact hi.1

private theorem edgeComponent_conn_endpoint
    {I W : Type*} [Fintype W] [DecidableEq W]
    {ends : I → Sym2 W} {K : Finset I} {u x : W} {i : I}
    (hi : i ∈ edgeComponent ends K u) (hx : x ∈ ends i) :
    connK ends K u x := by
  classical
  rw [edgeComponent, Finset.mem_filter] at hi
  exact hi.2 x hx

private theorem weightedCollision_edgeComponent_three (K : Finset (Fin 4)) :
    edgeComponent weightedCollisionEnds K 3 = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  exact weightedCollision_not_conn_three_zero K
    (edgeComponent_conn_endpoint hi (weightedCollision_zero_mem_ends i))

private theorem weightedCollision_edgeComponent_zero (K : Finset (Fin 4)) :
    edgeComponent weightedCollisionEnds K 0 = K := by
  classical
  apply Finset.Subset.antisymm
  · intro i hi
    exact edgeComponent_mem_support hi
  · intro i hi
    exact mem_edgeComponent_of_endpoint hi (weightedCollision_zero_mem_ends i)



theorem weightedCollisionLeftSupports_left :
    ∀ K ∈ weightedCollisionLeftSupports,
      K ⊆ (Finset.univ : Finset (Fin 4)) ∧
        LeftRowSupport weightedCollisionEnds Finset.univ 1 0 2 3 K := by
  intro K hK
  have hcases : K = {0} ∨ K = {1} ∨ K = {2} ∨ K = {0, 1, 2} := by
    simpa [weightedCollisionLeftSupports] using hK
  refine ⟨Finset.subset_univ K, ?_⟩
  unfold LeftRowSupport
  rcases hcases with rfl | rfl | rfl | rfl
  all_goals
    refine ⟨by decide, by decide,
      weightedCollision_not_conn_zero_three _,
      weightedCollision_not_conn_zero_three _⟩



theorem weightedCollisionLeftSupports_exchange :
    ∀ K ∈ weightedCollisionLeftSupports,
      exchangeFirstRow weightedCollisionEnds K (Finset.univ \ K) 0 3 =
        Finset.univ := by
  classical
  intro K _
  rw [exchangeFirstRow, weightedCollision_edgeComponent_three,
    weightedCollision_edgeComponent_zero, Finset.sdiff_empty]
  exact Finset.union_sdiff_of_subset (Finset.subset_univ K)


theorem weightedCollisionTarget_right :
    RightRowSupport weightedCollisionEnds Finset.univ 1 0 2 3
      Finset.univ := by
  unfold RightRowSupport
  refine ⟨by decide, ⟨{0}, by simp, by decide⟩, by simp [sources, degK],
    weightedCollision_not_conn_zero_three _,
    weightedCollision_not_conn_zero_three _⟩

theorem weightedCollision_weight_singleton_zero :
    rowSupportWeight weightedCollisionEnds Finset.univ {0} = 2 := by
  decide

theorem weightedCollision_weight_singleton_one :
    rowSupportWeight weightedCollisionEnds Finset.univ {1} = 2 := by
  decide

theorem weightedCollision_weight_singleton_two :
    rowSupportWeight weightedCollisionEnds Finset.univ {2} = 2 := by
  decide

theorem weightedCollision_weight_parallel :
    rowSupportWeight weightedCollisionEnds Finset.univ {0, 1, 2} = 4 := by
  decide

theorem weightedCollision_weight_target :
    rowSupportWeight weightedCollisionEnds Finset.univ Finset.univ = 4 := by
  decide


theorem weightedCollision_source_weight_sum :
    (∑ K ∈ weightedCollisionLeftSupports,
      rowSupportWeight weightedCollisionEnds Finset.univ K) = 10 := by
  change (∑ K ∈ insert {0} (insert {1} (insert {2} (singleton {0, 1, 2}))),
    rowSupportWeight weightedCollisionEnds Finset.univ K) = 10
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    weightedCollision_weight_singleton_zero,
    weightedCollision_weight_singleton_one,
    weightedCollision_weight_singleton_two,
    weightedCollision_weight_parallel]
  norm_num




theorem weightedCollision_fixedTarget_weighted_bound_false :
    ¬ ((∑ K ∈ weightedCollisionLeftSupports,
        rowSupportWeight weightedCollisionEnds Finset.univ K) ≤
      rowSupportWeight weightedCollisionEnds Finset.univ Finset.univ) := by
  rw [weightedCollision_source_weight_sum, weightedCollision_weight_target]
  omega

end StatMech.GrahamGHS.FourColor
