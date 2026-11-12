/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKMedialBoundaryOrbitReachability











open Equiv Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section

variable {T : EvenTorus}



def permOrbitVisitCount {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) (d e : α) : Nat :=
  ∑ i : Fin (orderOf σ), if (σ ^ (i : Nat)) d = e then 1 else 0

private theorem perm_pow_fin_add {α : Type*}
    (σ : Perm α) [NeZero (orderOf σ)]
    (i k : Fin (orderOf σ)) :
    σ ^ ((i + k : Fin (orderOf σ)) : Nat) =
      σ ^ ((i : Nat) + (k : Nat)) := by
  rw [← pow_mod_orderOf σ ((i : Nat) + (k : Nat))]
  congr


theorem permOrbitVisitCount_eq_of_sameCycle
    {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) (d a b : α) (hab : σ.SameCycle a b) :
    permOrbitVisitCount σ d a = permOrbitVisitCount σ d b := by
  classical
  letI : NeZero (orderOf σ) := ⟨(orderOf_pos σ).ne'⟩
  obtain ⟨k, hklt, hk⟩ := hab.exists_pow_eq'
  let kfin : Fin (orderOf σ) := ⟨k, hklt⟩
  unfold permOrbitVisitCount
  rw [← Equiv.sum_comp (Equiv.addRight kfin)
    (fun i : Fin (orderOf σ) =>
      if (σ ^ (i : Nat)) d = b then 1 else 0)]
  apply Finset.sum_congr rfl
  intro i hi
  change (if (σ ^ (i : Nat)) d = a then 1 else 0) =
    if (σ ^ ((i + kfin : Fin (orderOf σ)) : Nat)) d = b then 1 else 0
  rw [perm_pow_fin_add]
  rw [Nat.add_comm (i : Nat) (kfin : Nat)]
  simp only [pow_add, Perm.mul_apply]
  rw [← show (σ ^ (kfin : Nat)) a = b by exact hk]
  simp only [Equiv.apply_eq_iff_eq]



theorem permOrbitVisitCount_pos_iff_sameCycle
    {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) (d e : α) :
    0 < permOrbitVisitCount σ d e ↔ σ.SameCycle d e := by
  classical
  unfold permOrbitVisitCount
  rw [Finset.sum_pos_iff]
  constructor
  · rintro ⟨i, -, hi⟩
    have heq : (σ ^ (i : Nat)) d = e := by
      by_contra hne
      simp [hne] at hi
    refine ⟨(i : Nat), ?_⟩
    simpa only [zpow_natCast] using heq
  · intro hcycle
    obtain ⟨i, hi⟩ := hcycle.exists_fin_pow_eq
    refine ⟨i, Finset.mem_univ _, ?_⟩
    simp [hi]


theorem permOrbitVisitCount_eq_zero_iff_not_sameCycle
    {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) (d e : α) :
    permOrbitVisitCount σ d e = 0 ↔ ¬ σ.SameCycle d e := by
  rw [← permOrbitVisitCount_pos_iff_sameCycle]
  omega


abbrev fkMedialBoundaryOrbitVisitCount
    (pairing : FKMedialLoopPairing T) (d e : FKMedialDart T) : Nat :=
  permOrbitVisitCount (fkMedialBoundaryStep pairing) d e



theorem fkMedial_west_east_visitCount_eq_zero_iff_not_reachable
    (pairing : FKMedialLoopPairing T) (v : T.Vertex) :
    fkMedialBoundaryOrbitVisitCount pairing
        (fkMedialWestDart v) (fkMedialEastDart v) = 0 ↔
      ¬ (fkMedialLoopGraph T pairing).Reachable
        (fkMedialWestDart v) (fkMedialEastDart v) := by
  rw [permOrbitVisitCount_eq_zero_iff_not_sameCycle,
    fkMedial_west_east_sameCycle_iff_reachable]



theorem fkMedial_west_visitCount_eq_east_visitCount_iff_reachable
    (pairing : FKMedialLoopPairing T) (v : T.Vertex) :
    fkMedialBoundaryOrbitVisitCount pairing
        (fkMedialWestDart v) (fkMedialWestDart v) =
      fkMedialBoundaryOrbitVisitCount pairing
        (fkMedialWestDart v) (fkMedialEastDart v) ↔
      (fkMedialLoopGraph T pairing).Reachable
        (fkMedialWestDart v) (fkMedialEastDart v) := by
  constructor
  · intro hcount
    by_contra hreach
    have heast : fkMedialBoundaryOrbitVisitCount pairing
        (fkMedialWestDart v) (fkMedialEastDart v) = 0 :=
      (fkMedial_west_east_visitCount_eq_zero_iff_not_reachable
        pairing v).2 hreach
    have hwest : 0 < fkMedialBoundaryOrbitVisitCount pairing
        (fkMedialWestDart v) (fkMedialWestDart v) :=
      (permOrbitVisitCount_pos_iff_sameCycle _ _ _).2 ⟨0, rfl⟩
    omega
  · intro hreach
    apply permOrbitVisitCount_eq_of_sameCycle
    exact (fkMedial_west_east_sameCycle_iff_reachable pairing v).2 hreach



theorem fkMedial_west_sub_east_visitCount_ne_zero_iff_not_reachable
    (pairing : FKMedialLoopPairing T) (v : T.Vertex) :
    ((fkMedialBoundaryOrbitVisitCount pairing
          (fkMedialWestDart v) (fkMedialWestDart v) : Int) -
        fkMedialBoundaryOrbitVisitCount pairing
          (fkMedialWestDart v) (fkMedialEastDart v) ≠ 0) ↔
      ¬ (fkMedialLoopGraph T pairing).Reachable
        (fkMedialWestDart v) (fkMedialEastDart v) := by
  constructor
  · intro hdiff hreach
    apply hdiff
    apply sub_eq_zero.mpr
    exact_mod_cast
      (fkMedial_west_visitCount_eq_east_visitCount_iff_reachable
        pairing v).2 hreach
  · intro hreach hzero
    apply hreach
    apply (fkMedial_west_visitCount_eq_east_visitCount_iff_reachable
      pairing v).1
    exact_mod_cast (sub_eq_zero.mp hzero)

end

end StatMech.FrontierD
