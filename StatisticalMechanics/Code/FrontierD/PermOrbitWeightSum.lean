/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKMedialBoundaryOrbitVisits



open Equiv Finset

namespace StatMech.FrontierD

noncomputable section


def permOrbitWeightSum {α A : Type*} [Fintype α] [DecidableEq α]
    [AddCommMonoid A] (σ : Perm α) (d : α) (f : α → A) : A :=
  ∑ i : Fin (orderOf σ), f ((σ ^ (i : Nat)) d)


def permCycleClassWeightSum {α A : Type*} [Fintype α] [DecidableEq α]
    [AddCommMonoid A] (σ : Perm α) (d : α) (f : α → A) : A :=
  ∑ x : α, if σ.SameCycle d x then f x else 0

private theorem sum_indicator_smul
    {α A : Type*} [Fintype α] [DecidableEq α]
    [AddCommMonoid A] (σ : Perm α) (d x : α) (f : α → A) :
    (permOrbitVisitCount σ d x) • f x =
      ∑ i : Fin (orderOf σ),
        if (σ ^ (i : Nat)) d = x then f x else 0 := by
  unfold permOrbitVisitCount
  change (∑ i ∈ (Finset.univ : Finset (Fin (orderOf σ))),
      if (σ ^ (i : Nat)) d = x then 1 else 0) • f x =
    ∑ i ∈ (Finset.univ : Finset (Fin (orderOf σ))),
      if (σ ^ (i : Nat)) d = x then f x else 0
  generalize (Finset.univ : Finset (Fin (orderOf σ))) = s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, add_nsmul, ih]
      split <;> simp_all

private theorem nsmul_sum_eq_sum_nsmul
    {α A : Type*} [Fintype α] [DecidableEq α]
    [AddCommMonoid A] (n : Nat) (f : α → A) :
    n • (∑ x : α, f x) = ∑ x : α, n • f x := by
  change n • (∑ x ∈ (Finset.univ : Finset α), f x) =
    ∑ x ∈ (Finset.univ : Finset α), n • f x
  generalize (Finset.univ : Finset α) = s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx, nsmul_add, ih]



theorem permOrbitWeightSum_eq_visitCount_nsmul_cycleSum
    {α A : Type*} [Fintype α] [DecidableEq α]
    [AddCommMonoid A] (σ : Perm α) (d : α) (f : α → A) :
    permOrbitWeightSum σ d f =
      (permOrbitVisitCount σ d d) •
        permCycleClassWeightSum σ d f := by
  classical
  unfold permOrbitWeightSum permCycleClassWeightSum
  calc
    (∑ i : Fin (orderOf σ), f ((σ ^ (i : Nat)) d)) =
        ∑ i : Fin (orderOf σ), ∑ x : α,
          if (σ ^ (i : Nat)) d = x then f x else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp
    _ = ∑ x : α, ∑ i : Fin (orderOf σ),
          if (σ ^ (i : Nat)) d = x then f x else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x : α, (permOrbitVisitCount σ d x) • f x := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (sum_indicator_smul σ d x f).symm
    _ = ∑ x : α,
          (permOrbitVisitCount σ d d) •
            (if σ.SameCycle d x then f x else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hdx : σ.SameCycle d x
      · rw [if_pos hdx,
          permOrbitVisitCount_eq_of_sameCycle σ d d x hdx]
      · rw [if_neg hdx,
          (permOrbitVisitCount_eq_zero_iff_not_sameCycle σ d x).2 hdx]
        simp
    _ = (permOrbitVisitCount σ d d) •
          ∑ x : α, if σ.SameCycle d x then f x else 0 := by
      exact (nsmul_sum_eq_sum_nsmul
        (permOrbitVisitCount σ d d)
        (fun x : α => if σ.SameCycle d x then f x else 0)).symm


theorem permOrbitVisitCount_self_pos
    {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) (d : α) :
    0 < permOrbitVisitCount σ d d :=
  (permOrbitVisitCount_pos_iff_sameCycle σ d d).2 .rfl

end

end StatMech.FrontierD
