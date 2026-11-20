/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsoradialRibbonBoundaryParity

namespace StatMech.FrontierA

open Equiv

variable {D : Type*} [Fintype D] [DecidableEq D]



abbrev PermCycleClass (sigma : Perm D) :=
  Quot (Equiv.Perm.SameCycle.setoid sigma)



abbrev PermCycleRepresentative (sigma : Perm D) :=
  sigma.cycleFactorsFinset ⊕ Function.fixedPoints sigma

noncomputable def permCycleRepresentativeOf (sigma : Perm D) (x : D) :
    PermCycleRepresentative sigma := by
  classical
  exact if hx : x ∈ sigma.support then
    Sum.inl ⟨sigma.cycleOf x,
      Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hx⟩
  else
    Sum.inr ⟨x, by simpa only [Equiv.Perm.notMem_support] using hx⟩

theorem permCycleRepresentativeOf_eq_iff_sameCycle
    (sigma : Perm D) (x y : D) :
    permCycleRepresentativeOf sigma x =
        permCycleRepresentativeOf sigma y ↔
      sigma.SameCycle x y := by
  classical
  by_cases hx : x ∈ sigma.support <;>
    by_cases hy : y ∈ sigma.support
  · simp only [permCycleRepresentativeOf, dif_pos hx, dif_pos hy,
      Sum.inl.injEq, Subtype.ext_iff]
    exact (Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support hx hy).symm
  · simp only [permCycleRepresentativeOf, dif_pos hx, dif_neg hy,
      Sum.inl_ne_inr, false_iff]
    intro hxy
    have hyfix : sigma y = y := by
      simpa only [Equiv.Perm.notMem_support] using hy
    have hxfix : sigma x = x :=
      (hxy.apply_eq_self_iff).2 hyfix
    exact (Equiv.Perm.mem_support.mp hx) hxfix
  · simp only [permCycleRepresentativeOf, dif_neg hx, dif_pos hy,
      Sum.inr_ne_inl, false_iff]
    intro hxy
    have hxfix : sigma x = x := by
      simpa only [Equiv.Perm.notMem_support] using hx
    have hyfix : sigma y = y :=
      (hxy.apply_eq_self_iff).1 hxfix
    exact (Equiv.Perm.mem_support.mp hy) hyfix
  · simp only [permCycleRepresentativeOf, dif_neg hx, dif_neg hy,
      Sum.inr.injEq, Subtype.ext_iff]
    constructor
    · intro hxy
      exact hxy.sameCycle sigma
    · intro hxy
      have hxfix : sigma x = x := by
        simpa only [Equiv.Perm.notMem_support] using hx
      exact hxy.eq_of_left hxfix

theorem permCycleRepresentativeOf_surjective (sigma : Perm D) :
    Function.Surjective (permCycleRepresentativeOf sigma) := by
  classical
  rintro (c | x)
  · obtain ⟨a, ha⟩ :=
      Equiv.Perm.IsCycle.nonempty_support
        (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).1
    refine ⟨a, ?_⟩
    simp only [permCycleRepresentativeOf, dif_pos
      (Equiv.Perm.mem_cycleFactorsFinset_support_le c.2 ha), Sum.inl.injEq,
      Subtype.ext_iff]
    exact (Equiv.Perm.cycle_is_cycleOf ha c.2).symm
  · refine ⟨x.1, ?_⟩
    have hx : x.1 ∉ sigma.support := by
      rw [Equiv.Perm.notMem_support]
      exact x.2
    simp [permCycleRepresentativeOf, hx]



noncomputable def permCycleClassEquivRepresentative (sigma : Perm D) :
    PermCycleClass sigma ≃ PermCycleRepresentative sigma := by
  classical
  let f : PermCycleClass sigma → PermCycleRepresentative sigma :=
    Quot.lift (permCycleRepresentativeOf sigma) fun x y hxy =>
      (permCycleRepresentativeOf_eq_iff_sameCycle sigma x y).2 hxy
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    induction a using Quot.ind with
    | _ x =>
      induction b using Quot.ind with
      | _ y =>
        apply Quot.sound
        exact (permCycleRepresentativeOf_eq_iff_sameCycle sigma x y).1 hab
  · intro r
    obtain ⟨x, hx⟩ := permCycleRepresentativeOf_surjective sigma r
    exact ⟨Quot.mk _ x, hx⟩



theorem natCard_permCycleClass (sigma : Perm D) :
    Nat.card (PermCycleClass sigma) = permCycleCount sigma := by
  classical
  rw [Nat.card_congr (permCycleClassEquivRepresentative sigma),
    Nat.card_eq_fintype_card, Fintype.card_sum,
    Fintype.card_coe, Equiv.Perm.card_fixedPoints]
  unfold permCycleCount
  rw [Equiv.Perm.cycleType_def, Multiset.card_map, Finset.card_def]

private theorem two_not_mem_cycleType_of_sq_ne
    (sigma : Perm D) (h2 : ∀ x, (sigma ^ 2) x ≠ x) :
    2 ∉ sigma.cycleType := by
  intro hmem
  simp only [Equiv.Perm.cycleType_def, ← Finset.mem_def,
    Function.comp_apply, Multiset.mem_map,
    Equiv.Perm.mem_cycleFactorsFinset_iff] at hmem
  obtain ⟨c, ⟨hc, hagree⟩, hcard⟩ := hmem
  obtain ⟨x, hx⟩ := hc.nonempty_support
  have hcx : c x = sigma x := hagree x hx
  have hcx_mem : c x ∈ c.support := Equiv.Perm.apply_mem_support.mpr hx
  have hccx : c (c x) = sigma (c x) := hagree (c x) hcx_mem
  have horder : orderOf c = 2 := hc.orderOf.trans hcard
  have hcpow : c ^ 2 = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [horder]
  apply h2 x
  rw [pow_two, Equiv.Perm.mul_apply, ← hcx, ← hccx]
  change (c ^ 2) x = x
  rw [hcpow]
  rfl



theorem four_mul_permCycleCount_eq_card_of_pow_four_eq_one_of_sq_ne
    (sigma : Perm D) (h4 : sigma ^ 4 = 1)
    (h2 : ∀ x, (sigma ^ 2) x ≠ x) :
    4 * permCycleCount sigma = Fintype.card D := by
  have hne2 := two_not_mem_cycleType_of_sq_ne sigma h2
  have hall : ∀ n ∈ sigma.cycleType, n = 4 := by
    intro n hn
    have hnlow := Equiv.Perm.two_le_of_mem_cycleType hn
    have hndiv : n ∣ 4 :=
      (Equiv.Perm.dvd_of_mem_cycleType hn).trans
        (orderOf_dvd_of_pow_eq_one h4)
    have hnnot : n ≠ 2 := fun h => hne2 (h ▸ hn)
    have hnle : n ≤ 4 := Nat.le_of_dvd (by norm_num) hndiv
    interval_cases n
    · exact (hnnot rfl).elim
    · norm_num at hndiv
    · rfl
  have htype : sigma.cycleType =
      Multiset.replicate sigma.cycleType.card 4 :=
    Multiset.eq_replicate.mpr ⟨rfl, hall⟩
  have hsupp : sigma.support = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro x
    apply Equiv.Perm.mem_support.mpr
    intro hx
    apply h2 x
    simp [pow_two, Equiv.Perm.mul_apply, hx]
  have hsum : sigma.cycleType.sum = Fintype.card D := by
    rw [sigma.sum_cycleType, hsupp, Finset.card_univ]
  have hcycles : sigma.cycleType.card * 4 = Fintype.card D := by
    rw [← hsum, htype, Multiset.sum_replicate]
    simp
  unfold permCycleCount
  rw [hsum, Nat.sub_self, Nat.add_zero]
  omega

end StatMech.FrontierA
