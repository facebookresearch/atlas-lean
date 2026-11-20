/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.PermOrbitWeightSum
import Code.FrontierA.PermCycleQuotientCount



open Equiv Finset

namespace StatMech.FrontierD

noncomputable section



noncomputable instance permCycleClassFintype
    {D : Type*} [Fintype D] [DecidableEq D] (sigma : Perm D) :
    Fintype (StatMech.FrontierA.PermCycleClass sigma) :=
  Fintype.ofEquiv
    (StatMech.FrontierA.PermCycleRepresentative sigma)
    (StatMech.FrontierA.permCycleClassEquivRepresentative sigma).symm



def permCycleQuotientWeightSum
    {D A : Type*} [Fintype D] [DecidableEq D] [AddCommMonoid A]
    (sigma : Perm D) (C : StatMech.FrontierA.PermCycleClass sigma)
    (f : D → A) : A := by
  classical
  exact ∑ x : D, if C = Quot.mk _ x then f x else 0



theorem permCycleClassWeightSum_eq_of_sameCycle
    {D A : Type*} [Fintype D] [DecidableEq D] [AddCommMonoid A]
    (sigma : Perm D) (d e : D) (f : D → A)
    (hde : sigma.SameCycle d e) :
    permCycleClassWeightSum sigma d f =
      permCycleClassWeightSum sigma e f := by
  classical
  unfold permCycleClassWeightSum
  apply Finset.sum_congr rfl
  intro x _
  have hiff : sigma.SameCycle d x ↔ sigma.SameCycle e x :=
    ⟨fun h => hde.symm.trans h, fun h => hde.trans h⟩
  by_cases hdx : sigma.SameCycle d x
  · simp [hdx, hiff.mp hdx]
  · simp [hdx, mt hiff.mpr hdx]



theorem permCycleClassWeightSum_filter_of_sameCycle_invariant
    {D A : Type*} [Fintype D] [DecidableEq D] [AddCommMonoid A]
    (sigma : Perm D) (p : D → Prop) [DecidablePred p] (f : D → A)
    (hinv : ∀ d e, sigma.SameCycle d e → (p d ↔ p e)) (d : D) :
    permCycleClassWeightSum sigma d
        (fun e => if p e then f e else 0) =
      if p d then permCycleClassWeightSum sigma d f else 0 := by
  classical
  unfold permCycleClassWeightSum
  by_cases hd : p d
  · rw [if_pos hd]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hde : sigma.SameCycle d e
    · simp [hde, (hinv d e hde).mp hd]
    · simp [hde]
  · rw [if_neg hd]
    apply Finset.sum_eq_zero
    intro e _
    by_cases hde : sigma.SameCycle d e
    · simp [hde, mt (hinv d e hde).mpr hd]
    · simp [hde]



theorem permCycleQuotientWeightSum_mk
    {D A : Type*} [Fintype D] [DecidableEq D] [AddCommMonoid A]
    (sigma : Perm D) (d : D) (f : D → A) :
    permCycleQuotientWeightSum sigma (Quot.mk _ d) f =
      permCycleClassWeightSum sigma d f := by
  classical
  unfold permCycleQuotientWeightSum permCycleClassWeightSum
  apply Finset.sum_congr rfl
  intro x _
  rw [show (Quot.mk (Perm.SameCycle.setoid sigma) d = Quot.mk _ x) ↔
      sigma.SameCycle d x by
    exact Quotient.eq_iff_equiv]
  by_cases h : sigma.SameCycle d x <;> simp [h]



theorem sum_permCycleQuotientWeightSum
    {D A : Type*} [Fintype D] [DecidableEq D] [AddCommMonoid A]
    (sigma : Perm D) (f : D → A) :
    (∑ C : StatMech.FrontierA.PermCycleClass sigma,
        permCycleQuotientWeightSum sigma C f) = ∑ x : D, f x := by
  classical
  unfold permCycleQuotientWeightSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp




theorem eq_of_sum_ite_eq_zero_of_card_nonzero_le_two_of_fst_mul_pos
    {D : Type*} [Fintype D] [DecidableEq D]
    (p : D → Prop) [DecidablePred p] (w : D → Int × Int)
    (hsum : (∑ d : D, if p d then w d else 0) = 0)
    (hcard : (Finset.univ.filter fun d => p d ∧ w d ≠ 0).card ≤ 2)
    {a b : D} (ha : p a) (hb : p b)
    (hsign : 0 < (w a).1 * (w b).1) : a = b := by
  classical
  by_contra hab
  let S := Finset.univ.filter fun d => p d ∧ w d ≠ 0
  have hwa : w a ≠ 0 := by
    intro hzero
    rw [hzero] at hsign
    simp at hsign
  have hwb : w b ≠ 0 := by
    intro hzero
    rw [hzero] at hsign
    simp at hsign
  have haS : a ∈ S := by simp [S, ha, hwa]
  have hbS : b ∈ S := by simp [S, hb, hwb]
  have hpS : ({a, b} : Finset D) ⊆ S := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact haS
    · exact hbS
  have hcardS : S.card ≤ 2 := by simpa [S] using hcard
  have hpair : ({a, b} : Finset D) = S := by
    apply Finset.eq_of_subset_of_card_le hpS
    simpa [hab] using hcardS
  have hsumS : (∑ d ∈ S, w d) = 0 := by
    change (∑ d ∈ Finset.univ.filter (fun d => p d ∧ w d ≠ 0),
      w d) = 0
    rw [Finset.sum_filter]
    calc
      (∑ d : D, if p d ∧ w d ≠ 0 then w d else 0) =
          ∑ d : D, if p d then w d else 0 := by
        apply Finset.sum_congr rfl
        intro d _
        by_cases hd : p d <;> by_cases hw : w d = 0 <;> simp [hd, hw]
      _ = 0 := hsum
  rw [← hpair] at hsumS
  have hfirst := congrArg Prod.fst hsumS
  simp [hab] at hfirst
  have hbneg : (w b).1 = -(w a).1 := by omega
  rw [hbneg] at hsign
  nlinarith [sq_nonneg (w a).1]

end

end StatMech.FrontierD
