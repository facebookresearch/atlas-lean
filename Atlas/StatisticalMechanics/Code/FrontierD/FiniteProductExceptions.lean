/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib



namespace StatMech.FrontierD

theorem pow_mul_pow_le_prod_of_exception_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bad : Finset ι) (D : Nat) {a b : Real}
    (ha : 0 < a) (ha1 : a <= 1) (hb : 0 < b) (hb1 : b <= 1)
    (hcard : bad.card <= D) (F : ι -> Real)
    (hall : ∀ i, b <= F i)
    (hbulk : ∀ i, i ∉ bad -> a <= F i) :
    b ^ D * a ^ Fintype.card ι <= ∏ i, F i := by
  classical
  let good := Finset.univ \ bad
  have hbadProd : b ^ bad.card <= ∏ i ∈ bad, F i := by
    rw [show b ^ bad.card = ∏ _i ∈ bad, b by simp]
    exact Finset.prod_le_prod (fun _ _ => hb.le) (fun i _ => hall i)
  have hgoodProd : a ^ good.card <= ∏ i ∈ good, F i := by
    rw [show a ^ good.card = ∏ _i ∈ good, a by simp]
    apply Finset.prod_le_prod (fun _ _ => ha.le)
    intro i hi
    exact hbulk i (Finset.mem_sdiff.1 hi).2
  have hgoodCard : good.card <= Fintype.card ι := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card (Finset.sdiff_subset)
  have hbPow : b ^ D <= b ^ bad.card :=
    pow_le_pow_of_le_one hb.le hb1 hcard
  have haPow : a ^ Fintype.card ι <= a ^ good.card :=
    pow_le_pow_of_le_one ha.le ha1 hgoodCard
  calc
    b ^ D * a ^ Fintype.card ι <= b ^ bad.card * a ^ good.card :=
      mul_le_mul hbPow haPow (pow_nonneg ha.le _) (pow_nonneg hb.le _)
    _ <= (∏ i ∈ bad, F i) * ∏ i ∈ good, F i :=
      mul_le_mul hbadProd hgoodProd (pow_nonneg ha.le _)
        (Finset.prod_nonneg fun i _ => (hb.trans_le (hall i)).le)
    _ = ∏ i, F i := by
      rw [mul_comm]
      exact Finset.prod_sdiff (s₁ := bad) (s₂ := Finset.univ)
        (Finset.subset_univ bad)

end StatMech.FrontierD
