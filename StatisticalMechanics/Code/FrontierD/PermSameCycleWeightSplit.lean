/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.PermSameCycleSplit
import Code.FrontierD.PermOrbitWeightSum



open Equiv Finset

namespace StatMech.FrontierD

open StatMech.FrontierA

variable {D A : Type*} [Fintype D] [DecidableEq D] [AddCommGroup A]

private theorem sum_eq_of_eq_off_pair_of_pair_eq
    (a b : D) (hab : a ≠ b) (f g : D → A)
    (haway : ∀ x, x ≠ a → x ≠ b → f x = g x)
    (hpair : f a + f b = g a + g b) :
    (∑ x : D, f x) = ∑ x : D, g x := by
  classical
  let s : Finset D := (Finset.univ.erase a).erase b
  have ha : a ∈ (Finset.univ : Finset D) := Finset.mem_univ a
  have hb : b ∈ (Finset.univ.erase a : Finset D) := by simp [hab.symm]
  have hfs : (∑ x ∈ s, f x) = ∑ x ∈ s, g x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hx' : x ≠ b ∧ x ≠ a := by simpa [s] using hx
    exact haway x hx'.2 hx'.1
  have hf : (∑ x : D, f x) = f a + f b + ∑ x ∈ s, f x := by
    rw [← Finset.sum_erase_add _ _ ha, ← Finset.sum_erase_add _ _ hb]
    simp only [s]
    ac_rfl
  have hg : (∑ x : D, g x) = g a + g b + ∑ x ∈ s, g x := by
    rw [← Finset.sum_erase_add _ _ ha, ← Finset.sum_erase_add _ _ hb]
    simp only [s]
    ac_rfl
  rw [hf, hg, hpair, hfs]




theorem permCycleClassWeightSum_split
    (σ : Perm D) (a b : D) (habne : a ≠ b)
    (hab : σ.SameCycle a b)
    (hcount : permCycleCount (σ * Equiv.swap a b) =
      permCycleCount σ + 1)
    (f g : D → A)
    (haway : ∀ x, x ≠ a → x ≠ b → f x = g x)
    (hpair : f a + f b = g a + g b) :
    permCycleClassWeightSum σ a f =
      permCycleClassWeightSum (σ * Equiv.swap a b) a g +
        permCycleClassWeightSum (σ * Equiv.swap a b) b g := by
  classical
  let τ := σ * Equiv.swap a b
  have hdisc : ¬ τ.SameCycle a b := by
    exact not_sameCycle_mul_swap_of_sameCycle σ habne hab
  have hfg :
      (∑ x : D, if σ.SameCycle a x then f x else 0) =
        ∑ x : D, if σ.SameCycle a x then g x else 0 := by
    apply sum_eq_of_eq_off_pair_of_pair_eq a b habne
    · intro x hxa hxb
      split
      · exact haway x hxa hxb
      · rfl
    · rw [if_pos .rfl, if_pos hab, if_pos .rfl, if_pos hab, hpair]
  have hindicator (x : D) :
      (if σ.SameCycle a x then g x else 0) =
        (if τ.SameCycle a x then g x else 0) +
          (if τ.SameCycle b x then g x else 0) := by
    by_cases hax : σ.SameCycle a x
    · rcases (sameCycle_mul_swap_partition_of_count σ habne hab hcount x).1 hax with
          hnewa | hnewb
      · have hnotb : ¬ τ.SameCycle b x := by
          intro hbx
          apply hdisc
          change τ.SameCycle a x at hnewa
          exact hnewa.trans hbx.symm
        change τ.SameCycle a x at hnewa
        simp [hax, hnewa, hnotb]
      · have hnota : ¬ τ.SameCycle a x := by
          intro hax'
          apply hdisc
          change τ.SameCycle b x at hnewb
          exact hax'.trans hnewb.symm
        change τ.SameCycle b x at hnewb
        simp [hax, hnewb, hnota]
    · have hnota : ¬ τ.SameCycle a x := by
        intro h
        apply hax
        exact (sameCycle_mul_swap_partition_of_count σ habne hab hcount x).2
          (Or.inl h)
      have hnotb : ¬ τ.SameCycle b x := by
        intro h
        apply hax
        exact (sameCycle_mul_swap_partition_of_count σ habne hab hcount x).2
          (Or.inr h)
      simp [hax, hnota, hnotb]
  unfold permCycleClassWeightSum
  rw [hfg]
  simp_rw [hindicator]
  exact Finset.sum_add_distrib


theorem permCycleClassWeightSum_eq_of_not_sameCycle
    (σ : Perm D) (a b x : D) (habne : a ≠ b)
    (hab : σ.SameCycle a b)
    (hcount : permCycleCount (σ * Equiv.swap a b) =
      permCycleCount σ + 1)
    (hx : ¬ σ.SameCycle a x)
    (f g : D → A)
    (haway : ∀ y, y ≠ a → y ≠ b → f y = g y) :
    permCycleClassWeightSum σ x f =
      permCycleClassWeightSum (σ * Equiv.swap a b) x g := by
  classical
  unfold permCycleClassWeightSum
  apply Finset.sum_congr rfl
  intro y hy
  have hiff := sameCycle_mul_swap_iff_of_not_sameCycle
    σ habne hab hcount hx (y := y)
  by_cases hxy : σ.SameCycle x y
  · have hya : y ≠ a := by
      intro h
      subst y
      exact hx hxy.symm
    have hyb : y ≠ b := by
      intro h
      subst y
      exact hx (hab.trans hxy.symm)
    simp [hxy, hiff, haway y hya hyb]
  · simp [hxy, hiff]

end StatMech.FrontierD
