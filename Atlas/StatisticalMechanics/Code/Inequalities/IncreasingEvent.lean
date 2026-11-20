/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





















import Code.Foundations.ConfigSpace

namespace StatMech

open ConfigSpace

variable {E : Type*}





def IsIncreasing (A : Set (ConfigSpace E)) : Prop := IsUpperSet A


def IsDecreasing (A : Set (ConfigSpace E)) : Prop := IsLowerSet A



def IsIncreasingFun (f : ConfigSpace E → ℝ) : Prop := Monotone f


def IsDecreasingFun (f : ConfigSpace E → ℝ) : Prop := Antitone f


lemma IsIncreasing.compl {A : Set (ConfigSpace E)} (hA : IsIncreasing A) :
    IsDecreasing Aᶜ := IsUpperSet.compl hA


lemma IsDecreasing.compl {A : Set (ConfigSpace E)} (hA : IsDecreasing A) :
    IsIncreasing Aᶜ := IsLowerSet.compl hA


lemma IsIncreasing.inter {A B : Set (ConfigSpace E)}
    (hA : IsIncreasing A) (hB : IsIncreasing B) : IsIncreasing (A ∩ B) :=
  IsUpperSet.inter hA hB


lemma IsIncreasing.union {A B : Set (ConfigSpace E)}
    (hA : IsIncreasing A) (hB : IsIncreasing B) : IsIncreasing (A ∪ B) :=
  IsUpperSet.union hA hB


lemma isIncreasing_iInter {ι : Sort*} {A : ι → Set (ConfigSpace E)}
    (hA : ∀ i, IsIncreasing (A i)) : IsIncreasing (⋂ i, A i) :=
  isUpperSet_iInter hA



lemma IsIncreasing.indicator_monotone {A : Set (ConfigSpace E)} (hA : IsIncreasing A) :
    Monotone (A.indicator (fun _ => (1 : ℝ))) := by
  intro x y hxy
  simp only [Set.indicator]
  split_ifs with hxA hyA
  · exact le_refl _
  · exact absurd (hA hxy hxA) hyA
  · exact zero_le_one
  · exact le_refl _




theorem isIncreasing_iff_indicator_monotone {A : Set (ConfigSpace E)} :
    IsIncreasing A ↔ Monotone (A.indicator (fun _ => (1 : ℝ))) := by
  refine ⟨IsIncreasing.indicator_monotone, fun h x y hxy hx => ?_⟩
  have h1 : A.indicator (fun _ => (1 : ℝ)) x = 1 := by rw [Set.indicator_of_mem hx]
  have hle := h hxy
  rw [h1] at hle
  by_contra hy
  rw [Set.indicator_of_notMem hy] at hle
  linarith


lemma indicator_nonneg' (A : Set (ConfigSpace E)) :
    (0 : ConfigSpace E → ℝ) ≤ A.indicator (fun _ => (1 : ℝ)) := by
  intro x
  simp only [Pi.zero_apply, Set.indicator]
  split_ifs <;> norm_num







def FKGLatticeCondition (π : ConfigSpace E → ℝ) : Prop :=
  ∀ ω ω', π ω * π ω' ≤ π (ω ⊔ ω') * π (ω ⊓ ω')




lemma FKGLatticeCondition.of_logModular {π : ConfigSpace E → ℝ}
    (h : ∀ ω ω', π ω * π ω' = π (ω ⊔ ω') * π (ω ⊓ ω')) : FKGLatticeCondition π :=
  fun ω ω' => le_of_eq (h ω ω')

end StatMech
