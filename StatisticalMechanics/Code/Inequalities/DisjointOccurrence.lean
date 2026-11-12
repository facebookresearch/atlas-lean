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





def agreeOn (K : Set E) (ω ω' : ConfigSpace E) : Prop := ∀ e ∈ K, ω' e = ω e


@[refl] lemma agreeOn_refl (K : Set E) (ω : ConfigSpace E) : agreeOn K ω ω :=
  fun _ _ => rfl


lemma agreeOn_symm {K : Set E} {ω ω' : ConfigSpace E} (h : agreeOn K ω ω') :
    agreeOn K ω' ω := fun e he => (h e he).symm


lemma agreeOn_trans {K : Set E} {ω ω' ω'' : ConfigSpace E}
    (h : agreeOn K ω ω') (h' : agreeOn K ω' ω'') : agreeOn K ω ω'' :=
  fun e he => (h' e he).trans (h e he)



lemma agreeOn_mono {K K' : Set E} (hKK' : K ⊆ K') {ω ω' : ConfigSpace E}
    (h : agreeOn K' ω ω') : agreeOn K ω ω' := fun e he => h e (hKK' he)






def OccursOn (A : Set (ConfigSpace E)) (K : Set E) (ω : ConfigSpace E) : Prop :=
  ∀ ω', agreeOn K ω ω' → ω' ∈ A


lemma OccursOn.mem_self {A : Set (ConfigSpace E)} {K : Set E} {ω : ConfigSpace E}
    (h : OccursOn A K ω) : ω ∈ A := h ω (agreeOn_refl K ω)




lemma OccursOn.mono {A : Set (ConfigSpace E)} {K K' : Set E} {ω : ConfigSpace E}
    (h : OccursOn A K ω) (hKK' : K ⊆ K') : OccursOn A K' ω :=
  fun ω' hω' => h ω' (agreeOn_mono hKK' hω')



lemma OccursOn.mono_event {A B : Set (ConfigSpace E)} {K : Set E}
    {ω : ConfigSpace E} (h : OccursOn A K ω) (hAB : A ⊆ B) : OccursOn B K ω :=
  fun ω' hω' => hAB (h ω' hω')





def disjointOccurrence (A B : Set (ConfigSpace E)) : Set (ConfigSpace E) :=
  {ω | ∃ K L : Set E, Disjoint K L ∧ OccursOn A K ω ∧ OccursOn B L ω}










scoped notation3:70 A " □ " B => disjointOccurrence A B


lemma mem_disjointOccurrence {A B : Set (ConfigSpace E)} {ω : ConfigSpace E} :
    ω ∈ disjointOccurrence A B ↔
      ∃ K L : Set E, Disjoint K L ∧ OccursOn A K ω ∧ OccursOn B L ω :=
  Iff.rfl



lemma disjointOccurrence_notation (A B : Set (ConfigSpace E)) :
    (A □ B : Set (ConfigSpace E)) = disjointOccurrence A B := rfl



theorem disjointOccurrence_subset_inter (A B : Set (ConfigSpace E)) :
    disjointOccurrence A B ⊆ A ∩ B := by
  rintro ω ⟨K, L, _, hA, hB⟩
  exact ⟨hA.mem_self, hB.mem_self⟩



theorem disjointOccurrence_comm (A B : Set (ConfigSpace E)) :
    disjointOccurrence A B = disjointOccurrence B A := by
  ext ω
  constructor
  · rintro ⟨K, L, hKL, hA, hB⟩
    exact ⟨L, K, hKL.symm, hB, hA⟩
  · rintro ⟨K, L, hKL, hB, hA⟩
    exact ⟨L, K, hKL.symm, hA, hB⟩



theorem disjointOccurrence_mono {A A' B B' : Set (ConfigSpace E)}
    (hA : A ⊆ A') (hB : B ⊆ B') :
    disjointOccurrence A B ⊆ disjointOccurrence A' B' := by
  rintro ω ⟨K, L, hKL, hAK, hBL⟩
  exact ⟨K, L, hKL, hAK.mono_event hA, hBL.mono_event hB⟩

end StatMech
