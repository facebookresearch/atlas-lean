/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Configuration.ConfigSpace

@[expose] public section

/-!
# Disjoint occurrence of events

For events `A B ⊆ ConfigSpace E = E → Bool`, the *disjoint occurrence* `A □ B` is the set of
configurations `ω` for which there are disjoint sets of coordinates `K` and `L` such that the
values of `ω` on `K` alone force `A` and the values of `ω` on `L` alone force `B`. This is the
event appearing in the van den Berg–Kesten (BK) and Reimer inequalities.

## Main definitions

* `StatMech.agreeOn K ω ω'`: the configurations `ω` and `ω'` agree on `K`.
* `StatMech.OccursOn A K ω`: `A` occurs on `K` at `ω`, i.e. every configuration agreeing with `ω`
  on `K` lies in `A` (the restriction of `ω` to `K` is a witness for `A`).
* `StatMech.disjointOccurrence A B`, notation `A □ B`: the disjoint occurrence of `A` and `B`.

## Main results

* `StatMech.disjointOccurrence_subset_inter`: `A □ B ⊆ A ∩ B`.
* `StatMech.disjointOccurrence_comm`, `StatMech.disjointOccurrence_mono`.

## References

* J. van den Berg, H. Kesten, *Inequalities with applications to percolation and reliability*,
  J. Appl. Probab. 22 (1985).
-/

namespace StatMech

open ConfigSpace

variable {E : Type*}

/-- `agreeOn K ω ω'`: the configurations `ω` and `ω'` take the same value at every coordinate of
`K`. This is `Set.EqOn ω' ω K` (see `StatMech.agreeOn_iff_eqOn`). -/
def agreeOn (K : Set E) (ω ω' : ConfigSpace E) : Prop := ∀ e ∈ K, ω' e = ω e

/-- `agreeOn` is the pointwise form of `Set.EqOn`. -/
lemma agreeOn_iff_eqOn {K : Set E} {ω ω' : ConfigSpace E} : agreeOn K ω ω' ↔ Set.EqOn ω' ω K :=
  ⟨fun h _ he => h _ he, fun h _ he => h he⟩

/-- Every configuration agrees with itself (`Set.eqOn_refl`). -/
@[refl] lemma agreeOn_refl (K : Set E) (ω : ConfigSpace E) : agreeOn K ω ω :=
  fun _ _ => rfl

/-- `agreeOn` is symmetric (`Set.EqOn.symm`). -/
lemma agreeOn_symm {K : Set E} {ω ω' : ConfigSpace E} (h : agreeOn K ω ω') :
    agreeOn K ω' ω := fun e he => (h e he).symm

/-- `agreeOn` is transitive (`Set.EqOn.trans`). -/
lemma agreeOn_trans {K : Set E} {ω ω' ω'' : ConfigSpace E}
    (h : agreeOn K ω ω') (h' : agreeOn K ω' ω'') : agreeOn K ω ω'' :=
  fun e he => (h' e he).trans (h e he)

/-- Agreement on a set implies agreement on any subset (`Set.EqOn.mono`). -/
lemma agreeOn_mono {K K' : Set E} (hKK' : K ⊆ K') {ω ω' : ConfigSpace E}
    (h : agreeOn K' ω ω') : agreeOn K ω ω' := fun e he => h e (hKK' he)

/-- `OccursOn A K ω`: the event `A` occurs on the coordinate set `K` at `ω`, meaning that every
configuration agreeing with `ω` on `K` lies in `A`. -/
def OccursOn (A : Set (ConfigSpace E)) (K : Set E) (ω : ConfigSpace E) : Prop :=
  ∀ ω', agreeOn K ω ω' → ω' ∈ A

/-- If `A` occurs on some `K` at `ω`, then `ω ∈ A`. -/
lemma OccursOn.mem_self {A : Set (ConfigSpace E)} {K : Set E} {ω : ConfigSpace E}
    (h : OccursOn A K ω) : ω ∈ A := h ω (agreeOn_refl K ω)

/-- Occurrence on `K` implies occurrence on any larger coordinate set. -/
lemma OccursOn.mono {A : Set (ConfigSpace E)} {K K' : Set E} {ω : ConfigSpace E}
    (h : OccursOn A K ω) (hKK' : K ⊆ K') : OccursOn A K' ω :=
  fun ω' hω' => h ω' (agreeOn_mono hKK' hω')

/-- Occurrence of `A` on `K` implies occurrence of any larger event `B ⊇ A` on `K`. -/
lemma OccursOn.mono_event {A B : Set (ConfigSpace E)} {K : Set E}
    {ω : ConfigSpace E} (h : OccursOn A K ω) (hAB : A ⊆ B) : OccursOn B K ω :=
  fun ω' hω' => hAB (h ω' hω')

/-- The *disjoint occurrence* `A □ B`: the configurations `ω` for which there are disjoint
coordinate sets `K` and `L` such that `A` occurs on `K` at `ω` and `B` occurs on `L` at `ω`. -/
def disjointOccurrence (A B : Set (ConfigSpace E)) : Set (ConfigSpace E) :=
  {ω | ∃ K L : Set E, Disjoint K L ∧ OccursOn A K ω ∧ OccursOn B L ω}

/-- Notation `A □ B` for `StatMech.disjointOccurrence A B`. -/
scoped notation3:70 A " □ " B => disjointOccurrence A B

/-- Membership in `A □ B` unfolded. -/
lemma mem_disjointOccurrence {A B : Set (ConfigSpace E)} {ω : ConfigSpace E} :
    ω ∈ disjointOccurrence A B ↔
      ∃ K L : Set E, Disjoint K L ∧ OccursOn A K ω ∧ OccursOn B L ω :=
  Iff.rfl

/-- The notation `A □ B` unfolds to `disjointOccurrence A B`. -/
lemma disjointOccurrence_notation (A B : Set (ConfigSpace E)) :
    (A □ B : Set (ConfigSpace E)) = disjointOccurrence A B := rfl

/-- Disjoint occurrence implies occurrence of both events: `A □ B ⊆ A ∩ B`. -/
theorem disjointOccurrence_subset_inter (A B : Set (ConfigSpace E)) :
    disjointOccurrence A B ⊆ A ∩ B := by
  rintro ω ⟨K, L, _, hA, hB⟩
  exact ⟨hA.mem_self, hB.mem_self⟩

/-- Disjoint occurrence is symmetric: `A □ B = B □ A`. -/
theorem disjointOccurrence_comm (A B : Set (ConfigSpace E)) :
    disjointOccurrence A B = disjointOccurrence B A := by
  ext ω
  constructor
  · rintro ⟨K, L, hKL, hA, hB⟩
    exact ⟨L, K, hKL.symm, hB, hA⟩
  · rintro ⟨K, L, hKL, hB, hA⟩
    exact ⟨L, K, hKL.symm, hA, hB⟩

/-- Disjoint occurrence is monotone in both events. -/
theorem disjointOccurrence_mono {A A' B B' : Set (ConfigSpace E)}
    (hA : A ⊆ A') (hB : B ⊆ B') :
    disjointOccurrence A B ⊆ disjointOccurrence A' B' := by
  rintro ω ⟨K, L, hKL, hAK, hBL⟩
  exact ⟨K, L, hKL, hAK.mono_event hA, hBL.mono_event hB⟩

end StatMech
