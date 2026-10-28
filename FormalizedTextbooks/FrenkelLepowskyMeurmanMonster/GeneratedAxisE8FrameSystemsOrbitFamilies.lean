/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsOrbitWords

/-! Two explicit families exhaust the actual carrier and lie in full section-group orbits. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual mapped candidates have distinct whole quotient subspaces. -/
theorem generatedAxisE8ActualFrameSystemCandidate_injective :
    Function.Injective generatedAxisE8ActualFrameSystemCandidate := by
  intro k l h
  apply generatedAxisE8FrameSystemCandidate_injective
  have he := congrArg (fun W : Submodule (ZMod 2) LeechModTwo =>
    W.comap generatedAxisE8FrameRootEmbedding) h
  simpa only [generatedAxisE8ActualFrameSystemCandidate,
    Submodule.comap_map_eq_of_injective generatedAxisE8FrameRootEmbedding_injective] using he

/-- Every actual selected-section frame system is one of the270 genuine mapped candidates. -/
theorem generatedAxisE8ActualFrameSystemCandidate_surjective
    (W : Submodule (ZMod 2) LeechModTwo)
    (hW : W ∈ generatedAxisE8FrameSystems
      (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad))) :
    ∃ k : Fin 270, generatedAxisE8ActualFrameSystemCandidate k = W := by
  obtain ⟨k, hk⟩ := generatedAxisE8ActualFrameSystemsEquivCandidates.surjective ⟨W, hW⟩
  exact ⟨k, congrArg Subtype.val hk⟩

/-- The two finite parent trees cover every candidate index. -/
theorem generatedAxisE8FrameSystemOrbitIndex_surjective :
    Function.Surjective (fun p : Fin 2 × Fin 135 =>
      generatedAxisE8FrameSystemOrbitIndex p.1 p.2) := by
  apply ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨generatedAxisE8FrameSystemOrbitIndex_injective, ?_⟩).2
  rw [Nat.card_prod, Nat.card_fin, Nat.card_fin, Nat.card_fin]

/-- The actual whole-subspace family reached from each explicit root. -/
def generatedAxisE8FrameSystemOrbitFamily (k : Fin 2) :
    Set (Submodule (ZMod 2) LeechModTwo) := Set.range (fun i : Fin 135 =>
  generatedAxisE8ActualFrameSystemCandidate (generatedAxisE8FrameSystemOrbitIndex k i))

/-- Each explicit family consists of135 distinct actual whole frame systems. -/
theorem generatedAxisE8FrameSystemOrbitFamily_card (k : Fin 2) :
    Nat.card (generatedAxisE8FrameSystemOrbitFamily k) = 135 := by
  let f (i : Fin 135) :=
    generatedAxisE8ActualFrameSystemCandidate (generatedAxisE8FrameSystemOrbitIndex k i)
  have hf : Function.Injective f := by
    intro i j h
    have he := generatedAxisE8ActualFrameSystemCandidate_injective h
    have hp : (k, i) = (k, j) := generatedAxisE8FrameSystemOrbitIndex_injective he
    exact congrArg Prod.snd hp
  exact (Nat.card_congr (Equiv.ofInjective f hf)).symm.trans (Nat.card_fin 135)

/-- Different parent trees give disjoint sets of actual whole frame systems. -/
theorem generatedAxisE8FrameSystemOrbitFamily_disjoint (k l : Fin 2) (hkl : k ≠ l) :
    Disjoint (generatedAxisE8FrameSystemOrbitFamily k)
      (generatedAxisE8FrameSystemOrbitFamily l) := by
  rw [Set.disjoint_left]
  rintro W ⟨i, rfl⟩ ⟨j, hj⟩
  have he := generatedAxisE8ActualFrameSystemCandidate_injective hj
  have hp : (l, j) = (k, i) := generatedAxisE8FrameSystemOrbitIndex_injective he
  exact hkl (congrArg Prod.fst hp).symm

/-- The two explicit source-word families exhaust the full actual selected-section carrier. -/
theorem generatedAxisE8FrameSystemOrbitFamily_union :
    generatedAxisE8FrameSystemOrbitFamily 0 ∪ generatedAxisE8FrameSystemOrbitFamily 1 =
      generatedAxisE8FrameSystems
        (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad)) := by
  apply Set.Subset.antisymm
  · rintro W (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact generatedAxisE8ActualFrameSystemCandidate_mem _
    · exact generatedAxisE8ActualFrameSystemCandidate_mem _
  · intro W hW
    obtain ⟨a, rfl⟩ := generatedAxisE8ActualFrameSystemCandidate_surjective W hW
    obtain ⟨⟨k, i⟩, rfl⟩ := generatedAxisE8FrameSystemOrbitIndex_surjective a
    fin_cases k
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr ⟨i, rfl⟩

/-- Every explicit family member is reached by a genuine word in the full section group. -/
theorem generatedAxisE8FrameSystemOrbitFamily_subset (k : Fin 2) :
    generatedAxisE8FrameSystemOrbitFamily k ⊆
      MulAction.orbit generatedAxisE8FrameSystemSectionGroup
        (generatedAxisE8ActualFrameSystemCandidate (generatedAxisE8FrameSystemOrbitRoot k)) := by
  rintro W ⟨i, rfl⟩
  exact generatedAxisE8FrameSystemOrbit_word_mem k i

/-- Inclusion between equally sized finite carriers is equality. -/
theorem generatedAxisE8FrameSystems_set_eq_of_subset_card {α : Type*} [Finite α]
    (A B : Set α) (hAB : A ⊆ B) (hc : Nat.card A = Nat.card B) : A = B := by
  let f : A → B := fun a => ⟨a.val, hAB a.property⟩
  have hf : Function.Injective f := by
    intro a b h
    have he : a.val = b.val := congrArg (fun z : B => z.val) h
    exact Subtype.ext he
  have hb : Function.Bijective f := (Nat.bijective_iff_injective_and_card f).mpr ⟨hf, hc⟩
  ext x
  constructor
  · intro hx
    exact hAB hx
  · intro hx
    obtain ⟨a, ha⟩ := hb.2 ⟨x, hx⟩
    have he : a.val = x := congrArg (fun z : B => z.val) ha
    exact he ▸ a.property

/-- The explicit candidate14 family is its full actual selected-section orbit. -/
theorem generatedAxisE8FrameSystemOrbitFamily_one_eq_orbit :
    generatedAxisE8FrameSystemOrbitFamily 1 =
      MulAction.orbit generatedAxisE8FrameSystemSectionGroup
        (generatedAxisE8ActualFrameSystemCandidate 14) := by
  have : Finite LeechModTwo := Finite.of_injective
    leechHyperbolicCoordinates leechHyperbolicCoordinates.injective
  apply generatedAxisE8FrameSystems_set_eq_of_subset_card
  · have h1 : (1 : Fin 2) ≠ 0 := by decide
    simpa only [generatedAxisE8FrameSystemOrbitRoot, ite_eq_right h1] using
      generatedAxisE8FrameSystemOrbitFamily_subset 1
  · exact (generatedAxisE8FrameSystemOrbitFamily_card 1).trans
      generatedAxisE8FrameSystemCandidate_orbit_card_fourteen.symm

/-- Candidate0 is outside the full actual orbit of candidate14. -/
theorem generatedAxisE8FrameSystemCandidate_zero_not_fourteen_orbit :
    generatedAxisE8ActualFrameSystemCandidate 0 ∉
      MulAction.orbit generatedAxisE8FrameSystemSectionGroup
        (generatedAxisE8ActualFrameSystemCandidate 14) := by
  intro h
  have h0 : generatedAxisE8ActualFrameSystemCandidate 0 ∈
      generatedAxisE8FrameSystemOrbitFamily 0 := by
    refine ⟨0, ?_⟩
    simp only [generatedAxisE8FrameSystemOrbit_root, ↓reduceIte]
  have h1 : generatedAxisE8ActualFrameSystemCandidate 0 ∈
      generatedAxisE8FrameSystemOrbitFamily 1 := by
    rwa [generatedAxisE8FrameSystemOrbitFamily_one_eq_orbit]
  exact Set.disjoint_left.mp
    (generatedAxisE8FrameSystemOrbitFamily_disjoint 0 1 (by decide)) h0 h1

/-- The candidate0 family is its full orbit under the original selected-section group. -/
theorem generatedAxisE8FrameSystemOrbitFamily_zero_eq_orbit :
    generatedAxisE8FrameSystemOrbitFamily 0 =
      MulAction.orbit generatedAxisE8FrameSystemSectionGroup
        (generatedAxisE8ActualFrameSystemCandidate 0) := by
  apply Set.Subset.antisymm
  · simpa only [generatedAxisE8FrameSystemOrbitRoot, ↓reduceIte] using
      generatedAxisE8FrameSystemOrbitFamily_subset 0
  · intro W hw
    have hc := generatedAxisE8FrameSystems_orbit_subset _
      (generatedAxisE8ActualFrameSystemCandidate_mem 0) hw
    rw [← generatedAxisE8FrameSystemOrbitFamily_union] at hc
    rcases hc with h0 | h1
    · exact h0
    · rw [generatedAxisE8FrameSystemOrbitFamily_one_eq_orbit] at h1
      exact (generatedAxisE8FrameSystemCandidate_zero_not_fourteen_orbit
        (MulAction.mem_orbit_trans (MulAction.mem_orbit_symm.mp hw) h1)).elim

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
