/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.SetTheory.Determinacy.GaleStewart
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

@[expose] public section

open Set MathlibExt.SetTheory.Determinacy

namespace MathlibExtTest.SetTheory.Determinacy.GaleStewart

/-- The open game "player I eventually plays `true`" on `{false, true}`. -/
def eventuallyTrue : Set (ℕ → Bool) := {x | ∃ n, x n = true}

theorem isOpen_eventuallyTrue : IsOpen eventuallyTrue := by
  have : eventuallyTrue = ⋃ n, (fun x : ℕ → Bool => x n) ⁻¹' {true} := by
    ext x; simp [eventuallyTrue]
  rw [this]
  exact isOpen_iUnion fun n => (isOpen_discrete _).preimage (continuous_apply n)

/-- Player I wins by playing `true` at once. -/
example : IWins eventuallyTrue :=
  ⟨fun _ => true, fun _ hx => ⟨0, hx 0 rfl⟩⟩

/-- The Gale–Stewart theorem applies, and player II does not win. -/
example : Determined eventuallyTrue := determined_of_isOpen isOpen_eventuallyTrue

example : ¬ IIWins eventuallyTrue := fun h =>
  not_iWins_and_iiWins _
    ⟨(show IWins eventuallyTrue from ⟨fun _ => true, fun _ hx => ⟨0, hx 0 rfl⟩⟩), h⟩

/-- The closed game "every move is `false`": player II wins by playing `true` at move 1. -/
example : IIWins eventuallyTrueᶜ :=
  ⟨fun _ => true, fun _ hx h => h ⟨1, hx 1 rfl⟩⟩

example : Determined eventuallyTrueᶜ :=
  determined_of_isClosed isOpen_eventuallyTrue.isClosed_compl

/-- A closed game on `ℕ` won by player I, a non-trivial instance of the closed case. -/
example : Determined {x : ℕ → ℕ | ∀ n, x (2 * n) = 0} := by
  have : {x : ℕ → ℕ | ∀ n, x (2 * n) = 0} = ⋂ n, (fun x : ℕ → ℕ => x (2 * n)) ⁻¹' {0} := by
    ext x; simp
  rw [this]
  exact determined_of_isClosed
    (isClosed_iInter fun n => (isClosed_discrete _).preimage (continuous_apply _))

/-- The play of two strategies follows both. -/
example (σ τ : List Bool → Bool) : FollowsI σ (play σ τ) ∧ FollowsII τ (play σ τ) :=
  ⟨followsI_play σ τ, followsII_play σ τ⟩

/-- With a single move every game is determined. -/
example (S : Set (ℕ → Unit)) : Determined S := determined_of_subsingleton S

/-- With no moves at all there are no strategies, so nothing is determined: the hypothesis
`Nonempty A` of the Gale–Stewart theorem cannot be dropped. -/
example : ¬ Determined (Set.univ : Set (ℕ → Empty)) := by
  rintro (⟨σ, -⟩ | ⟨τ, -⟩)
  · exact (σ []).elim
  · exact (τ []).elim

/-- The hypotheses of the regularity theorems in `WantedExt.SetTheory.Determinacy.RegularityWanted`
are trivially satisfiable: the family `{∅, univ}` is closed under all preimages and its members
are determined. Its conclusions are trivial; by `mem_of_closed_under_borel_preimage`, any
non-trivial instance contains every Borel set and so needs Martin's Borel determinacy, a wanted
theorem here. -/
example : let Γ : Set (Set (ℕ → ℕ)) := {∅, Set.univ}
    (∀ f : (ℕ → ℕ) → ℕ → ℕ, Measurable f → ∀ B ∈ Γ, f ⁻¹' B ∈ Γ) ∧ (∀ B ∈ Γ, Determined B) := by
  refine ⟨?_, ?_⟩
  · rintro f - B (rfl | rfl)
    · simp
    · simp
  · rintro B (rfl | rfl)
    · exact determined_of_isOpen isOpen_empty
    · exact determined_of_isOpen isOpen_univ

/-- A family closed under preimages by Borel maps of `ℕ^ℕ` that contains a set other than `∅` and
`ℕ^ℕ` contains every Borel set: `B` is the preimage of `S` by the map sending `B` to `p ∈ S` and
its complement to `q ∉ S`. Hence the determinacy hypothesis of the regularity theorems, for such a
family, includes the determinacy of every Borel set (Martin's theorem, wanted in
`WantedExt.SetTheory.Determinacy.BorelDeterminacyWanted`). -/
theorem mem_of_closed_under_borel_preimage (Γ : Set (Set (ℕ → ℕ)))
    (hΓ : ∀ f : (ℕ → ℕ) → ℕ → ℕ, Measurable f → ∀ B ∈ Γ, f ⁻¹' B ∈ Γ)
    {S : Set (ℕ → ℕ)} (hS : S ∈ Γ) {p q : ℕ → ℕ} (hp : p ∈ S) (hq : q ∉ S)
    {B : Set (ℕ → ℕ)} (hB : MeasurableSet B) : B ∈ Γ := by
  classical
  have hf : Measurable (B.piecewise (fun _ => p) (fun _ => q)) :=
    Measurable.piecewise hB measurable_const measurable_const
  convert hΓ _ hf S hS using 1
  ext x
  by_cases hx : x ∈ B <;> simp [Set.piecewise, hx, hp, hq]

/-- The Borel sets form a family closed under preimages by Borel maps, as in the regularity
theorems; that its members are determined is Martin's theorem
(`WantedExt.SetTheory.Determinacy.BorelDeterminacyWanted`), a wanted theorem here. -/
example : ∀ f : (ℕ → ℕ) → ℕ → ℕ, Measurable f →
    ∀ B ∈ {B : Set (ℕ → ℕ) | MeasurableSet B}, f ⁻¹' B ∈ {B : Set (ℕ → ℕ) | MeasurableSet B} :=
  fun _ hf _ hB => hf hB

end MathlibExtTest.SetTheory.Determinacy.GaleStewart
