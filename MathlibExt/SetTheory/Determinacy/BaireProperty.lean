/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.SetTheory.Determinacy.GaleStewart
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Baire.BaireMeasurable
public import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# The property of Baire from determinacy

We prove that if a family `Γ` of subsets of Baire space `ℕ^ℕ` is closed under preimages by Borel
maps `ℕ^ℕ → ℕ^ℕ` and all of its members are determined, then every member of `Γ` has the property
of Baire (`baireMeasurableSet_of_determined`).

The proof uses the Banach–Mazur game (Banach and Mazur; Oxtoby), coded as a Gale–Stewart game on
`ℕ`: each move codes a non-empty finite sequence (a word), and player I wins a play if the
concatenation of all the words, a continuous function of the play, lies in the payoff set `T`.
Given a strategy and a position, call a point *blocked* if it extends the words played so far but
no move at that position, followed by the strategy's reply, keeps an initial segment of it. Each
set of blocked points is closed with empty interior, so the points blocked at some position form a
meagre set.

* If player II wins with `τ`, every point `x` that `τ` blocks at no position is the outcome of a
  play following `τ` (player I always moves along `x`), so `x ∉ T`: hence `T` is meagre.
* If player I wins with `σ`, every point that begins with the first word of `σ` and that `σ`
  blocks at no position is, in the same way, the outcome of a play following `σ`, so it lies in
  `T`: hence `T` is comeagre in the basic open set given by that word.

For `S ∈ Γ`, let `U` be the union of the basic open sets in which `S` is comeagre, so that `U \ S`
is meagre. The set `S \ U` is a Borel preimage of `S` (send `U` to a point outside `S`), so its
Banach–Mazur game is determined. A winning strategy for player I would make `S` comeagre in a
basic open set contained in `U`, which `S \ U` misses, contradicting the Baire category theorem;
hence player II wins and `S \ U` is meagre. So `S` differs from the open set `U` by a meagre set.

**Hypotheses.** For the family of all subsets of `ℕ^ℕ`, the determinacy hypothesis is the axiom of
determinacy, which is false in Lean's ambient logic
(`MathlibExt.SetTheory.Determinacy.not_forall_determined`). A family satisfying the closure
hypothesis that contains a set other than `∅` and `ℕ^ℕ` contains every Borel set, so its
non-trivial instances need Martin's Borel determinacy theorem.
-/

open Set

open MathlibExt.SetTheory.Determinacy

namespace MathlibExt.SetTheory.DeterminacyWanted

/-- Non-empty words of natural numbers: the moves of the Banach–Mazur game on `ℕ^ℕ`. -/
private abbrev Word := {w : List ℕ // w ≠ []}

/-- The non-empty word coded by a move. -/
private def word (a : ℕ) : List ℕ :=
  ((Encodable.decode a : Option Word).getD ⟨[0], List.cons_ne_nil 0 []⟩).val

private theorem word_ne_nil (a : ℕ) : word a ≠ [] :=
  ((Encodable.decode a : Option Word).getD ⟨[0], List.cons_ne_nil 0 []⟩).property

private theorem word_encode (w : Word) : word (Encodable.encode w) = w.val := by
  simp [word, Encodable.encodek]

/-- The concatenation of the words coded by the moves of a finite history. -/
private def prefixOf (p : List ℕ) : List ℕ :=
  p.flatMap word

private theorem prefixOf_nil : prefixOf [] = [] := rfl

private theorem prefixOf_append (p q : List ℕ) : prefixOf (p ++ q) = prefixOf p ++ prefixOf q :=
  List.flatMap_append

private theorem prefixOf_singleton (a : ℕ) : prefixOf [a] = word a := by
  simp [prefixOf]

private theorem prefixOf_append_pair (p : List ℕ) (a b : ℕ) :
    prefixOf (p ++ [a, b]) = prefixOf p ++ word a ++ word b := by
  simp [prefixOf, List.append_assoc]

private theorem length_le_length_prefixOf (p : List ℕ) : p.length ≤ (prefixOf p).length := by
  induction p with
  | nil => simp
  | cons a p ih =>
    have h := List.length_pos_iff.mpr (word_ne_nil a)
    simp only [prefixOf, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    omega

private theorem le_length_prefixOf_history (x : ℕ → ℕ) (n : ℕ) :
    n ≤ (prefixOf (history x n)).length := by
  simpa only [length_history] using length_le_length_prefixOf (history x n)

private theorem prefixOf_history_mono (x : ℕ → ℕ) {m n : ℕ} (h : m ≤ n) :
    prefixOf (history x m) <+: prefixOf (history x n) := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih =>
    rw [history_succ, prefixOf_append]
    exact ih.trans (List.prefix_append _ _)

/-- The outcome of a play of the coded Banach–Mazur game: the concatenation of all the words
played. -/
private def outcome (x : ℕ → ℕ) (i : ℕ) : ℕ :=
  (prefixOf (history x (i + 1))).getD i 0

/-- A point matches a word if the word is an initial segment of it. -/
private def Matches (p : List ℕ) (x : ℕ → ℕ) : Prop :=
  ∀ i (hi : i < p.length), p[i] = x i

private theorem outcome_matches (x : ℕ → ℕ) (n : ℕ) :
    Matches (prefixOf (history x n)) (outcome x) := by
  intro i hi
  have hi' : i < (prefixOf (history x (i + 1))).length :=
    lt_of_lt_of_le (Nat.lt_succ_self i) (le_length_prefixOf_history x (i + 1))
  rw [outcome, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
  exact ((prefixOf_history_mono x (le_max_left n (i + 1))).getElem hi).trans
    ((prefixOf_history_mono x (le_max_right n (i + 1))).getElem hi').symm

/-- If infinitely many positions of a play are initial segments of `x`, the play has outcome
`x`. -/
private theorem outcome_eq_of_matches {y x : ℕ → ℕ}
    (h : ∀ n, ∃ m, n ≤ m ∧ Matches (prefixOf (history y m)) x) : outcome y = x := by
  funext i
  obtain ⟨m, hm, hmx⟩ := h (i + 1)
  have hi : i < (prefixOf (history y m)).length := by
    have := le_length_prefixOf_history y m
    omega
  exact (outcome_matches y m i hi).symm.trans (hmx i hi)

private theorem continuous_outcome : Continuous outcome := by
  apply continuous_pi
  intro i
  refine continuous_iff_continuousAt.mpr fun x => (continuousAt_const (y := outcome x i)).congr ?_
  filter_upwards [(PiNat.isOpen_cylinder (fun _ => ℕ) x (i + 1)).mem_nhds
    (PiNat.self_mem_cylinder x (i + 1))] with y hy
  have h : history y (i + 1) = history x (i + 1) :=
    history_eq_history_iff.mpr (PiNat.mem_cylinder_iff.mp hy)
  simp only [outcome, h]

private theorem isClopen_setOf_matches (w : List ℕ) : IsClopen {x : ℕ → ℕ | Matches w x} := by
  have h : {x : ℕ → ℕ | Matches w x} = ⋂ i : Fin w.length, (fun x : ℕ → ℕ => x i) ⁻¹' {w[i]} := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter, mem_preimage, mem_singleton_iff, Matches]
    exact ⟨fun h i => (h i i.isLt).symm, fun h i hi => (h ⟨i, hi⟩).symm⟩
  rw [h]
  exact isClopen_iInter_of_finite fun i => (isClopen_discrete _).preimage (continuous_apply _)

/-- The point that extends a word by zeros. -/
private def extendByZero (w : List ℕ) (i : ℕ) : ℕ :=
  w.getD i 0

private theorem matches_extendByZero (w : List ℕ) : Matches w (extendByZero w) := by
  intro i hi
  simp [extendByZero, hi]

private theorem exists_matching_append {p : List ℕ} {x : ℕ → ℕ} (hp : Matches p x)
    (k : ℕ) : ∃ w : List ℕ, w.length = k ∧ Matches (p ++ w) x := by
  let w := List.ofFn fun i : Fin k => x (p.length + i)
  refine ⟨w, by simp [w], fun i hi => ?_⟩
  by_cases h : i < p.length
  · exact (List.getElem_append_left h).trans (hp i h)
  · rw [List.getElem_append_right (by omega)]
    simp only [w, List.getElem_ofFn, Nat.add_sub_of_le (by omega : p.length ≤ i)]

/-- The points blocked at the position `p` by the strategy `ρ`: they extend the current
prefix, but no move at `p` followed by the reply of `ρ` keeps an initial segment of them. -/
private def blocked (ρ : List ℕ → ℕ) (p : List ℕ) : Set (ℕ → ℕ) :=
  {x | Matches (prefixOf p) x ∧ ∀ a, ¬Matches (prefixOf (p ++ [a, ρ (p ++ [a])])) x}

private theorem isClosed_blocked (ρ : List ℕ → ℕ) (p : List ℕ) : IsClosed (blocked ρ p) := by
  have h : blocked ρ p = {x | Matches (prefixOf p) x} ∩
      ⋂ a, {x | Matches (prefixOf (p ++ [a, ρ (p ++ [a])])) x}ᶜ := by
    ext x
    simp [blocked]
  rw [h]
  exact (isClopen_setOf_matches _).isClosed.inter
    (isClosed_iInter fun _ => (isClopen_setOf_matches _).isOpen.isClosed_compl)

/-- Each blocked set is nowhere dense: inside any basic open set meeting it, the mover can play a
word leading into that basic open set, after which the reply of `ρ` leaves the blocked set. -/
private theorem isNowhereDense_blocked (ρ : List ℕ → ℕ) (p : List ℕ) :
    IsNowhereDense (blocked ρ p) := by
  rw [(isClosed_blocked ρ p).isNowhereDense_iff, eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨_, ⟨z, N, rfl⟩, hxN, hN⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ : ℕ => ℕ)).exists_subset_of_mem_open hx
      isOpen_interior
  obtain ⟨w, hw, hxw⟩ := exists_matching_append (interior_subset hx).1 (N + 1)
  have hwne : w ≠ [] := by
    rintro rfl
    simp at hw
  let a := Encodable.encode (⟨w, hwne⟩ : Word)
  have hl : prefixOf (p ++ [a, ρ (p ++ [a])]) = (prefixOf p ++ w) ++ word (ρ (p ++ [a])) := by
    rw [prefixOf_append_pair, word_encode]
  let y := extendByZero ((prefixOf p ++ w) ++ word (ρ (p ++ [a])))
  have hyN : y ∈ PiNat.cylinder z N := by
    rw [PiNat.mem_cylinder_iff]
    intro i hi
    have hi' : i < (prefixOf p ++ w).length := by
      rw [List.length_append, hw]
      omega
    have hy : y i = (prefixOf p ++ w)[i] := by
      simp only [y, extendByZero]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi', List.getElem?_eq_getElem hi',
        Option.getD_some]
    rw [hy, hxw i hi']
    exact PiNat.mem_cylinder_iff.mp hxN i hi
  refine (interior_subset (hN hyN) : y ∈ blocked ρ p).2 a ?_
  rw [hl]
  exact matches_extendByZero _

private theorem isMeagre_iUnion_blocked (ρ : List ℕ → ℕ) : IsMeagre (⋃ p, blocked ρ p) :=
  isMeagre_iUnion fun p => (isNowhereDense_blocked ρ p).isMeagre

private theorem history_add_two (y : ℕ → ℕ) (n : ℕ) :
    history y (n + 2) = history y n ++ [y n, y (n + 1)] := by
  simp [history_succ, List.append_assoc]

/-- **Banach–Mazur, player II.** If player II wins the coded Banach–Mazur game with payoff
`outcome ⁻¹' T`, then `T` is covered by the sets blocked by the winning strategy. -/
private theorem subset_iUnion_blocked_of_iiWins {T : Set (ℕ → ℕ)} {τ : List ℕ → ℕ}
    (hτ : ∀ y, FollowsII τ y → y ∉ outcome ⁻¹' T) : T ⊆ ⋃ p, blocked τ p := by
  classical
  intro x hxT
  by_contra hx
  have hmove (p : List ℕ) (hp : Matches (prefixOf p) x) :
      ∃ a, Matches (prefixOf (p ++ [a, τ (p ++ [a])])) x := by
    by_contra! h
    exact hx (mem_iUnion.mpr ⟨p, hp, h⟩)
  -- Player I keeps the position along `x`.
  let σ : List ℕ → ℕ := fun p =>
    if h : ∃ a, Matches (prefixOf (p ++ [a, τ (p ++ [a])])) x then h.choose else 0
  let y := play σ τ
  have hmatch (n : ℕ) : Matches (prefixOf (history y (2 * n))) x := by
    induction n with
    | zero => simp [history, prefixOf_nil, Matches]
    | succ n ih =>
      have hm := hmove _ ih
      have hy₀ : y (2 * n) = σ (history y (2 * n)) := followsI_play σ τ (2 * n) (by omega)
      have hy₁ : y (2 * n + 1) = τ (history y (2 * n) ++ [σ (history y (2 * n))]) := by
        have h : y (2 * n + 1) = τ (history y (2 * n + 1)) :=
          followsII_play σ τ (2 * n + 1) (by omega)
        rw [h, history_succ, hy₀]
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, history_add_two, hy₁, hy₀]
      simpa only [σ, dite_eq_left hm] using hm.choose_spec
  refine hτ y (followsII_play σ τ) ?_
  rw [mem_preimage, outcome_eq_of_matches fun n => ⟨2 * n, by omega, hmatch n⟩]
  exact hxT

/-- **Banach–Mazur, player I.** If player I wins the coded Banach–Mazur game with payoff
`outcome ⁻¹' T` by the strategy `σ`, then, inside the basic open set given by the first move of
`σ`, the complement of `T` is covered by the sets blocked by `σ`. -/
private theorem sdiff_subset_iUnion_blocked_of_iWins {T : Set (ℕ → ℕ)} {σ : List ℕ → ℕ}
    (hσ : ∀ y, FollowsI σ y → y ∈ outcome ⁻¹' T) :
    {x | Matches (word (σ [])) x} \ T ⊆ ⋃ p, blocked σ p := by
  classical
  rintro x ⟨hx₀, hxT⟩
  by_contra hx
  have hmove (p : List ℕ) (hp : Matches (prefixOf p) x) :
      ∃ b, Matches (prefixOf (p ++ [b, σ (p ++ [b])])) x := by
    by_contra! h
    exact hx (mem_iUnion.mpr ⟨p, hp, h⟩)
  -- Player II keeps the position along `x`.
  let τ : List ℕ → ℕ := fun p =>
    if h : ∃ b, Matches (prefixOf (p ++ [b, σ (p ++ [b])])) x then h.choose else 0
  let y := play σ τ
  have hmatch (n : ℕ) : Matches (prefixOf (history y (2 * n + 1))) x := by
    induction n with
    | zero =>
      have hy₀ : y 0 = σ [] := followsI_play σ τ 0 rfl
      rw [show 2 * 0 + 1 = 0 + 1 by rfl, history_succ, hy₀]
      simpa [history, prefixOf_singleton] using hx₀
    | succ n ih =>
      have hm := hmove _ ih
      have hy₁ : y (2 * n + 1) = τ (history y (2 * n + 1)) :=
        followsII_play σ τ (2 * n + 1) (by omega)
      have hy₂ : y (2 * n + 1 + 1) =
          σ (history y (2 * n + 1) ++ [τ (history y (2 * n + 1))]) := by
        have h : y (2 * n + 1 + 1) = σ (history y (2 * n + 1 + 1)) :=
          followsI_play σ τ (2 * n + 1 + 1) (by omega)
        rw [h, history_succ, hy₁]
      rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring, history_add_two, hy₂, hy₁]
      simpa only [τ, dite_eq_left hm] using hm.choose_spec
  have h := hσ y (followsI_play σ τ)
  rw [mem_preimage, outcome_eq_of_matches fun n => ⟨2 * n + 1, by omega, hmatch n⟩] at h
  exact hxT h

/-- **Property of Baire from determinacy.** Let `Γ` be a family of subsets of Baire space
`ℕ^ℕ`, closed under preimages by Borel maps `ℕ^ℕ → ℕ^ℕ`, all of whose members are determined.
Then every member of `Γ` has the property of Baire (S. Banach and S. Mazur, Problem 43 of the
Scottish Book; J. C. Oxtoby, *The Banach–Mazur game and Banach category theorem*, Ann. of Math.
Stud. 39 (1957); Moschovakis, *Descriptive Set Theory*, 2nd ed., AMS 2009, 6A.13–6A.16). -/
public theorem baireMeasurableSet_of_determined {Γ : Set (Set (ℕ → ℕ))}
    (hΓ : ∀ f : (ℕ → ℕ) → ℕ → ℕ, Measurable f → ∀ B ∈ Γ, f ⁻¹' B ∈ Γ)
    (hdet : ∀ B ∈ Γ, Determined B) {S : Set (ℕ → ℕ)} (hS : S ∈ Γ) :
    BaireMeasurableSet S := by
  classical
  by_cases huniv : S = univ
  · rw [huniv]
    exact isOpen_univ.baireMeasurableSet
  obtain ⟨q, hq⟩ : ∃ q, q ∉ S := by
    by_contra! h
    exact huniv (eq_univ_of_forall h)
  -- The union of the basic open sets in which `S` is comeagre.
  let C : List ℕ → Set (ℕ → ℕ) := fun w => {x | Matches w x}
  let U : Set (ℕ → ℕ) := ⋃ w : {w : List ℕ // IsMeagre (C w \ S)}, C w.val
  have hUo : IsOpen U := isOpen_iUnion fun w => (isClopen_setOf_matches w.val).isOpen
  have hUS : IsMeagre (U \ S) := by
    rw [iUnion_sdiff]
    exact isMeagre_iUnion fun w => w.property
  -- `S \ U` is a Borel preimage of `S`, so its coded Banach–Mazur game is determined.
  have hT : S \ U ∈ Γ := by
    have hg : Measurable fun x => if x ∈ U then q else x :=
      Measurable.ite hUo.measurableSet measurable_const measurable_id
    convert hΓ _ hg S hS using 1
    ext x
    by_cases hx : x ∈ U <;> simp [hx, hq]
  have hSU : IsMeagre (S \ U) := by
    rcases hdet _ (hΓ outcome continuous_outcome.measurable _ hT) with ⟨σ, hσ⟩ | ⟨τ, hτ⟩
    · -- A win for player I makes `S` comeagre in a basic open set inside `U`, which `S \ U`
      -- misses: this contradicts the Baire category theorem.
      exfalso
      have h₁ : IsMeagre (C (word (σ [])) \ (S \ U)) :=
        (isMeagre_iUnion_blocked σ).mono (sdiff_subset_iUnion_blocked_of_iWins hσ)
      have h₂ : C (word (σ [])) ⊆ U :=
        subset_iUnion_of_subset ⟨word (σ []), h₁.mono (sdiff_subset_sdiff_right sdiff_subset)⟩
          subset_rfl
      have h₃ : C (word (σ [])) \ (S \ U) = C (word (σ [])) :=
        sdiff_eq_left.mpr (disjoint_sdiff_left.mono_right h₂).symm
      rw [h₃] at h₁
      exact not_isMeagre_of_isOpen (isClopen_setOf_matches _).isOpen
        ⟨_, matches_extendByZero _⟩ h₁
    · exact (isMeagre_iUnion_blocked τ).mono (subset_iUnion_blocked_of_iiWins hτ)
  rw [BaireMeasurableSet.iff_residualEq_isOpen]
  refine ⟨U, hUo, ?_⟩
  rw [Filter.eventuallyEqSet_iff]
  filter_upwards [hSU, hUS] with x hx₁ hx₂
  simp only [mem_compl_iff, mem_sdiff, not_and, not_not] at hx₁ hx₂
  exact ⟨hx₁, hx₂⟩

end MathlibExt.SetTheory.DeterminacyWanted
