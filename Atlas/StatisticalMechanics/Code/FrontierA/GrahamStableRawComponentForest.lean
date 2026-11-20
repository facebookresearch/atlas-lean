/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamStableRawHoleCollisionSplit








open Finset

namespace StatMech.GrahamGHS.FourColor

universe u v uI uW

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]



structure FiniteRankTerminalSystem (A B : Type*) where
  rank : A -> Nat
  terminals : A -> Finset B
  children : A -> Finset A
  children_rank_lt : ∀ a child, child ∈ children a -> rank child < rank a




noncomputable def FiniteRankTerminalSystem.terminalClosure
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (system : FiniteRankTerminalSystem A B) (a : A) : Finset B :=
  system.terminals a ∪ (system.children a).attach.biUnion
    (fun child => system.terminalClosure child.1)
termination_by system.rank a
decreasing_by exact system.children_rank_lt a child.1 child.2


def FiniteRankTerminalSystem.ReachesTerminal
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (system : FiniteRankTerminalSystem A B) (a : A) (terminal : B) : Prop :=
  terminal ∈ system.terminalClosure a

theorem FiniteRankTerminalSystem.terminalClosure_eq
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (system : FiniteRankTerminalSystem A B) (a : A) :
    system.terminalClosure a =
      system.terminals a ∪ (system.children a).attach.biUnion
        (fun child => system.terminalClosure child.1) := by
  rw [FiniteRankTerminalSystem.terminalClosure]

theorem FiniteRankTerminalSystem.terminals_subset_terminalClosure
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (system : FiniteRankTerminalSystem A B) (a : A) :
    system.terminals a ⊆ system.terminalClosure a := by
  rw [system.terminalClosure_eq]
  exact Finset.subset_union_left

theorem FiniteRankTerminalSystem.terminalClosure_subset_of_mem_children
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (system : FiniteRankTerminalSystem A B) {a child : A}
    (hchild : child ∈ system.children a) :
    system.terminalClosure child ⊆ system.terminalClosure a := by
  intro terminal hterminal
  rw [system.terminalClosure_eq a]
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr
    ⟨⟨child, hchild⟩, Finset.mem_attach _ _, hterminal⟩



theorem FiniteRankTerminalSystem.exists_terminalEmbedding_of_hall
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (system : FiniteRankTerminalSystem A B)
    (hhall : ∀ sources : Finset A,
      sources.card ≤ (sources.biUnion system.terminalClosure).card) :
    ∃ matching : A ↪ B,
      ∀ source, system.ReachesTerminal source (matching source) := by
  obtain ⟨matching, hinjective, hterminal⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective
      system.terminalClosure).mp hhall
  exact ⟨⟨matching, hinjective⟩, hterminal⟩




theorem exists_minimal_deficiency_one_family
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (neighborhood : Finset A -> Finset B)
    (hmono : Monotone neighborhood)
    (hfail : ∃ sources : Finset A,
      (neighborhood sources).card < sources.card) :
    ∃ sources : Finset A,
      sources.Nonempty ∧
        (neighborhood sources).card + 1 = sources.card ∧
        (∀ source ∈ sources,
          neighborhood (sources.erase source) = neighborhood sources) ∧
        ∀ smaller : Finset A, smaller ⊂ sources ->
          smaller.card ≤ (neighborhood smaller).card := by
  classical
  let bad : Finset (Finset A) := Finset.univ.filter fun sources =>
    (neighborhood sources).card < sources.card
  have hbad : bad.Nonempty := by
    obtain ⟨sources, hsources⟩ := hfail
    refine ⟨sources, ?_⟩
    simpa only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
  obtain ⟨sources, hsourcesBad, hsourcesMinimal⟩ :=
    bad.exists_min_image Finset.card hbad
  have hdeficit : (neighborhood sources).card < sources.card := by
    simpa only [bad, Finset.mem_filter, Finset.mem_univ, true_and] using
      hsourcesBad
  have hsourcesNonempty : sources.Nonempty :=
    Finset.card_pos.mp (Nat.zero_lt_of_lt hdeficit)
  have hproper : ∀ smaller : Finset A, smaller ⊂ sources ->
      smaller.card ≤ (neighborhood smaller).card := by
    intro smaller hsmaller
    by_contra hnot
    have hsmallerBad : smaller ∈ bad := by
      simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hminimal := hsourcesMinimal smaller hsmallerBad
    have hcard := Finset.card_lt_card hsmaller
    omega
  have heraseHall : ∀ source ∈ sources,
      (sources.erase source).card ≤
        (neighborhood (sources.erase source)).card := by
    intro source hsource
    exact hproper (sources.erase source)
      (Finset.erase_ssubset hsource)
  have herase : ∀ source ∈ sources,
      neighborhood (sources.erase source) = neighborhood sources := by
    intro source hsource
    have hsubset := hmono (Finset.erase_subset source sources)
    apply Finset.eq_of_subset_of_card_le hsubset
    have hhall := heraseHall source hsource
    rw [Finset.card_erase_of_mem hsource] at hhall
    omega
  have htight : (neighborhood sources).card + 1 = sources.card := by
    obtain ⟨source, hsource⟩ := hsourcesNonempty
    have hhall := heraseHall source hsource
    rw [herase source hsource, Finset.card_erase_of_mem hsource] at hhall
    omega
  exact ⟨sources, hsourcesNonempty, htight, herase, hproper⟩



noncomputable def finiteBipartiteRelationNeighborhood
    {A : Type u} {B : Type v} [Fintype B]
    (related : A -> B -> Prop) (sources : Finset A) : Finset B := by
  classical
  exact Finset.univ.filter fun token =>
    ∃ source ∈ sources, related source token

theorem finiteBipartiteRelationNeighborhood_mono
    {A : Type u} {B : Type v} [Fintype B]
    (related : A -> B -> Prop) :
    Monotone (finiteBipartiteRelationNeighborhood related) := by
  classical
  intro smaller larger hsubset token htoken
  obtain ⟨source, hsource, hrelated⟩ :=
    (Finset.mem_filter.mp htoken).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ token,
    source, hsubset hsource, hrelated⟩






structure FiniteRelationMinimalTightProblem where
  State : Type u
  Token : Type v
  [stateFintype : Fintype State]
  [stateDecidableEq : DecidableEq State]
  [tokenFintype : Fintype Token]
  [tokenDecidableEq : DecidableEq Token]
  incident : State -> Token -> Prop
  carrier : Finset State
  nonempty : carrier.Nonempty
  deficiency_one :
    (finiteBipartiteRelationNeighborhood incident carrier).card + 1 =
      carrier.card
  erase_invariant : ∀ source ∈ carrier,
    finiteBipartiteRelationNeighborhood incident (carrier.erase source) =
      finiteBipartiteRelationNeighborhood incident carrier
  proper_hall : ∀ smaller : Finset State, smaller ⊂ carrier ->
    smaller.card ≤
      (finiteBipartiteRelationNeighborhood incident smaller).card

attribute [instance]
  FiniteRelationMinimalTightProblem.stateFintype
  FiniteRelationMinimalTightProblem.stateDecidableEq
  FiniteRelationMinimalTightProblem.tokenFintype
  FiniteRelationMinimalTightProblem.tokenDecidableEq

abbrev FiniteRelationMinimalTightProblem.StateCarrier
    (problem : FiniteRelationMinimalTightProblem.{u, v}) :=
  ↑problem.carrier



def FiniteRelationMinimalTightProblem.rank
    (problem : FiniteRelationMinimalTightProblem.{u, v}) : Nat :=
  Fintype.card problem.StateCarrier

@[simp] theorem FiniteRelationMinimalTightProblem.rank_eq_carrier_card
    (problem : FiniteRelationMinimalTightProblem.{u, v}) :
    problem.rank = problem.carrier.card := by
  simp [FiniteRelationMinimalTightProblem.rank]



theorem FiniteRelationMinimalTightProblem.strongInduction
    (motive : FiniteRelationMinimalTightProblem.{u, v} -> Prop)
    (step : ∀ problem,
      (∀ smaller, smaller.rank < problem.rank -> motive smaller) ->
        motive problem)
    (problem : FiniteRelationMinimalTightProblem.{u, v}) :
    motive problem := by
  induction hrank : problem.rank using Nat.strong_induction_on
      generalizing problem with
  | h rank ih =>
      apply step problem
      intro smaller hsmaller
      exact ih smaller.rank (by simpa only [hrank] using hsmaller) smaller rfl


noncomputable abbrev FiniteRelationMinimalTightProblem.TokenCarrier
    (problem : FiniteRelationMinimalTightProblem.{u, v}) :=
  ↑(finiteBipartiteRelationNeighborhood problem.incident problem.carrier)



noncomputable def FiniteRelationMinimalTightProblem.restrictedIncident
    (problem : FiniteRelationMinimalTightProblem.{u, v}) :
    problem.StateCarrier -> problem.TokenCarrier -> Prop :=
  fun state token => problem.incident state.1 token.1

theorem FiniteRelationMinimalTightProblem.tokenCarrier_card_lt_stateCarrier
    (problem : FiniteRelationMinimalTightProblem.{u, v}) :
    Fintype.card problem.TokenCarrier <
      Fintype.card problem.StateCarrier := by
  have htight := problem.deficiency_one
  simpa only [FiniteRelationMinimalTightProblem.TokenCarrier,
    FiniteRelationMinimalTightProblem.StateCarrier, Fintype.card_coe] using
      (show (finiteBipartiteRelationNeighborhood
        problem.incident problem.carrier).card < problem.carrier.card by
        omega)



theorem FiniteRelationMinimalTightProblem.exists_holeState
    (problem : FiniteRelationMinimalTightProblem.{u, v}) :
    Nonempty (StatMech.FrontierA.RelationPartialMatching.HoleState
      problem.restrictedIncident) :=
  StatMech.FrontierA.RelationPartialMatching.exists_holeState_of_card_lt
    problem.restrictedIncident problem.tokenCarrier_card_lt_stateCarrier




theorem FiniteRelationMinimalTightProblem.strongInductionWithHoleState
    (motive : FiniteRelationMinimalTightProblem.{u, v} -> Prop)
    (step : ∀ problem,
      Nonempty (StatMech.FrontierA.RelationPartialMatching.HoleState
        problem.restrictedIncident) ->
      (∀ smaller, smaller.rank < problem.rank -> motive smaller) ->
        motive problem)
    (problem : FiniteRelationMinimalTightProblem.{u, v}) :
    motive problem := by
  apply problem.strongInduction motive
  intro current ih
  exact step current current.exists_holeState ih





theorem exists_external_incident_of_tight_properHall
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (related : A -> B -> Prop) [DecidableRel related]
    (htight : Fintype.card B + 1 = Fintype.card A)
    (hproper : ∀ smaller : Finset A, smaller ⊂ Finset.univ ->
      smaller.card ≤
        (Finset.univ.filter fun token =>
          ∃ source ∈ smaller, related source token).card)
    (size : Nat) (hsize : 0 < size)
    (states : Fin size ↪ A) (tokens : Fin size ↪ B) :
    ∃ i : Fin size, ∃ source : A,
      (∀ q, source ≠ states q) ∧ related source (tokens i) := by
  classical
  let stateBlock : Finset A := Finset.univ.map states
  let tokenBlock : Finset B := Finset.univ.map tokens
  let remaining : Finset A := Finset.univ \ stateBlock
  by_contra hno
  have havoid : ∀ source ∈ remaining, ∀ token ∈ tokenBlock,
      ¬ related source token := by
    intro source hsource token htoken hrelated
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp htoken
    apply hno
    refine ⟨i, source, ?_, hrelated⟩
    intro q hsourceEq
    exact (Finset.mem_sdiff.mp hsource).2
      (Finset.mem_map.mpr
        ⟨q, Finset.mem_univ q, hsourceEq.symm⟩)
  let first : Fin size := ⟨0, hsize⟩
  have hremainingProper : remaining ⊂ (Finset.univ : Finset A) := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.sdiff_subset, ?_⟩
    intro heq
    have hfirstRemaining : states first ∈ remaining := by
      rw [heq]
      exact Finset.mem_univ _
    exact (Finset.mem_sdiff.mp hfirstRemaining).2
      (Finset.mem_map.mpr ⟨first, Finset.mem_univ first, rfl⟩)
  let neighborhood : Finset A -> Finset B := fun family =>
    Finset.univ.filter fun token =>
      ∃ source ∈ family, related source token
  have hneighborhoodSubset : neighborhood remaining ⊆
      Finset.univ \ tokenBlock := by
    intro token htoken
    obtain ⟨_huniv, source, hsource, hrelated⟩ :=
      Finset.mem_filter.mp htoken
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ token, fun htokenBlock =>
      havoid source hsource token htokenBlock hrelated⟩
  have hhall : remaining.card ≤ (neighborhood remaining).card := by
    exact hproper remaining hremainingProper
  have hneighborhoodCard : (neighborhood remaining).card ≤
      (Finset.univ \ tokenBlock).card :=
    Finset.card_le_card hneighborhoodSubset
  have hstateBlockCard : stateBlock.card = size := by
    simpa only [stateBlock, Finset.card_map, Finset.card_univ,
      Fintype.card_fin]
  have htokenBlockCard : tokenBlock.card = size := by
    simpa only [tokenBlock, Finset.card_map, Finset.card_univ,
      Fintype.card_fin]
  have hremainingCard : remaining.card = Fintype.card A - size := by
    change (Finset.univ \ stateBlock).card = Fintype.card A - size
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ stateBlock),
      Finset.card_univ, hstateBlockCard]
  have htokenRemainingCard : (Finset.univ \ tokenBlock).card =
      Fintype.card B - size := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ tokenBlock),
      Finset.card_univ, htokenBlockCard]
  have hsizeB : size ≤ Fintype.card B := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective tokens tokens.injective
  rw [hremainingCard] at hhall
  rw [htokenRemainingCard] at hneighborhoodCard
  omega



theorem finiteEmbedding_add_fresh
    {A : Type*} (size : Nat) (block : Fin size ↪ A) (extra : A)
    (hfresh : ∀ i, extra ≠ block i) :
    Nonempty (Fin (size + 1) ↪ A) := by
  let f : Fin size ⊕ Fin 1 → A
    | Sum.inl i => block i
    | Sum.inr _ => extra
  have hinjective : Function.Injective f := by
    intro x y hxy
    cases x with
    | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (block.injective hxy)
        | inr y => exact False.elim (hfresh x hxy.symm)
    | inr x =>
        cases y with
        | inl y => exact False.elim (hfresh y hxy)
        | inr y => exact congrArg Sum.inr (Subsingleton.elim x y)
  let extended : Fin size ⊕ Fin 1 ↪ A := ⟨f, hinjective⟩
  exact ⟨(finSumFinEquiv (m := size) (n := 1)).symm.toEmbedding.trans extended⟩


theorem finiteEmbedding_snoc
    {A : Type*} (size : Nat) (block : Fin size ↪ A) (extra : A)
    (hfresh : ∀ i, extra ≠ block i) :
    ∃ extended : Fin (size + 1) ↪ A,
      (∀ i, extended i.castSucc = block i) ∧
      extended (Fin.last size) = extra := by
  let f : Fin (size + 1) -> A :=
    Fin.lastCases extra (fun i => block i)
  have hinjective : Function.Injective f := by
    intro x
    refine Fin.lastCases ?_ (fun i => ?_) x
    · intro y
      refine Fin.lastCases ?_ (fun q h => ?_) y
      · intro _
        rfl
      · exact False.elim (hfresh q (by simpa only [f,
          Fin.lastCases_last, Fin.lastCases_castSucc] using h))
    · intro y
      refine Fin.lastCases ?_ (fun q h => ?_) y
      · intro h
        exact False.elim (hfresh i (by simpa only [f,
          Fin.lastCases_last, Fin.lastCases_castSucc] using h.symm))
      · exact congrArg Fin.castSucc (block.injective (by simpa only [f,
          Fin.lastCases_castSucc] using h))
  let extended : Fin (size + 1) ↪ A := ⟨f, hinjective⟩
  refine ⟨extended, ?_, ?_⟩
  · intro i
    change f i.castSucc = block i
    exact Fin.lastCases_castSucc i
  · change f (Fin.last size) = extra
    exact Fin.lastCases_last


noncomputable def finiteEmbedding_replaceAt
    {A : Type*} {size : Nat} (block : Fin size ↪ A) (extra : A)
    (hfresh : ∀ i, extra ≠ block i) (index : Fin size) : Fin size ↪ A where
  toFun i := if i = index then extra else block i
  inj' := by
    intro x y hxy
    by_cases hx : x = index
    · subst x
      by_cases hy : y = index
      · exact hy.symm
      · exfalso
        apply hfresh y
        simpa only [if_pos, if_neg, hy] using hxy
    · by_cases hy : y = index
      · subst y
        exfalso
        apply hfresh x
        simpa only [if_pos, if_neg, hx] using hxy.symm
      · exact block.injective (by
          simpa only [if_neg, hx, hy] using hxy)

@[simp] theorem finiteEmbedding_replaceAt_same
    {A : Type*} {size : Nat} (block : Fin size ↪ A) (extra : A)
    (hfresh : ∀ i, extra ≠ block i) (index : Fin size) :
    finiteEmbedding_replaceAt block extra hfresh index index = extra := by
  change (if index = index then extra else block index) = extra
  rw [if_pos rfl]

theorem finiteEmbedding_replaceAt_ne
    {A : Type*} {size : Nat} (block : Fin size ↪ A) (extra : A)
    (hfresh : ∀ i, extra ≠ block i) (index other : Fin size)
    (hne : other ≠ index) :
    finiteEmbedding_replaceAt block extra hfresh index other = block other := by
  change (if other = index then extra else block other) = block other
  rw [if_neg hne]


theorem finiteEmbedding_replaceAt_displaced_fresh
    {A : Type*} {size : Nat} (block : Fin size ↪ A) (extra : A)
    (hfresh : ∀ i, extra ≠ block i) (index : Fin size) :
    ∀ other, block index ≠ finiteEmbedding_replaceAt block extra hfresh index other := by
  intro other
  by_cases hother : other = index
  · subst other
    rw [finiteEmbedding_replaceAt_same]
    exact (hfresh index).symm
  · rw [finiteEmbedding_replaceAt_ne block extra hfresh index other hother]
    intro heq
    exact hother (block.injective heq.symm)


theorem exists_fin_castSucc_eq_of_ne_last
    {size : Nat} (q : Fin (size + 1)) (hq : q ≠ Fin.last size) :
    ∃ i : Fin size, i.castSucc = q := by
  have hlt : q < Fin.last size := Fin.lt_last_iff_ne_last.mpr hq
  let i : Fin size := ⟨q.1, hlt⟩
  exact ⟨i, Fin.ext (by rfl)⟩



theorem exists_fin_castSucc_eq_left_or_right_of_ne
    {size : Nat} (q r : Fin (size + 1)) (hqr : q ≠ r) :
    ∃ i : Fin size, i.castSucc = q ∨ i.castSucc = r := by
  by_cases hq : q = Fin.last size
  · have hr : r ≠ Fin.last size := by
      intro hr
      exact hqr (hq.trans hr.symm)
    obtain ⟨i, hi⟩ := exists_fin_castSucc_eq_of_ne_last r hr
    exact ⟨i, Or.inr hi⟩
  · obtain ⟨i, hi⟩ := exists_fin_castSucc_eq_of_ne_last q hq
    exact ⟨i, Or.inl hi⟩



theorem saturatedHoleState_sourceEmbedding_add_hole
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (state : StatMech.FrontierA.RelationPartialMatching.HoleState r)
    (hsaturated : ∀ token, ∃ source,
      state.matching.toFun source = some token)
    (size : Nat) (tokens : Fin size ↪ B) :
    Nonempty (Fin (size + 1) ↪ A) := by
  classical
  let preimage : B ↪ A :=
    ⟨state.matching.targetPreimage hsaturated,
      state.matching.targetPreimage_injective hsaturated⟩
  let occupants : Fin size ↪ A := tokens.trans preimage
  have hfresh : ∀ i, state.hole ≠ occupants i := by
    intro i heq
    apply state.hole_unmatched
    apply (StatMech.FrontierA.RelationPartialMatching.mem_support_iff
      state.matching state.hole).2
    refine ⟨tokens i, ?_⟩
    rw [heq]
    exact state.matching.targetPreimage_spec hsaturated (tokens i)
  exact finiteEmbedding_add_fresh size occupants state.hole hfresh



theorem saturatedHoleState_targetPreimage_fresh_of_token_fresh
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (state : StatMech.FrontierA.RelationPartialMatching.HoleState r)
    (hsaturated : ∀ token, ∃ source,
      state.matching.toFun source = some token)
    (size : Nat) (sources : Fin size ↪ A) (tokens : Fin size ↪ B)
    (hmatched : ∀ i,
      state.matching.toFun (sources i) = some (tokens i))
    (fresh : B) (hfresh : ∀ i, fresh ≠ tokens i) :
    ∀ i, state.matching.targetPreimage hsaturated fresh ≠ sources i := by
  intro i heq
  apply hfresh i
  apply Option.some.inj
  exact (state.matching.targetPreimage_spec hsaturated fresh).symm.trans
    (heq ▸ hmatched i)




theorem saturatedHoleState_extendMatchedBlock
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (state : StatMech.FrontierA.RelationPartialMatching.HoleState r)
    (hsaturated : ∀ token, ∃ source,
      state.matching.toFun source = some token)
    (size : Nat) (sources : Fin size ↪ A) (tokens : Fin size ↪ B)
    (hmatched : ∀ i,
      state.matching.toFun (sources i) = some (tokens i))
    (fresh : B) (hfresh : ∀ i, fresh ≠ tokens i) :
    ∃ extendedSources : (Fin size ⊕ Fin 1) ↪ A,
      ∃ extendedTokens : (Fin size ⊕ Fin 1) ↪ B,
        (∀ q, state.matching.toFun (extendedSources q) =
          some (extendedTokens q)) ∧
        (∀ i, extendedSources (Sum.inl i) = sources i) ∧
        (∀ i, extendedTokens (Sum.inl i) = tokens i) ∧
        extendedTokens (Sum.inr 0) = fresh := by
  let newSource := state.matching.targetPreimage hsaturated fresh
  have hsourceFresh : ∀ i, newSource ≠ sources i :=
    saturatedHoleState_targetPreimage_fresh_of_token_fresh
      state hsaturated size sources tokens hmatched fresh hfresh
  let sourceMap : Fin size ⊕ Fin 1 -> A
    | Sum.inl i => sources i
    | Sum.inr _ => newSource
  have hsourceInjective : Function.Injective sourceMap := by
    intro x y hxy
    cases x with
    | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (sources.injective hxy)
        | inr y => exact False.elim (hsourceFresh x hxy.symm)
    | inr x =>
        cases y with
        | inl y => exact False.elim (hsourceFresh y hxy)
        | inr y => exact congrArg Sum.inr (Subsingleton.elim x y)
  let tokenMap : Fin size ⊕ Fin 1 -> B
    | Sum.inl i => tokens i
    | Sum.inr _ => fresh
  have htokenInjective : Function.Injective tokenMap := by
    intro x y hxy
    cases x with
    | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (tokens.injective hxy)
        | inr y => exact False.elim (hfresh x hxy.symm)
    | inr x =>
        cases y with
        | inl y => exact False.elim (hfresh y hxy)
        | inr y => exact congrArg Sum.inr (Subsingleton.elim x y)
  let extendedSources : (Fin size ⊕ Fin 1) ↪ A :=
    ⟨sourceMap, hsourceInjective⟩
  let extendedTokens : (Fin size ⊕ Fin 1) ↪ B :=
    ⟨tokenMap, htokenInjective⟩
  refine ⟨extendedSources, extendedTokens, ?_, ?_, ?_, rfl⟩
  · intro q
    cases q with
    | inl i => exact hmatched i
    | inr i =>
        exact state.matching.targetPreimage_spec hsaturated fresh
  · intro i
    rfl
  · intro i
    rfl



theorem saturatedHoleState_alternatingPath_nextSource_fresh
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (state : StatMech.FrontierA.RelationPartialMatching.HoleState r)
    (hsaturated : ∀ token, ∃ source,
      state.matching.toFun source = some token)
    (size : Nat) (sources : Fin (size + 1) ↪ A)
    (tokens : Fin size ↪ B)
    (hhole : sources 0 = state.hole)
    (hmatched : ∀ i,
      state.matching.toFun (sources i.succ) = some (tokens i))
    (fresh : B) (hfresh : ∀ i, fresh ≠ tokens i) :
    ∀ q, state.matching.targetPreimage hsaturated fresh ≠ sources q := by
  intro q
  refine Fin.cases ?_ (fun i => ?_) q
  · intro heq
    apply state.hole_unmatched
    apply (StatMech.FrontierA.RelationPartialMatching.mem_support_iff
      state.matching state.hole).2
    refine ⟨fresh, ?_⟩
    rw [← hhole, ← heq]
    exact state.matching.targetPreimage_spec hsaturated fresh
  · intro heq
    apply hfresh i
    apply Option.some.inj
    exact (state.matching.targetPreimage_spec hsaturated fresh).symm.trans
      (heq ▸ hmatched i)




theorem saturatedHoleState_alternatingPath_close_or_extend
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (state : StatMech.FrontierA.RelationPartialMatching.HoleState r)
    (hsaturated : ∀ token, ∃ source,
      state.matching.toFun source = some token)
    (successor : A -> B)
    (size : Nat) (sources : Fin (size + 1) ↪ A)
    (tokens : Fin size ↪ B)
    (hhole : sources 0 = state.hole)
    (htransition : ∀ i, tokens i = successor (sources i.castSucc))
    (hmatched : ∀ i,
      state.matching.toFun (sources i.succ) = some (tokens i)) :
    (∃ i, successor (sources (Fin.last size)) = tokens i ∧
      state.matching.targetPreimage hsaturated
          (successor (sources (Fin.last size))) = sources i.succ) ∨
      ∃ extendedSources : Fin (size + 2) ↪ A,
        ∃ extendedTokens : Fin (size + 1) ↪ B,
          extendedSources 0 = state.hole ∧
          (∀ i, extendedTokens i =
            successor (extendedSources i.castSucc)) ∧
          (∀ i, state.matching.toFun (extendedSources i.succ) =
            some (extendedTokens i)) ∧
          (∀ i, extendedSources i.castSucc = sources i) ∧
          (∀ i, extendedTokens i.castSucc = tokens i) := by
  let nextToken := successor (sources (Fin.last size))
  by_cases hrepeats : ∃ i, nextToken = tokens i
  · obtain ⟨i, hi⟩ := hrepeats
    left
    refine ⟨i, hi, ?_⟩
    apply state.matching.injective_some
    · exact state.matching.targetPreimage_spec hsaturated nextToken
    · exact (hmatched i).trans (congrArg some hi.symm)
  · have hfresh : ∀ i, nextToken ≠ tokens i := by
      intro i hi
      exact hrepeats ⟨i, hi⟩
    let nextSource := state.matching.targetPreimage hsaturated nextToken
    have hsourceFresh : ∀ q, nextSource ≠ sources q :=
      saturatedHoleState_alternatingPath_nextSource_fresh
        state hsaturated size sources tokens hhole hmatched nextToken hfresh
    obtain ⟨extendedSources, hsourcePrefix, hsourceLast⟩ :=
      finiteEmbedding_snoc (size + 1) sources nextSource hsourceFresh
    obtain ⟨extendedTokens, htokenPrefix, htokenLast⟩ :=
      finiteEmbedding_snoc size tokens nextToken hfresh
    right
    refine ⟨extendedSources, extendedTokens, ?_, ?_, ?_,
      hsourcePrefix, htokenPrefix⟩
    · calc
        extendedSources 0 = sources 0 := hsourcePrefix 0
        _ = state.hole := hhole
    · intro i
      refine Fin.lastCases ?_ (fun q => ?_) i
      · calc
          extendedTokens (Fin.last size) = nextToken := htokenLast
          _ = successor (sources (Fin.last size)) := rfl
          _ = successor (extendedSources (Fin.last size).castSucc) :=
            congrArg successor (hsourcePrefix (Fin.last size)).symm
      · calc
          extendedTokens q.castSucc = tokens q := htokenPrefix q
          _ = successor (sources q.castSucc) := htransition q
          _ = successor (extendedSources q.castSucc.castSucc) :=
            congrArg successor (hsourcePrefix q.castSucc).symm
    · intro i
      refine Fin.lastCases ?_ (fun q => ?_) i
      · have hlastSucc : (Fin.last size).succ = Fin.last (size + 1) := by
          apply Fin.ext
          rfl
        rw [hlastSucc, hsourceLast, htokenLast]
        exact state.matching.targetPreimage_spec hsaturated nextToken
      · have hsuccCast : q.castSucc.succ = q.succ.castSucc := by
          apply Fin.ext
          rfl
        rw [hsuccCast, hsourcePrefix q.succ, htokenPrefix q]
        exact hmatched q


def finiteEmbeddingBlock
    {A : Type*} [Fintype A] [DecidableEq A]
    (size : Nat) (block : Fin size ↪ A) : Finset A :=
  Finset.univ.map block


abbrev FiniteEmbeddingComplement
    {A : Type*} [Fintype A] [DecidableEq A]
    (size : Nat) (block : Fin size ↪ A) :=
  {a : A // a ∉ finiteEmbeddingBlock size block}


theorem finiteEmbeddingComplement_card
    {A : Type*} [Fintype A] [DecidableEq A]
    (size : Nat) (block : Fin size ↪ A) :
    Fintype.card (FiniteEmbeddingComplement size block) =
      Fintype.card A - size := by
  classical
  let P := fun a : A => a ∈ finiteEmbeddingBlock size block
  have hsplit := Fintype.card_subtype_compl P
  have hblock : Fintype.card {a : A // P a} = size := by
    simpa only [P, Fintype.card_coe, finiteEmbeddingBlock,
      Finset.card_map, Finset.card_univ, Fintype.card_fin]
  simpa only [P, hblock] using hsplit



def FiniteRelationBlockClosed
    {A B : Type*} (related : A -> B -> Prop) (size : Nat)
    (sources : Fin size ↪ A) (tokens : Fin size ↪ B) : Prop :=
  ∀ source token, related source token ->
    ((∃ i, source = sources i) ↔ ∃ i, token = tokens i)



def FiniteRelationTokenClosed
    {A B : Type*} (related : A -> B -> Prop) (size : Nat)
    (sources : Fin size ↪ A) (tokens : Fin size ↪ B) : Prop :=
  ∀ source token, related source token ->
    (∃ i, token = tokens i) -> ∃ i, source = sources i



def finiteRelationComplement
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (related : A -> B -> Prop) (size : Nat)
    (sources : Fin size ↪ A) (tokens : Fin size ↪ B) :
    FiniteEmbeddingComplement size sources ->
      FiniteEmbeddingComplement size tokens -> Prop :=
  fun source token => related source.1 token.1



theorem finiteRelationComplement_closed
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (related : A -> B -> Prop) (size : Nat)
    (sources : Fin size ↪ A) (tokens : Fin size ↪ B)
    (hclosed : FiniteRelationBlockClosed related size sources tokens)
    (source : FiniteEmbeddingComplement size sources) (token : B)
    (hrelated : related source.1 token) :
    token ∉ finiteEmbeddingBlock size tokens := by
  intro hmem
  obtain ⟨i, _hi, heq⟩ := Finset.mem_map.mp hmem
  have hsourceMem : ∃ q, source.1 = sources q :=
    (hclosed source.1 token hrelated).2 ⟨i, heq.symm⟩
  obtain ⟨q, hq⟩ := hsourceMem
  apply source.2
  apply Finset.mem_map.mpr
  exact ⟨q, Finset.mem_univ _, hq.symm⟩



theorem finiteRelationBlockClosed_or_crossing
    {A B : Type*} (related : A -> B -> Prop) (size : Nat)
    (sources : Fin size ↪ A) (tokens : Fin size ↪ B) :
    FiniteRelationBlockClosed related size sources tokens ∨
      ∃ source token, related source token ∧
        (((∃ i, source = sources i) ∧ ∀ i, token ≠ tokens i) ∨
          ((∀ i, source ≠ sources i) ∧ ∃ i, token = tokens i)) := by
  classical
  by_cases hclosed : FiniteRelationBlockClosed related size sources tokens
  · exact Or.inl hclosed
  · right
    unfold FiniteRelationBlockClosed at hclosed
    push Not at hclosed
    obtain ⟨source, token, hrelated, hnot⟩ := hclosed
    refine ⟨source, token, hrelated, ?_⟩
    tauto



theorem finiteRelationTokenClosed_or_crossing
    {A B : Type*} (related : A -> B -> Prop) (size : Nat)
    (sources : Fin size ↪ A) (tokens : Fin size ↪ B) :
    FiniteRelationTokenClosed related size sources tokens ∨
      ∃ source token, related source token ∧
        (∀ i, source ≠ sources i) ∧ ∃ i, token = tokens i := by
  classical
  by_cases hclosed : FiniteRelationTokenClosed related size sources tokens
  · exact Or.inl hclosed
  · right
    unfold FiniteRelationTokenClosed at hclosed
    push Not at hclosed
    obtain ⟨source, token, hrelated, htoken, hsource⟩ := hclosed
    exact ⟨source, token, hrelated, hsource, htoken⟩



theorem finiteRelationComplement_tokenClosed
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (related : A -> B -> Prop) (size : Nat)
    (sources : Fin size ↪ A) (tokens : Fin size ↪ B)
    (hclosed : FiniteRelationTokenClosed related size sources tokens)
    (source : FiniteEmbeddingComplement size sources) (token : B)
    (hrelated : related source.1 token) :
    token ∉ finiteEmbeddingBlock size tokens := by
  intro hmem
  obtain ⟨i, _hi, heq⟩ := Finset.mem_map.mp hmem
  obtain ⟨q, hq⟩ := hclosed source.1 token hrelated ⟨i, heq.symm⟩
  apply source.2
  apply Finset.mem_map.mpr
  exact ⟨q, Finset.mem_univ _, hq.symm⟩


structure FiniteRelationDeficiencyOneFamily
    (A B : Type*) where
  states : Finset A
  tokens : Finset B
  deficiency_one : tokens.card + 1 = states.card


def FiniteRelationDeficiencyOneFamily.TokenSaturated
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (related : A -> B -> Prop) (family : FiniteRelationDeficiencyOneFamily A B) :
    Prop :=
  ∀ source token, related source token -> token ∈ family.tokens ->
    source ∈ family.states


def FiniteRelationDeficiencyOneFamily.SourceSaturated
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (related : A -> B -> Prop) (family : FiniteRelationDeficiencyOneFamily A B) :
    Prop :=
  ∀ source token, related source token -> source ∈ family.states ->
    token ∈ family.tokens

def FiniteRelationDeficiencyOneFamily.IsSaturated
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (related : A -> B -> Prop) (family : FiniteRelationDeficiencyOneFamily A B) :
    Prop := family.TokenSaturated related ∧ family.SourceSaturated related


theorem FiniteRelationDeficiencyOneFamily.tokenSaturated_or_crossing
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (related : A -> B -> Prop) (family : FiniteRelationDeficiencyOneFamily A B) :
    family.TokenSaturated related ∨
      ∃ source token, related source token ∧ token ∈ family.tokens ∧
        source ∉ family.states := by
  classical
  by_cases hsaturated : family.TokenSaturated related
  · exact Or.inl hsaturated
  · right
    unfold FiniteRelationDeficiencyOneFamily.TokenSaturated at hsaturated
    push Not at hsaturated
    exact hsaturated


theorem FiniteRelationDeficiencyOneFamily.sourceSaturated_or_crossing
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (related : A -> B -> Prop) (family : FiniteRelationDeficiencyOneFamily A B) :
    family.SourceSaturated related ∨
      ∃ source token, related source token ∧ source ∈ family.states ∧
        token ∉ family.tokens := by
  classical
  by_cases hsaturated : family.SourceSaturated related
  · exact Or.inl hsaturated
  · right
    unfold FiniteRelationDeficiencyOneFamily.SourceSaturated at hsaturated
    push Not at hsaturated
    exact hsaturated


def FiniteRelationDeficiencyOneFamily.extendPair
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (family : FiniteRelationDeficiencyOneFamily A B)
    (source : A) (token : B) (hsource : source ∉ family.states)
    (htoken : token ∉ family.tokens) : FiniteRelationDeficiencyOneFamily A B where
  states := insert source family.states
  tokens := insert token family.tokens
  deficiency_one := by
    rw [Finset.card_insert_of_notMem hsource,
      Finset.card_insert_of_notMem htoken]
    have hdeficiency := family.deficiency_one
    omega

@[simp] theorem FiniteRelationDeficiencyOneFamily.mem_states_extendPair
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (family : FiniteRelationDeficiencyOneFamily A B)
    (source : A) (token : B) (hsource : source ∉ family.states)
    (htoken : token ∉ family.tokens) :
    source ∈ (family.extendPair source token hsource htoken).states := by
  change source ∈ insert source family.states
  exact Finset.mem_insert_self source family.states

@[simp] theorem FiniteRelationDeficiencyOneFamily.mem_tokens_extendPair
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (family : FiniteRelationDeficiencyOneFamily A B)
    (source : A) (token : B) (hsource : source ∉ family.states)
    (htoken : token ∉ family.tokens) :
    token ∈ (family.extendPair source token hsource htoken).tokens := by
  change token ∈ insert token family.tokens
  exact Finset.mem_insert_self token family.tokens



structure FiniteRelationCrossingContinuation
    {A : Type u} {B : Type v} (related : A -> B -> Prop) where
  size : Nat
  sources : Fin size ↪ A
  tokens : Fin size ↪ B
  extra : A
  index : Fin size
  extra_fresh : ∀ i, extra ≠ sources i
  aligned : ∀ i, related (sources i) (tokens i)
  crossing : related extra (tokens index)

abbrev FiniteRelationCrossingContinuation.State
    {A : Type u} {B : Type v} {related : A -> B -> Prop}
    (continuation : FiniteRelationCrossingContinuation related) :=
  Fin continuation.size ⊕ Unit

abbrev FiniteRelationCrossingContinuation.Token
    {A : Type u} {B : Type v} {related : A -> B -> Prop}
    (continuation : FiniteRelationCrossingContinuation related) :=
  Fin continuation.size

def FiniteRelationCrossingContinuation.stateAt
    {A : Type u} {B : Type v} {related : A -> B -> Prop}
    (continuation : FiniteRelationCrossingContinuation related) :
    continuation.State -> A
  | Sum.inl index => continuation.sources index
  | Sum.inr _ => continuation.extra

def FiniteRelationCrossingContinuation.incident
    {A : Type u} {B : Type v} {related : A -> B -> Prop}
    (continuation : FiniteRelationCrossingContinuation related) :
    continuation.State -> continuation.Token -> Prop :=
  fun state token =>
    related (continuation.stateAt state) (continuation.tokens token)

def FiniteRelationCrossingContinuation.natural
    {A : Type u} {B : Type v} {related : A -> B -> Prop}
    (continuation : FiniteRelationCrossingContinuation related) :
    continuation.State -> continuation.Token
  | Sum.inl index => index
  | Sum.inr _ => continuation.index

theorem FiniteRelationCrossingContinuation.natural_incident
    {A : Type u} {B : Type v} {related : A -> B -> Prop}
    (continuation : FiniteRelationCrossingContinuation related) :
    ∀ state, continuation.incident state (continuation.natural state) := by
  intro state
  cases state with
  | inl index => exact continuation.aligned index
  | inr _ => exact continuation.crossing



noncomputable def FiniteRelationCrossingContinuation.initialMatching
    {A : Type u} {B : Type v} {related : A -> B -> Prop}
    (continuation : FiniteRelationCrossingContinuation related) :
    StatMech.FrontierA.RelationPartialMatching continuation.incident where
  toFun
    | Sum.inl index =>
        if index = continuation.index then none else some index
    | Sum.inr _ => some continuation.index
  related := by
    intro state token htoken
    cases state with
    | inl index =>
        simp only at htoken
        split at htoken
        next _ => contradiction
        next _ =>
          have : index = token := Option.some.inj htoken
          subst token
          exact continuation.aligned index
    | inr _ =>
        simp only [Option.some.injEq] at htoken
        subst token
        exact continuation.crossing
  injective_some := by
    intro first second token hfirst hsecond
    cases first with
    | inl first =>
        cases second with
        | inl second =>
            simp only at hfirst hsecond
            split at hfirst
            next _ => contradiction
            next _ =>
              split at hsecond
              next _ => contradiction
              next _ => exact congrArg Sum.inl (Option.some.inj
                (hfirst.trans hsecond.symm))
        | inr _ =>
            simp only at hfirst hsecond
            split at hfirst
            next _ => contradiction
            next hne =>
              have heq : first = continuation.index := Option.some.inj
                (hfirst.trans hsecond.symm)
              exact False.elim (hne heq)
    | inr first =>
        cases second with
        | inl second =>
            simp only at hfirst hsecond
            split at hsecond
            next _ => contradiction
            next hne =>
              have heq : second = continuation.index := Option.some.inj
                (hsecond.trans hfirst.symm)
              exact False.elim (hne heq)
        | inr second =>
            exact congrArg Sum.inr (Subsingleton.elim first second)

theorem FiniteRelationCrossingContinuation.initialMatching_support
    {A : Type u} {B : Type v} {related : A -> B -> Prop}
    (continuation : FiniteRelationCrossingContinuation related) :
    continuation.initialMatching.support =
      Finset.univ.erase (Sum.inl continuation.index) := by
  ext state
  cases state with
  | inl index =>
      by_cases hindex : index = continuation.index
      · subst index
        simp [StatMech.FrontierA.RelationPartialMatching.mem_support_iff,
          FiniteRelationCrossingContinuation.initialMatching]
      · simp [StatMech.FrontierA.RelationPartialMatching.mem_support_iff,
          FiniteRelationCrossingContinuation.initialMatching, hindex]
  | inr _ =>
      simp [StatMech.FrontierA.RelationPartialMatching.mem_support_iff,
        FiniteRelationCrossingContinuation.initialMatching]

theorem FiniteRelationCrossingContinuation.initialMatching_maximum
    {A : Type u} {B : Type v} {related : A -> B -> Prop}
    (continuation : FiniteRelationCrossingContinuation related) :
    continuation.initialMatching.IsMaximum := by
  intro other
  have hle := other.card_support_le_target
  have hle' : other.support.card ≤ continuation.size := by
    simpa only [FiniteRelationCrossingContinuation.Token,
      Fintype.card_fin] using hle
  rw [continuation.initialMatching_support]
  simp only [Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_unit]
  omega

noncomputable def FiniteRelationCrossingContinuation.initialHoleState
    {A : Type u} {B : Type v} {related : A -> B -> Prop}
    (continuation : FiniteRelationCrossingContinuation related) :
    StatMech.FrontierA.RelationPartialMatching.HoleState
      continuation.incident where
  matching := continuation.initialMatching
  maximum := continuation.initialMatching_maximum
  hole := Sum.inl continuation.index
  hole_unmatched := by
    rw [continuation.initialMatching_support]
    simp


theorem FiniteRelationCrossingContinuation.move_initialHole_eq_extra
    {A : Type u} {B : Type v} {related : A -> B -> Prop}
    (continuation : FiniteRelationCrossingContinuation related) :
    (continuation.initialHoleState.move
      continuation.natural continuation.natural_incident).hole =
        Sum.inr () := by
  apply continuation.initialMatching.injective_some
  · simpa only [FiniteRelationCrossingContinuation.initialHoleState,
      FiniteRelationCrossingContinuation.natural] using
      continuation.initialHoleState.matching_apply_move_hole
        continuation.natural continuation.natural_incident
  · rfl




theorem FiniteRelationCrossingContinuation.moveThenAlternate_hole
    {A : Type u} {B : Type v} {related : A -> B -> Prop}
    (continuation : FiniteRelationCrossingContinuation related)
    (alternate : continuation.Token)
    (hne : alternate ≠ continuation.index)
    (hincident : continuation.incident (Sum.inr ()) alternate) :
    let moved := continuation.initialHoleState.move
      continuation.natural continuation.natural_incident
    ∃ hincident' : continuation.incident moved.hole alternate,
      (moved.moveAcross alternate hincident').hole = Sum.inl alternate := by
  dsimp only
  let moved := continuation.initialHoleState.move
    continuation.natural continuation.natural_incident
  have hmovedHole : moved.hole = Sum.inr () :=
    continuation.move_initialHole_eq_extra
  have hincident' : continuation.incident moved.hole alternate := by
    rw [hmovedHole]
    exact hincident
  refine ⟨hincident', ?_⟩
  apply moved.matching.injective_some
  · exact moved.matching_apply_moveAcross_hole alternate hincident'
  · rw [continuation.initialHoleState.move_matching_apply_of_ne
      continuation.natural continuation.natural_incident]
    · simp [FiniteRelationCrossingContinuation.initialHoleState,
        FiniteRelationCrossingContinuation.initialMatching, hne]
    · intro heq
      exact hne (Sum.inl.inj heq)
    · rw [hmovedHole]
      simp



theorem FiniteRelationCrossingContinuation.exists_minimal_hole_repeat
    {A : Type u} {B : Type v} {related : A -> B -> Prop}
    (continuation : FiniteRelationCrossingContinuation related) :
    let move := StatMech.FrontierA.RelationPartialMatching.HoleState.move
      continuation.natural continuation.natural_incident
    ∃ start stop : Nat, start < stop ∧ stop ≤ continuation.size + 1 ∧
      (move^[start] continuation.initialHoleState).hole =
        (move^[stop] continuation.initialHoleState).hole ∧
      ∀ a b : Nat, a < b -> b < stop ->
        (move^[a] continuation.initialHoleState).hole ≠
          (move^[b] continuation.initialHoleState).hole := by
  simpa only [FiniteRelationCrossingContinuation.State,
    Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] using
    continuation.initialHoleState.exists_minimal_hole_repeat
      continuation.natural continuation.natural_incident


def FiniteRelationDeficiencyOneFamily.threeTwo
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (a b c : A) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (x y : B) (hxy : x ≠ y) : FiniteRelationDeficiencyOneFamily A B where
  states := {a, b, c}
  tokens := {x, y}
  deficiency_one := by
    simp [hab, hac, hbc, hxy]





theorem finiteRelation_threeTwoOrbitCore_saturated_no_freshToken :
    let related : Fin 3 -> Fin 2 -> Prop := fun _ _ => True
    let family := FiniteRelationDeficiencyOneFamily.threeTwo
      (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
      (0 : Fin 2) 1 (by decide)
    family.IsSaturated related ∧
      related 0 0 ∧ related 1 0 ∧ related 0 1 ∧ related 2 1 ∧
      Nonempty (Fin 2 ↪ Fin 2) ∧ Nonempty (Fin 2 ↪ Fin 2) ∧
      ¬ ∃ token : Fin 2, token ∉ family.tokens := by
  dsimp [FiniteRelationDeficiencyOneFamily.threeTwo,
    FiniteRelationDeficiencyOneFamily.IsSaturated,
    FiniteRelationDeficiencyOneFamily.TokenSaturated,
    FiniteRelationDeficiencyOneFamily.SourceSaturated]
  constructor
  · constructor
    · intro source token _ _
      fin_cases source <;> simp
    · intro source token _ _
      fin_cases token <;> simp
  · refine ⟨by trivial, by trivial, by trivial, by trivial,
      ⟨Function.Embedding.refl _⟩, ⟨Function.Embedding.refl _⟩, ?_⟩
    simp





theorem finiteRelation_threeTwoOrbitCore_balancedBlock_not_tokenClosed :
    ∃ sources : Fin 1 ↪ Fin 3, ∃ tokens : Fin 1 ↪ Fin 2,
      ¬ FiniteRelationTokenClosed (fun _ _ => True) 1 sources tokens := by
  let sources : Fin 1 ↪ Fin 3 :=
    ⟨fun _ => 0, fun _ _ _ => Subsingleton.elim _ _⟩
  let tokens : Fin 1 ↪ Fin 2 :=
    ⟨fun _ => 0, fun _ _ _ => Subsingleton.elim _ _⟩
  refine ⟨sources, tokens, ?_⟩
  intro hclosed
  obtain ⟨i, hi⟩ := hclosed 1 0 trivial ⟨0, rfl⟩
  simp [sources] at hi



theorem finiteEmbeddingComplement_strictDeficit
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (size : Nat) (sources : Fin size ↪ A) (tokens : Fin size ↪ B)
    (hdeficit : Fintype.card B < Fintype.card A) :
    Fintype.card (FiniteEmbeddingComplement size tokens) <
      Fintype.card (FiniteEmbeddingComplement size sources) := by
  rw [finiteEmbeddingComplement_card, finiteEmbeddingComplement_card]
  have hsourceSize : size ≤ Fintype.card A := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective sources sources.injective
  have htokenSize : size ≤ Fintype.card B := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective tokens tokens.injective
  omega



theorem finiteEmbedding_strictBlock_prefix
    {B : Type*} [Fintype B] [DecidableEq B]
    (size : Nat) (tokens : Fin (size + 1) ↪ B) :
    ∃ initial : Fin size ↪ B,
      ∃ extra : FiniteEmbeddingComplement size initial,
        extra.1 = tokens (Fin.last size) := by
  let initial : Fin size ↪ B := Fin.castSuccEmb.trans tokens
  let extra : FiniteEmbeddingComplement size initial :=
    ⟨tokens (Fin.last size), by
      intro hmem
      obtain ⟨i, _hi, heq⟩ := Finset.mem_map.mp hmem
      exact Fin.castSucc_ne_last i (tokens.injective heq)⟩
  exact ⟨initial, extra, rfl⟩



theorem exists_closedBlock_of_strictExtension
    {Block : Type*} (capacity : Nat)
    (blockSize : Block -> Nat) (closed : Block -> Prop)
    (hbound : ∀ block, blockSize block ≤ capacity)
    (hextend : ∀ block, ¬ closed block ->
      ∃ extended, blockSize extended = blockSize block + 1)
    (start : Block) : ∃ block, closed block := by
  have aux : ∀ measure, ∀ current : Block,
      capacity - blockSize current = measure -> ∃ block, closed block := by
    intro measure
    induction measure using Nat.strong_induction_on with
    | h measure ih =>
      intro current hmeasure
      by_cases hclosed : closed current
      · exact ⟨current, hclosed⟩
      · obtain ⟨extended, hextended⟩ := hextend current hclosed
        have hstrict : capacity - blockSize extended < measure := by
          have hextendedBound := hbound extended
          rw [← hmeasure]
          omega
        exact ih (capacity - blockSize extended) hstrict extended rfl
  exact aux (capacity - blockSize start) start rfl





theorem exists_sizeMaximalBlock
    {Block : Type*} (capacity : Nat) (blockSize : Block -> Nat)
    (hbound : ∀ block, blockSize block ≤ capacity) (start : Block) :
    ∃ block, ∀ other, blockSize other ≤ blockSize block := by
  classical
  have aux : ∀ measure, ∀ current : Block,
      capacity - blockSize current = measure ->
        ∃ block, ∀ other, blockSize other ≤ blockSize block := by
    intro measure
    induction measure using Nat.strong_induction_on with
    | h measure ih =>
      intro current hmeasure
      by_cases hmax : ∀ other, blockSize other ≤ blockSize current
      · exact ⟨current, hmax⟩
      · push Not at hmax
        obtain ⟨larger, hlarger⟩ := hmax
        have hstrict : capacity - blockSize larger < measure := by
          have hlargerBound := hbound larger
          rw [← hmeasure]
          omega
        exact ih (capacity - blockSize larger) hstrict larger rfl
  exact aux (capacity - blockSize start) start rfl


theorem exists_fintype_score_maximal
    {A : Type*} [Fintype A] [Nonempty A] (score : A -> Nat) :
    ∃ best, ∀ other, score other ≤ score best := by
  classical
  let scores := Finset.univ.image score
  have hscores : scores.Nonempty := by
    let sample : A := Classical.choice inferInstance
    exact ⟨score sample, Finset.mem_image.mpr
      ⟨sample, Finset.mem_univ sample, rfl⟩⟩
  let maximum := scores.max' hscores
  have hmaximum : maximum ∈ scores := Finset.max'_mem scores hscores
  obtain ⟨best, _hbest, hscore⟩ := Finset.mem_image.mp hmaximum
  refine ⟨best, ?_⟩
  intro other
  rw [hscore]
  exact Finset.le_max' scores (score other)
    (Finset.mem_image.mpr ⟨other, Finset.mem_univ other, rfl⟩)


theorem finiteEmbedding_three_of_pairwise_ne
    {A : Type*} (a b c : A) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Nonempty (Fin 3 ↪ A) := by
  let f : Fin 3 -> A := fun i =>
    Fin.cases a (fun q => Fin.cases b (fun _ => c) q) i
  have hinjective : Function.Injective f := by
    intro x y hxy
    fin_cases x <;> fin_cases y
    · rfl
    · exact False.elim (hab hxy)
    · exact False.elim (hac hxy)
    · exact False.elim (hab hxy.symm)
    · rfl
    · exact False.elim (hbc hxy)
    · exact False.elim (hac hxy.symm)
    · exact False.elim (hbc hxy.symm)
    · rfl
  exact ⟨⟨f, hinjective⟩⟩


theorem finiteEmbedding_two_of_ne
    {A : Type*} (a b : A) (hab : a ≠ b) : Nonempty (Fin 2 ↪ A) := by
  let f : Fin 2 -> A := fun i => Fin.cases a (fun _ => b) i
  have hinjective : Function.Injective f := by
    intro x y hxy
    fin_cases x <;> fin_cases y
    · rfl
    · exact False.elim (hab hxy)
    · exact False.elim (hab hxy.symm)
    · rfl
  exact ⟨⟨f, hinjective⟩⟩




theorem tightProperHall_externalSource_freshToken_or_exhausts
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (related : A -> B -> Prop) [DecidableRel related]
    (hproper : ∀ smaller : Finset A, smaller ⊂ Finset.univ ->
      smaller.card ≤
        (Finset.univ.filter fun token =>
          ∃ source ∈ smaller, related source token).card)
    (size : Nat) (states : Fin size ↪ A)
    (external : A) (hexternal : ∀ i, external ≠ states i) :
    Nonempty (Fin (size + 1) ↪ B) ∨
      ∀ source : A, source = external ∨ ∃ i, source = states i := by
  classical
  let stateBlock : Finset A := Finset.univ.map states
  let extended := insert external stateBlock
  have hexternalNotMem : external ∉ stateBlock := by
    intro hmem
    obtain ⟨i, _hi, heq⟩ := Finset.mem_map.mp hmem
    exact hexternal i heq.symm
  have hextendedCard : extended.card = size + 1 := by
    rw [Finset.card_insert_of_notMem hexternalNotMem]
    simp only [stateBlock, Finset.card_map, Finset.card_univ,
      Fintype.card_fin]
  by_cases hproperBlock : extended ⊂ (Finset.univ : Finset A)
  · left
    have hhall := hproper extended hproperBlock
    have hneighborhoodCard :
        (Finset.univ.filter fun token =>
          ∃ source ∈ extended, related source token).card ≤ Fintype.card B := by
      simpa only [Finset.card_univ] using Finset.card_le_univ
        (Finset.univ.filter fun token =>
          ∃ source ∈ extended, related source token)
    apply Function.Embedding.nonempty_of_card_le
    simpa only [Fintype.card_fin, hextendedCard] using hhall.trans hneighborhoodCard
  · right
    have hextended : extended = (Finset.univ : Finset A) := by
      by_contra hne
      exact hproperBlock (Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.subset_univ _, hne⟩)
    intro source
    have hmem : source ∈ extended := by rw [hextended]; exact Finset.mem_univ _
    rcases Finset.mem_insert.mp hmem with heq | hstate
    · exact Or.inl heq
    · obtain ⟨i, _hi, heq⟩ := Finset.mem_map.mp hstate
      exact Or.inr ⟨i, heq.symm⟩





theorem strictDeficit_sub_balancedBlock
    (self direct token block : Nat)
    (hblockDirect : block ≤ direct) (hblockToken : block ≤ token)
    (hdeficit : token < self + direct) :
    token - block < self + (direct - block) := by
  omega



theorem strictDeficit_sub_balancedEmbeddings
    {Self Direct Token : Type*} [Finite Self] [Finite Direct] [Finite Token]
    (block : Nat)
    (hdeficit : Nat.card Token < Nat.card Self + Nat.card Direct)
    (directBlock : Nonempty (Fin block ↪ Direct))
    (tokenBlock : Nonempty (Fin block ↪ Token)) :
    Nat.card Token - block < Nat.card Self + (Nat.card Direct - block) := by
  obtain ⟨directEmbedding⟩ := directBlock
  obtain ⟨tokenEmbedding⟩ := tokenBlock
  have hblockDirect : block ≤ Nat.card Direct := by
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective
      directEmbedding directEmbedding.injective
  have hblockToken : block ≤ Nat.card Token := by
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective
      tokenEmbedding tokenEmbedding.injective
  exact strictDeficit_sub_balancedBlock
    (Nat.card Self) (Nat.card Direct) (Nat.card Token) block
      hblockDirect hblockToken hdeficit



def partialForestAdvance {A B : Type*} (step : A -> A ⊕ B) (a : A) : A :=
  match step a with
  | Sum.inl next => next
  | Sum.inr _ => a




theorem exists_partialForest_terminal_or_cycle
    {A B : Type*} [Fintype A] (step : A -> A ⊕ B) (start : A) :
    (∃ n ≤ Fintype.card A, ∃ terminal,
      step ((partialForestAdvance step)^[n] start) = Sum.inr terminal) ∨
      ∃ i j : Nat, i < j ∧ j ≤ Fintype.card A ∧
        ((partialForestAdvance step)^[i] start) =
          ((partialForestAdvance step)^[j] start) ∧
        ∀ n < j, ∃ next,
          step ((partialForestAdvance step)^[n] start) = Sum.inl next := by
  classical
  by_cases hterminal : ∃ n ≤ Fintype.card A, ∃ terminal,
      step ((partialForestAdvance step)^[n] start) = Sum.inr terminal
  · exact Or.inl hterminal
  · right
    let orbit : Fin (Fintype.card A + 1) -> A := fun n =>
      (partialForestAdvance step)^[n.1] start
    have hnotInjective : ¬ Function.Injective orbit := by
      intro hinjective
      have hcard := Fintype.card_le_of_injective orbit hinjective
      simp only [Fintype.card_fin] at hcard
      omega
    obtain ⟨u, v, horbit, huv⟩ := Function.not_injective_iff.mp hnotInjective
    obtain ⟨i, j, hij, heq, hj⟩ :
        ∃ i j : Nat, i < j ∧
          ((partialForestAdvance step)^[i] start) =
            ((partialForestAdvance step)^[j] start) ∧
          j ≤ Fintype.card A := by
      rcases lt_or_gt_of_ne huv with huv' | hvu'
      · exact ⟨u.1, v.1, huv', horbit, Nat.le_of_lt_succ v.2⟩
      · exact ⟨v.1, u.1, hvu', horbit.symm, Nat.le_of_lt_succ u.2⟩
    refine ⟨i, j, hij, hj, heq, ?_⟩
    intro n hn
    cases hstep : step ((partialForestAdvance step)^[n] start) with
    | inl next => exact ⟨next, rfl⟩
    | inr terminal =>
        exact False.elim (hterminal ⟨n, hn.le.trans hj, terminal, hstep⟩)



theorem exists_function_iterate_repeat
    {A : Type*} [Fintype A] (next : A -> A) (start : A) :
    ∃ i j : Nat, i < j ∧ j ≤ Fintype.card A ∧
      next^[i] start = next^[j] start := by
  let step : A -> A ⊕ Empty := fun state => Sum.inl (next state)
  have hadvance : partialForestAdvance step = next := by
    funext state
    rfl
  rcases exists_partialForest_terminal_or_cycle step start with
    hterminal | ⟨i, j, hij, hj, hrepeat, _hsteps⟩
  · obtain ⟨_n, _hn, terminal, _hterminal⟩ := hterminal
    exact terminal.elim
  · rw [hadvance] at hrepeat
    exact ⟨i, j, hij, hj, hrepeat⟩




theorem partialForest_iterate_injective_through_first_terminal
    {A B : Type*} (step : A -> A ⊕ B) (start : A) (stop : Nat)
    (hterminal : ∃ terminal,
      step ((partialForestAdvance step)^[stop] start) = Sum.inr terminal)
    (hfirst : ∀ n < stop, ∀ terminal,
      step ((partialForestAdvance step)^[n] start) ≠ Sum.inr terminal) :
    Function.Injective fun i : Fin (stop + 1) =>
      (partialForestAdvance step)^[i.1] start := by
  intro x y hxy
  have noRepeat (a b : Fin (stop + 1)) (hab : a.1 < b.1)
      (heq : (partialForestAdvance step)^[a.1] start =
        (partialForestAdvance step)^[b.1] start) : False := by
    obtain ⟨terminal, hstopTerminal⟩ := hterminal
    let shift := stop - b.1
    have hshift : a.1 + shift < stop := by
      dsimp only [shift]
      omega
    have hfuture :
        (partialForestAdvance step)^[a.1 + shift] start =
          (partialForestAdvance step)^[b.1 + shift] start := by
      let advance := partialForestAdvance step
      calc
        advance^[a.1 + shift] start =
            advance^[shift + a.1] start := by rw [Nat.add_comm a.1 shift]
        _ = advance^[shift] (advance^[a.1] start) :=
          Function.iterate_add_apply advance shift a.1 start
        _ = advance^[shift] (advance^[b.1] start) := congrArg _ heq
        _ = advance^[shift + b.1] start :=
          (Function.iterate_add_apply advance shift b.1 start).symm
        _ = advance^[b.1 + shift] start := by rw [Nat.add_comm b.1 shift]
    have hbStop : b.1 + shift = stop := by
      dsimp only [shift]
      omega
    apply hfirst (a.1 + shift) hshift terminal
    rw [hfuture, hbStop]
    exact hstopTerminal
  apply Fin.ext
  by_contra hval
  rcases lt_or_gt_of_ne hval with hxyVal | hyxVal
  · exact False.elim (noRepeat x y hxyVal hxy)
  · exact False.elim (noRepeat y x hyxVal hxy.symm)




theorem exists_partialForest_terminal_or_rankDrop_or_maxRankCycle
    {A B : Type*} [Fintype A] (step : A -> A ⊕ B) (rank : A -> Nat)
    (start : A) (hmax : ∀ a, rank a ≤ rank start) :
    (∃ n ≤ Fintype.card A, ∃ terminal,
      step ((partialForestAdvance step)^[n] start) = Sum.inr terminal) ∨
      (∃ n < Fintype.card A, ∃ next,
        step ((partialForestAdvance step)^[n] start) = Sum.inl next ∧
          rank next < rank start) ∨
      ∃ i j : Nat, i < j ∧ j ≤ Fintype.card A ∧
        ((partialForestAdvance step)^[i] start) =
          ((partialForestAdvance step)^[j] start) ∧
        ∀ n < j, ∃ next,
          step ((partialForestAdvance step)^[n] start) = Sum.inl next ∧
            rank next = rank start := by
  classical
  rcases exists_partialForest_terminal_or_cycle step start with
    hterminal | ⟨i, j, hij, hj, hrepeat, hsteps⟩
  · exact Or.inl hterminal
  · right
    by_cases hdrop : ∃ n < j, ∃ next,
        step ((partialForestAdvance step)^[n] start) = Sum.inl next ∧
          rank next < rank start
    · left
      obtain ⟨n, hn, next, hstep, hrank⟩ := hdrop
      exact ⟨n, by omega, next, hstep, hrank⟩
    · right
      refine ⟨i, j, hij, hj, hrepeat, ?_⟩
      intro n hn
      obtain ⟨next, hstep⟩ := hsteps n hn
      refine ⟨next, hstep, ?_⟩
      have hnotlt : ¬ rank next < rank start := by
        intro hrank
        exact hdrop ⟨n, hn, next, hstep, hrank⟩
      have hle := hmax next
      omega



theorem map_iterate_eq_of_step_until
    {A B : Type*} (f : A -> A) (g : B -> B) (project : A -> B)
    (start : A) (length : Nat)
    (hstep : ∀ n < length,
      project (f ((f^[n]) start)) = g (project ((f^[n]) start))) :
    project ((f^[length]) start) = (g^[length]) (project start) := by
  induction length with
  | zero => rfl
  | succ length ih =>
      rw [Function.iterate_succ_apply']
      calc
        project (f ((f^[length]) start)) =
            g (project ((f^[length]) start)) := hstep length (by omega)
        _ = g ((g^[length]) (project start)) := congrArg g (ih (by
          intro n hn
          exact hstep n (by omega)))
        _ = (g^[length + 1]) (project start) := by
          rw [Function.iterate_succ_apply']




theorem exists_minimal_iterateKey_repeat_of_closedOrbit
    {A K : Type*} (f : A -> A) (key : A -> K) (start : A)
    (length : Nat) (hlength : 0 < length)
    (hrepeat : (f^[length] start) = start) :
    ∃ first stop : Nat, first < stop ∧ stop ≤ length ∧
      key (f^[first] start) = key (f^[stop] start) ∧
      ∀ a b : Nat, a < b -> b < stop ->
        key (f^[a] start) ≠ key (f^[b] start) := by
  classical
  let orbitKey := fun n : Nat => key (f^[n] start)
  let P := fun n : Nat => ∃ i < n, orbitKey i = orbitKey n
  have hP : ∃ n, P n := by
    refine ⟨length, 0, hlength, ?_⟩
    change key start = key (f^[length] start)
    exact congrArg key hrepeat.symm
  let stop := Nat.find hP
  obtain ⟨first, hfirstStop, hkey⟩ := Nat.find_spec hP
  have hstopBound : stop ≤ length :=
    Nat.find_min' hP (by
      refine ⟨0, hlength, ?_⟩
      change key start = key (f^[length] start)
      exact congrArg key hrepeat.symm)
  refine ⟨first, stop, hfirstStop, hstopBound, hkey, ?_⟩
  intro a b hab hbStop habKey
  have hPb : P b := ⟨a, hab, habKey⟩
  have hstopLe := Nat.find_min' hP hPb
  exact (Nat.not_le_of_lt hbStop) hstopLe



theorem exists_function_cycleEmbedding
    {A : Type*} [Fintype A] (next : A -> A) (start : A) :
    ∃ size : Nat, 0 < size ∧
      ∃ cycle : Fin size ↪ A, ∃ σ : Equiv.Perm (Fin size),
        ∀ i, cycle (σ i) = next (cycle i) := by
  classical
  obtain ⟨a, b, hab, _hb, hrepeat⟩ :=
    exists_function_iterate_repeat next start
  let base := next^[a] start
  let length := b - a
  have hlength : 0 < length := by
    dsimp only [length]
    omega
  have hclosed : next^[length] base = base := by
    calc
      next^[length] base = next^[length + a] start := by
        exact (Function.iterate_add_apply next length a start).symm
      _ = next^[b] start := by congr 2 <;> omega
      _ = next^[a] start := hrepeat.symm
      _ = base := rfl
  obtain ⟨first, stop, hfirstStop, _hstopLength, hstate, hdistinct⟩ :=
    exists_minimal_iterateKey_repeat_of_closedOrbit
      next id base length hlength hclosed
  have hcyclePos : 0 < stop - first := by omega
  obtain ⟨cycleN, hcycle⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hcyclePos)
  let cycleState : Fin (cycleN + 1) -> A := fun x =>
    next^[first + x.1] base
  have hcycleStateInjective : Function.Injective cycleState := by
    intro x y hxy
    apply Fin.ext
    by_contra hval
    rcases lt_or_gt_of_ne hval with hxyVal | hyxVal
    · exact (hdistinct (first + x.1) (first + y.1) (by omega)
          (by omega)) hxy
    · exact (hdistinct (first + y.1) (first + x.1) (by omega)
          (by omega)) hxy.symm
  let cycle : Fin (cycleN + 1) ↪ A :=
    ⟨cycleState, hcycleStateInjective⟩
  let σ : Equiv.Perm (Fin (cycleN + 1)) := finRotate (cycleN + 1)
  have hcycleStep : ∀ x, cycle (σ x) = next (cycle x) := by
    intro x
    by_cases hx : x = Fin.last cycleN
    · subst x
      simp only [cycle, cycleState, σ, finRotate_last,
        Fin.val_zero, Fin.val_last]
      calc
        next^[first] base = next^[stop] base := by
          simpa only [id_eq] using hstate
        _ = next^[Nat.succ (first + cycleN)] base := by
          congr 2 <;> omega
        _ = next (next^[first + cycleN] base) :=
          Function.iterate_succ_apply' next (first + cycleN) base
    · have hrotate : (σ x).1 = x.1 + 1 :=
        coe_finRotate_of_ne_last hx
      change next^[first + (σ x).1] base =
        next (next^[first + x.1] base)
      rw [hrotate]
      convert Function.iterate_succ_apply' next (first + x.1) base using 1 <;>
        omega
  exact ⟨cycleN + 1, by omega, cycle, σ, hcycleStep⟩





theorem canonicalStableRawDirectAlternateExceptionalEdge_target_eq_next
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hdirect : s.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source)
    (hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawDirectAlternateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno s hdirect)) :
    (canonicalStableRawExceptionalEdgeOfLeftToken
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawDirectAlternateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno s hdirect)
          hexceptional).target =
      (canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno s).target := by
  classical
  apply Subtype.ext
  change (canonicalStableRawDirectAlternateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno s hdirect).2.1 =
    (canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno s).target.1
  rw [canonicalStableRawDirectAlternateLeftToken]
  dsimp only
  by_cases hsourceSelf :
      (canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno s).target.1 =
        canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p s.source
  · rw [dif_pos hsourceSelf]
    by_cases hownerSelf : s.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p
          ⟨canonicalStableRawPreferredRightBase ends m j k l zero
              hloop hjk hkl hk0 p s.target,
            canonicalStableRawPreferredRightBase_mem ends m j k l zero
              hloop hjk hkl hk0 p s.target⟩
    · rw [dif_pos hownerSelf]
    · rw [dif_neg hownerSelf]
      exfalso
      apply hexceptional
      unfold canonicalStableRawLeftTokenTarget
      rw [canonicalStableRawDirectAlternateLeftToken]
      dsimp only
      rw [dif_pos hsourceSelf, dif_neg hownerSelf]
  · rw [dif_neg hsourceSelf]




theorem canonicalStableRawDirectAlternateExceptionalEdge_next_or_sibling
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hdirect : s.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source)
    (hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawDirectAlternateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno s hdirect)) :
    let recovered := canonicalStableRawExceptionalEdgeOfLeftToken
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawDirectAlternateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno s hdirect)
        hexceptional
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno s
    recovered = next ∨
      (recovered.source ≠ next.source ∧ recovered.target = next.target) := by
  dsimp only
  have htarget :=
    canonicalStableRawDirectAlternateExceptionalEdge_target_eq_next
      ends m j k l zero hloop hjk hkl hk0 p hno s hdirect hexceptional
  rcases canonicalStableRawExceptionalEdge_source_ne_or_eq_of_target_eq
      (canonicalStableRawExceptionalEdgeOfLeftToken
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawDirectAlternateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno s hdirect)
          hexceptional)
      (canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno s) htarget with
    hsource | heq
  · exact Or.inr ⟨hsource, htarget⟩
  · exact Or.inl heq




theorem canonicalStableRawReferenceOwnerLeftToken_rank_lt
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    canonicalStableRawSourceRank ends m j k l zero p
        (canonicalStableRawReferenceOwnerLeftToken
          ends m j k l zero hloop hjk hkl hk0 p s hself).1 <
      canonicalStableRawSourceRank ends m j k l zero p s.source := by
  change canonicalStableRawSourceRank ends m j k l zero p
      (canonicalStableRawReferenceOwner
        ends m j k l zero hloop hjk hkl hk0 p s) <
    canonicalStableRawSourceRank ends m j k l zero p s.source
  exact canonicalStableRawPreferredRightBase_rank_lt_of_self
    ends m j k l zero hloop hjk hkl hk0 p s.target s.source
      hself.symm s.exceptional




noncomputable def canonicalStableRawComponentAlternateToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (s : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component := by
  classical
  by_cases hself : s.1.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.1.source
  · exact ⟨canonicalStableRawReferenceOwnerLeftToken
        ends m j k l zero hloop hjk hkl hk0 p s.1 hself,
      (canonicalStableRawReferenceOwnerLeftToken_fullComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s.1 hself).trans s.2⟩
  · exact ⟨canonicalStableRawDirectAlternateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s.1 hself,
      (canonicalStableRawDirectAlternateLeftToken_fullComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s.1 hself).trans s.2⟩


theorem canonicalStableRawComponentAlternateToken_incident
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (s : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component s
        (canonicalStableRawComponentAlternateToken
          ends m j k l zero hloop hjk hkl hk0 p hno component s) := by
  classical
  apply (canonicalStableRawWitnessedStateTokenIncidence_iff
    ends m j k l zero hloop hjk hkl hk0 p _ s.1).2
  unfold canonicalStableRawComponentAlternateToken
  split
  next hself =>
    exact canonicalStableRawReferenceOwnerLeftToken_stateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p s.1 hself
  next hdirect =>
    exact canonicalStableRawDirectAlternateLeftToken_stateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p hno s.1 hdirect



theorem canonicalStableRawComponentAlternateToken_ne_natural
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (s : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    canonicalStableRawComponentAlternateToken
        ends m j k l zero hloop hjk hkl hk0 p hno component s ≠
      canonicalStableRawComponentNaturalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component s := by
  classical
  intro heq
  have hraw :
      (canonicalStableRawComponentAlternateToken
        ends m j k l zero hloop hjk hkl hk0 p hno component s).1 =
      (canonicalStableRawComponentNaturalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component s).1 :=
    congrArg (fun token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component => token.1) heq
  unfold canonicalStableRawComponentAlternateToken at hraw
  split at hraw
  next hself =>
    change canonicalStableRawReferenceOwnerLeftToken
        ends m j k l zero hloop hjk hkl hk0 p s.1 hself =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s.1 at hraw
    unfold canonicalStableRawStateLeftToken at hraw
    rw [dif_pos hself] at hraw
    apply s.1.exceptional
    exact (congrArg (fun token => token.1.1) hraw).symm
  next hdirect =>
    change canonicalStableRawDirectAlternateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s.1 hdirect =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s.1 at hraw
    apply canonicalStableRawDirectAlternateLeftToken_ne_natural
      ends m j k l zero hloop hjk hkl hk0 p hno s.1 hdirect
    exact hraw




noncomputable def canonicalStableRawComponentSuccessorToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (s : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component := by
  classical
  by_cases hself : s.1.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.1.source
  · exact ⟨canonicalStableRawSelfOwnerRerouteLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s.1 hself,
      (canonicalStableRawSelfOwnerReroute_fullComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s.1 hself).trans s.2⟩
  · exact ⟨canonicalStableRawDirectAlternateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s.1 hself,
      (canonicalStableRawDirectAlternateLeftToken_fullComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s.1 hself).trans s.2⟩


theorem canonicalStableRawComponentSuccessorToken_incident
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (s : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component s
        (canonicalStableRawComponentSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component s) := by
  classical
  apply (canonicalStableRawWitnessedStateTokenIncidence_iff
    ends m j k l zero hloop hjk hkl hk0 p _ s.1).2
  unfold canonicalStableRawComponentSuccessorToken
  split
  next hself =>
    exact canonicalStableRawSelfOwnerReroute_stateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p hno s.1 hself
  next hdirect =>
    exact canonicalStableRawDirectAlternateLeftToken_stateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p hno s.1 hdirect



theorem canonicalStableRawComponentSuccessorToken_ne_natural
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (s : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component s ≠
      canonicalStableRawComponentNaturalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component s := by
  classical
  intro heq
  have hraw :
      (canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component s).1 =
      (canonicalStableRawComponentNaturalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component s).1 :=
    congrArg (fun token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component => token.1) heq
  unfold canonicalStableRawComponentSuccessorToken at hraw
  split at hraw
  next hself =>
    change canonicalStableRawSelfOwnerRerouteLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s.1 hself =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s.1 at hraw
    unfold canonicalStableRawStateLeftToken at hraw
    rw [dif_pos hself] at hraw
    apply s.1.exceptional
    exact (congrArg (fun token => token.1.1) hraw).symm
  next hdirect =>
    change canonicalStableRawDirectAlternateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s.1 hdirect =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s.1 at hraw
    apply canonicalStableRawDirectAlternateLeftToken_ne_natural
      ends m j k l zero hloop hjk hkl hk0 p hno s.1 hdirect
    exact hraw



theorem canonicalStableRawComponentSuccessorToken_not_exceptional_of_ownerStable
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstable : CanonicalStableRawOwnerStableStep
      ends m j k l zero hloop hjk hkl hk0 p hno self.1) :
    ¬ CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawComponentSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component
            ⟨self.1, self.2.1⟩).1 := by
  classical
  unfold canonicalStableRawComponentSuccessorToken
  rw [dif_pos self.2.2]
  exact canonicalStableRawSelfOwnerReroute_not_exceptional_of_ownerStable
    ends m j k l zero hloop hjk hkl hk0 p hno self.1 self.2.2 hstable




theorem canonicalStableRawComponentSuccessorToken_exceptional_of_advancing
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hadvancing : CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno self.1) :
    CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawComponentSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component
            ⟨self.1, self.2.1⟩).1 := by
  classical
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno self.1
  unfold canonicalStableRawComponentSuccessorToken
  rw [dif_pos self.2.2]
  intro heq
  apply next.exceptional
  calc
    next.source.1 = canonicalStableRawPreferredRightBase
        ends m j k l zero hloop hjk hkl hk0 p self.1.target := hadvancing
    _ = (canonicalStableRawSelfOwnerRerouteLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno self.1 self.2.2).1.1 := rfl
    _ = canonicalStableRawPreferredRightBase
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawLeftTokenTarget
            ends m j k l zero hloop hjk hkl hk0 p
              (canonicalStableRawSelfOwnerRerouteLeftToken
                ends m j k l zero hloop hjk hkl hk0 p hno
                  self.1 self.2.2)) := heq
    _ = canonicalStableRawPreferredRightBase
        ends m j k l zero hloop hjk hkl hk0 p next.target := rfl


abbrev CanonicalStableRawComponentExceptionalToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :=
  {token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component //
    CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p token.1}


abbrev CanonicalStableRawComponentNonexceptionalToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :=
  {token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component //
    ¬ CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p token.1}




noncomputable def canonicalStableRawComponentDirectStateEquivExceptionalToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component ≃
      CanonicalStableRawComponentExceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component := by
  classical
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let f : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component →
      CanonicalStableRawComponentExceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component := fun direct =>
    ⟨directMap direct, by
      change CanonicalStableRawLeftTokenIsExceptional
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno direct.1)
      unfold canonicalStableRawStateLeftToken
      rw [dif_neg direct.2.2]
      exact canonicalStableRawDirectLeftToken_isExceptional
        ends m j k l zero hloop hjk hkl hk0 p direct.1 direct.2.2⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply directMap.injective
    exact congrArg Subtype.val hxy
  · intro token
    let raw := token.1.1
    let edge := canonicalStableRawExceptionalEdgeOfLeftToken
      ends m j k l zero hloop hjk hkl hk0 p raw token.2
    have hdirect : edge.target.1 ≠ canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p edge.source := by
      exact Finset.ne_of_mem_erase raw.2.2
    have hcomponent : canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno edge = component := by
      exact (canonicalStableRawLeftToken_fullComponent_of_stateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p hno raw edge
          (canonicalStableRawExceptionalLeftToken_stateTokenIncidence
            ends m j k l zero hloop hjk hkl hk0 p raw token.2)).symm.trans
        token.1.2
    let direct : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨edge, hcomponent, hdirect⟩
    refine ⟨direct, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno direct.1 = raw
    unfold canonicalStableRawStateLeftToken
    rw [dif_neg direct.2.2]
    unfold direct edge raw canonicalStableRawDirectLeftToken
      canonicalStableRawExceptionalEdgeOfLeftToken
      canonicalStableRawLeftTokenTarget
    rfl

@[simp] theorem canonicalStableRawComponentDirectStateEquivExceptionalToken_apply
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (direct : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    (canonicalStableRawComponentDirectStateEquivExceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component direct).1 =
      canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component direct := by
  rfl



theorem canonicalStableRawComponentNonexceptionalToken_ne_direct
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (terminal : CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (direct : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    terminal.1 ≠ canonicalStableRawComponentDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component direct := by
  intro heq
  apply terminal.2
  rw [heq]
  exact (canonicalStableRawComponentDirectStateEquivExceptionalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component direct).2



noncomputable def canonicalStableRawComponentReferenceExceptionalDirect
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawComponentAlternateToken
          ends m j k l zero hloop hjk hkl hk0 p hno component
            ⟨self.1, self.2.1⟩).1) :
    CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
  (canonicalStableRawComponentDirectStateEquivExceptionalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component).symm
      ⟨canonicalStableRawComponentAlternateToken
        ends m j k l zero hloop hjk hkl hk0 p hno component
          ⟨self.1, self.2.1⟩, hexceptional⟩



theorem canonicalStableRawComponentReferenceExceptionalDirect_rank_lt
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawComponentAlternateToken
          ends m j k l zero hloop hjk hkl hk0 p hno component
            ⟨self.1, self.2.1⟩).1) :
    canonicalStableRawSourceRank ends m j k l zero p
        (canonicalStableRawComponentReferenceExceptionalDirect
          ends m j k l zero hloop hjk hkl hk0 p hno component
            self hexceptional).1.source <
      canonicalStableRawSourceRank ends m j k l zero p self.1.source := by
  classical
  let direct := canonicalStableRawComponentReferenceExceptionalDirect
    ends m j k l zero hloop hjk hkl hk0 p hno component
      self hexceptional
  have hinverse :=
    (canonicalStableRawComponentDirectStateEquivExceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component).apply_symm_apply
        ⟨canonicalStableRawComponentAlternateToken
          ends m j k l zero hloop hjk hkl hk0 p hno component
            ⟨self.1, self.2.1⟩, hexceptional⟩
  have htoken := congrArg Subtype.val (congrArg Subtype.val hinverse)
  change canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1 =
    (canonicalStableRawComponentAlternateToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ⟨self.1, self.2.1⟩).1 at htoken
  unfold canonicalStableRawStateLeftToken
    canonicalStableRawComponentAlternateToken at htoken
  rw [dif_neg direct.2.2, dif_pos self.2.2] at htoken
  have hsource : direct.1.source =
      (canonicalStableRawReferenceOwnerLeftToken
        ends m j k l zero hloop hjk hkl hk0 p self.1 self.2.2).1 :=
    congrArg Sigma.fst htoken
  rw [hsource]
  exact canonicalStableRawReferenceOwnerLeftToken_rank_lt
    ends m j k l zero hloop hjk hkl hk0 p self.1 self.2.2



noncomputable def canonicalStableRawComponentExceptionalSuccessorDirect
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (s : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawComponentSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component s).1) :
    CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
  (canonicalStableRawComponentDirectStateEquivExceptionalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component).symm
      ⟨canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component s,
        hexceptional⟩



theorem canonicalStableRawComponentExceptionalSuccessorDirect_natural
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (s : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawComponentSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component s).1) :
    canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component
          (canonicalStableRawComponentExceptionalSuccessorDirect
            ends m j k l zero hloop hjk hkl hk0 p hno component
              s hexceptional) =
      canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component s := by
  have hinverse :=
    (canonicalStableRawComponentDirectStateEquivExceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component).apply_symm_apply
        ⟨canonicalStableRawComponentSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component s,
          hexceptional⟩
  exact congrArg Subtype.val hinverse




theorem canonicalStableRawComponentExceptionalSuccessorDirect_next_or_sibling_of_direct
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (direct : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawComponentSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component
            ⟨direct.1, direct.2.1⟩).1) :
    let recovered := canonicalStableRawComponentExceptionalSuccessorDirect
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ⟨direct.1, direct.2.1⟩ hexceptional
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1
    recovered.1 = next ∨
      (recovered.1.source ≠ next.source ∧ recovered.1.target = next.target) := by
  classical
  dsimp only
  let recovered := canonicalStableRawComponentExceptionalSuccessorDirect
    ends m j k l zero hloop hjk hkl hk0 p hno component
      ⟨direct.1, direct.2.1⟩ hexceptional
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno direct.1
  have hexceptionalRaw : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawDirectAlternateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno
            direct.1 direct.2.2) := by
    simpa only [canonicalStableRawComponentSuccessorToken,
      dif_neg direct.2.2] using hexceptional
  have hnextTarget :=
    canonicalStableRawDirectAlternateExceptionalEdge_target_eq_next
      ends m j k l zero hloop hjk hkl hk0 p hno
        direct.1 direct.2.2 hexceptionalRaw
  have htoken := congrArg Subtype.val
    (canonicalStableRawComponentExceptionalSuccessorDirect_natural
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ⟨direct.1, direct.2.1⟩ hexceptional)
  change canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno recovered.1 =
    (canonicalStableRawComponentSuccessorToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ⟨direct.1, direct.2.1⟩).1 at htoken
  unfold canonicalStableRawStateLeftToken
    canonicalStableRawComponentSuccessorToken at htoken
  rw [dif_neg recovered.2.2, dif_neg direct.2.2] at htoken
  have htarget : recovered.1.target = next.target := by
    apply Subtype.ext
    have htokenTarget := congrArg (fun token => token.2.1) htoken
    have hnextTargetValue := congrArg Subtype.val hnextTarget
    change (canonicalStableRawDirectAlternateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno
        direct.1 direct.2.2).2.1 = next.target.1 at hnextTargetValue
    exact htokenTarget.trans hnextTargetValue
  rcases canonicalStableRawExceptionalEdge_source_ne_or_eq_of_target_eq
      recovered.1 next htarget with hsource | heq
  · exact Or.inr ⟨hsource, htarget⟩
  · exact Or.inl heq



theorem canonicalStableRawComponentExceptionalSuccessorDirect_eq_next_of_advancing
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hadvancing : CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno self.1) :
    let hexceptional :=
      canonicalStableRawComponentSuccessorToken_exceptional_of_advancing
        ends m j k l zero hloop hjk hkl hk0 p hno component self hadvancing
    (canonicalStableRawComponentExceptionalSuccessorDirect
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ⟨self.1, self.2.1⟩ hexceptional).1 =
      canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno self.1 := by
  classical
  dsimp only
  let direct := canonicalStableRawComponentExceptionalSuccessorDirect
    ends m j k l zero hloop hjk hkl hk0 p hno component
      ⟨self.1, self.2.1⟩
      (canonicalStableRawComponentSuccessorToken_exceptional_of_advancing
        ends m j k l zero hloop hjk hkl hk0 p hno component self hadvancing)
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno self.1
  have htoken := congrArg Subtype.val
    (canonicalStableRawComponentExceptionalSuccessorDirect_natural
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ⟨self.1, self.2.1⟩
        (canonicalStableRawComponentSuccessorToken_exceptional_of_advancing
          ends m j k l zero hloop hjk hkl hk0 p hno component self hadvancing))
  change canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1 =
    (canonicalStableRawComponentSuccessorToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ⟨self.1, self.2.1⟩).1 at htoken
  unfold canonicalStableRawStateLeftToken
    canonicalStableRawComponentSuccessorToken at htoken
  rw [dif_neg direct.2.2, dif_pos self.2.2] at htoken
  have hsource : direct.1.source = next.source := by
    apply Subtype.ext
    have howner := congrArg (fun token => token.1.1) htoken
    change direct.1.source.1 = canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p self.1.target at howner
    exact howner.trans hadvancing.symm
  have htarget : direct.1.target = next.target := by
    apply Subtype.ext
    have htargetValue := congrArg (fun token => token.2.1) htoken
    change direct.1.target.1 = next.target.1 at htargetValue
    exact htargetValue
  exact canonicalStableRawExceptionalEdge_eq_of_source_target_eq
    hsource htarget



theorem canonicalStableRawComponentExceptionalSuccessorDirect_rank_lt_of_advancing
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hadvancing : CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno self.1) :
    let hexceptional :=
      canonicalStableRawComponentSuccessorToken_exceptional_of_advancing
        ends m j k l zero hloop hjk hkl hk0 p hno component self hadvancing
    canonicalStableRawSourceRank ends m j k l zero p
        (canonicalStableRawComponentExceptionalSuccessorDirect
          ends m j k l zero hloop hjk hkl hk0 p hno component
            ⟨self.1, self.2.1⟩ hexceptional).1.source <
      canonicalStableRawSourceRank ends m j k l zero p self.1.source := by
  dsimp only
  rw [canonicalStableRawComponentExceptionalSuccessorDirect_eq_next_of_advancing
    ends m j k l zero hloop hjk hkl hk0 p hno component self hadvancing]
  exact canonicalStableRawOwnerAdvancingStep_rank_lt_of_self
    ends m j k l zero hloop hjk hkl hk0 p hno self.1 self.2.2 hadvancing



noncomputable def canonicalStableRawComponentForestStep
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (s : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
      CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component := by
  classical
  by_cases hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawComponentSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component s).1
  · exact Sum.inl
      (canonicalStableRawComponentExceptionalSuccessorDirect
        ends m j k l zero hloop hjk hkl hk0 p hno component s hexceptional)
  · exact Sum.inr
      ⟨canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component s,
        hexceptional⟩




theorem canonicalStableRawComponentForestStep_direct_split
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (direct : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      canonicalStableRawComponentForestStep
          ends m j k l zero hloop hjk hkl hk0 p hno component
            ⟨direct.1, direct.2.1⟩ = Sum.inr terminal) ∨
      ∃ continuation : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨direct.1, direct.2.1⟩ = Sum.inl continuation ∧
          let next := canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno direct.1
          continuation.1 = next ∨
            (continuation.1.source ≠ next.source ∧
              continuation.1.target = next.target) := by
  classical
  by_cases hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawComponentSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component
            ⟨direct.1, direct.2.1⟩).1
  · right
    let continuation := canonicalStableRawComponentExceptionalSuccessorDirect
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ⟨direct.1, direct.2.1⟩ hexceptional
    refine ⟨continuation, ?_, ?_⟩
    · unfold canonicalStableRawComponentForestStep
      rw [dif_pos hexceptional]
    · exact
        canonicalStableRawComponentExceptionalSuccessorDirect_next_or_sibling_of_direct
          ends m j k l zero hloop hjk hkl hk0 p hno component
            direct hexceptional
  · left
    let terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component
          ⟨direct.1, direct.2.1⟩, hexceptional⟩
    refine ⟨terminal, ?_⟩
    unfold canonicalStableRawComponentForestStep
    rw [dif_neg hexceptional]



theorem canonicalStableRawComponentForestStep_direct_next_or_sibling_of_eq
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (direct continuation : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstep : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component
          ⟨direct.1, direct.2.1⟩ = Sum.inl continuation) :
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1
    continuation.1 = next ∨
      (continuation.1.source ≠ next.source ∧
        continuation.1.target = next.target) := by
  dsimp only
  rcases canonicalStableRawComponentForestStep_direct_split
      ends m j k l zero hloop hjk hkl hk0 p hno component direct with
    ⟨terminal, hterminal⟩ | ⟨nextDirect, hnextDirect, hkind⟩
  · rw [hstep] at hterminal
    contradiction
  · have heq : nextDirect = continuation := Sum.inl.inj
      (hnextDirect.symm.trans hstep)
    simpa only [heq] using hkind


noncomputable def canonicalStableRawComponentDirectForestStep
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (direct : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :=
  canonicalStableRawComponentForestStep
    ends m j k l zero hloop hjk hkl hk0 p hno component
      ⟨direct.1, direct.2.1⟩



noncomputable def canonicalStableRawComponentDirectForestAdvance
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :=
  partialForestAdvance (canonicalStableRawComponentDirectForestStep
    ends m j k l zero hloop hjk hkl hk0 p hno component)

theorem canonicalStableRawComponentDirectForestAdvance_eq_of_step
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (direct continuation : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstep : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component
          ⟨direct.1, direct.2.1⟩ = Sum.inl continuation) :
    canonicalStableRawComponentDirectForestAdvance
      ends m j k l zero hloop hjk hkl hk0 p hno component direct =
        continuation := by
  change canonicalStableRawComponentDirectForestStep
      ends m j k l zero hloop hjk hkl hk0 p hno component direct =
    Sum.inl continuation at hstep
  unfold canonicalStableRawComponentDirectForestAdvance partialForestAdvance
  rw [hstep]





theorem exists_canonicalStableRawComponentDirect_terminal_or_cycle
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    let Direct := CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let advance := canonicalStableRawComponentDirectForestAdvance
      ends m j k l zero hloop hjk hkl hk0 p hno component
    (∃ n ≤ Nat.card Direct,
      ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ =
          Sum.inr terminal) ∨
      ∃ startIndex stopIndex : Nat,
        startIndex < stopIndex ∧ stopIndex ≤ Nat.card Direct ∧
        (advance^[startIndex] start) = (advance^[stopIndex] start) ∧
        ∀ n < stopIndex, ∃ continuation : Direct,
          canonicalStableRawComponentForestStep
              ends m j k l zero hloop hjk hkl hk0 p hno component
                ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ =
            Sum.inl continuation ∧
          let next := canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno
              (advance^[n] start).1
          continuation.1 = next ∨
            (continuation.1.source ≠ next.source ∧
              continuation.1.target = next.target) := by
  classical
  dsimp only
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  letI : Fintype Direct := Fintype.ofFinite Direct
  let step := canonicalStableRawComponentDirectForestStep
    ends m j k l zero hloop hjk hkl hk0 p hno component
  have horbit := exists_partialForest_terminal_or_cycle step start
  have hadvanceEq : partialForestAdvance step =
      canonicalStableRawComponentDirectForestAdvance
        ends m j k l zero hloop hjk hkl hk0 p hno component := by
    rfl
  rw [hadvanceEq] at horbit
  unfold step canonicalStableRawComponentDirectForestStep at horbit
  change _ ∨ ∃ startIndex stopIndex : Nat, _ at horbit
  rcases horbit with hterminal |
    ⟨startIndex, stopIndex, hlt, hstop, heq, hsteps⟩
  · exact Or.inl (by
      simpa only [Nat.card_eq_fintype_card] using hterminal)
  · right
    refine ⟨startIndex, stopIndex, hlt, ?_, heq, ?_⟩
    · simpa only [Nat.card_eq_fintype_card] using hstop
    intro n hn
    obtain ⟨continuation, hcontinuation⟩ := hsteps n hn
    refine ⟨continuation, hcontinuation, ?_⟩
    exact canonicalStableRawComponentForestStep_direct_next_or_sibling_of_eq
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ((canonicalStableRawComponentDirectForestAdvance
          ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start)
        continuation hcontinuation





theorem
    exists_canonicalStableRawComponentDirect_terminal_or_rankDrop_or_cycle
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    let Direct := CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let advance := canonicalStableRawComponentDirectForestAdvance
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let rank := fun direct : Direct =>
      canonicalStableRawSourceRank ends m j k l zero p direct.1.source
    (∃ n ≤ Nat.card Direct,
      ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ =
          Sum.inr terminal) ∨
      (∃ n < Nat.card Direct, ∃ continuation : Direct,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ =
            Sum.inl continuation ∧
          rank continuation < rank (advance^[n] start)) ∨
      ∃ startIndex stopIndex : Nat,
        startIndex < stopIndex ∧ stopIndex ≤ Nat.card Direct ∧
        (advance^[startIndex] start) = (advance^[stopIndex] start) ∧
        ∀ n < stopIndex, ∃ continuation : Direct,
          canonicalStableRawComponentForestStep
              ends m j k l zero hloop hjk hkl hk0 p hno component
                ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ =
              Sum.inl continuation ∧
            rank (advance^[n] start) ≤ rank continuation ∧
            let next := canonicalStableRawExceptionalEdgeNext
              ends m j k l zero hloop hjk hkl hk0 p hno
                (advance^[n] start).1
            continuation.1 = next ∨
              (continuation.1.source ≠ next.source ∧
                continuation.1.target = next.target) := by
  classical
  dsimp only
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let advance := canonicalStableRawComponentDirectForestAdvance
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let rank := fun direct : Direct =>
    canonicalStableRawSourceRank ends m j k l zero p direct.1.source
  rcases exists_canonicalStableRawComponentDirect_terminal_or_cycle
      ends m j k l zero hloop hjk hkl hk0 p hno component start with
    hterminal |
      ⟨startIndex, stopIndex, hlt, hstop, hrepeat, hsteps⟩
  · exact Or.inl hterminal
  · right
    by_cases hdrop : ∃ n < stopIndex, ∃ continuation : Direct,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ =
            Sum.inl continuation ∧
          rank continuation < rank (advance^[n] start)
    · left
      obtain ⟨n, hn, continuation, hstep, hrank⟩ := hdrop
      exact ⟨n, by omega, continuation, hstep, hrank⟩
    · right
      refine ⟨startIndex, stopIndex, hlt, hstop, hrepeat, ?_⟩
      intro n hn
      obtain ⟨continuation, hstep, hkind⟩ := hsteps n hn
      refine ⟨continuation, hstep, ?_, hkind⟩
      have hnotlt : ¬ rank continuation < rank (advance^[n] start) := by
        intro hrank
        exact hdrop ⟨n, hn, continuation, hstep, hrank⟩
      exact Nat.le_of_not_gt hnotlt



theorem canonicalStableRawComponentDirectSibling_componentPair
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (continuation : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (next : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hsource : continuation.1.source ≠ next.source)
    (htarget : continuation.1.target = next.target) :
    Nonempty (Fin 2 ↪ CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  simpa only [continuation.2.1] using
    (canonicalSameTargetDistinctExceptionalPair_componentEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno
        continuation.1 next htarget hsource)



theorem canonicalStableRawComponentDistinctDirect_twoTokenEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (first second : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hne : first ≠ second) :
    Nonempty (Fin 2 ↪ CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let f : Fin 2 → CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component := fun i =>
    if i = 0 then directMap first else directMap second
  refine ⟨⟨f, ?_⟩⟩
  intro x y hxy
  fin_cases x <;> fin_cases y <;> simp_all [f]



theorem canonicalStableRawComponentDistinctDirect_twoDirectEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (first second : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hne : first ≠ second) :
    Nonempty (Fin 2 ↪ CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  let f : Fin 2 → CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component := fun i =>
    if i = 0 then first else second
  refine ⟨⟨f, ?_⟩⟩
  intro x y hxy
  fin_cases x <;> fin_cases y <;> simp_all [f]



theorem canonicalStableRawComponentDirectSibling_twoTokenEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (direct continuation : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsibling : continuation.1.source ≠
        (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno direct.1).source ∧
      continuation.1.target =
        (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno direct.1).target) :
    Nonempty (Fin 2 ↪ CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  have hne : direct ≠ continuation := by
    intro heq
    apply canonicalStableRawExceptionalEdgeNext_target_ne
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1
    calc
      (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno direct.1).target.1 =
          continuation.1.target.1 := congrArg Subtype.val hsibling.2.symm
      _ = direct.1.target.1 := congrArg
        (fun state => state.1.target.1) heq.symm
  exact canonicalStableRawComponentDistinctDirect_twoTokenEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
      direct continuation hne



theorem canonicalStableRawComponentDirectSibling_twoDirectEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (direct continuation : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsibling : continuation.1.source ≠
        (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno direct.1).source ∧
      continuation.1.target =
        (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno direct.1).target) :
    Nonempty (Fin 2 ↪ CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  have hne : direct ≠ continuation := by
    intro heq
    apply canonicalStableRawExceptionalEdgeNext_target_ne
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1
    calc
      (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno direct.1).target.1 =
          continuation.1.target.1 := congrArg Subtype.val hsibling.2.symm
      _ = direct.1.target.1 := congrArg
        (fun state => state.1.target.1) heq.symm
  exact canonicalStableRawComponentDistinctDirect_twoDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
      direct continuation hne





theorem canonicalStableRawComponentDirectNext_twoTokenEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (direct continuation : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hnext : continuation.1 = canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1) :
    Nonempty (Fin 2 ↪ CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  have hne : direct ≠ continuation := by
    intro heq
    apply canonicalStableRawExceptionalEdgeNext_target_ne
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1
    calc
      (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno direct.1).target.1 =
          continuation.1.target.1 := congrArg
            (fun edge => edge.target.1) hnext.symm
      _ = direct.1.target.1 := congrArg
        (fun state => state.1.target.1) heq.symm
  exact canonicalStableRawComponentDistinctDirect_twoTokenEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
      direct continuation hne



theorem canonicalStableRawComponentDirectNext_twoDirectEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (direct continuation : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hnext : continuation.1 = canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1) :
    Nonempty (Fin 2 ↪ CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  have hne : direct ≠ continuation := by
    intro heq
    apply canonicalStableRawExceptionalEdgeNext_target_ne
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1
    calc
      (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno direct.1).target.1 =
          continuation.1.target.1 := congrArg
            (fun edge => edge.target.1) hnext.symm
      _ = direct.1.target.1 := congrArg
        (fun state => state.1.target.1) heq.symm
  exact canonicalStableRawComponentDistinctDirect_twoDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
      direct continuation hne



theorem canonicalStableRawComponentDirectCycle_sibling_or_allNext
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (startIndex stopIndex : Nat)
    (hsteps : ∀ n, startIndex ≤ n -> n < stopIndex ->
      ∃ continuation : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).1,
                ((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).2.1⟩ = Sum.inl continuation ∧
          let next := canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno
              ((canonicalStableRawComponentDirectForestAdvance
                ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                start).1
          continuation.1 = next ∨
            (continuation.1.source ≠ next.source ∧
              continuation.1.target = next.target)) :
    (∃ n, startIndex ≤ n ∧ n < stopIndex ∧
      ∃ continuation : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).1,
                ((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).2.1⟩ = Sum.inl continuation ∧
          let next := canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno
              ((canonicalStableRawComponentDirectForestAdvance
                ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                start).1
          continuation.1.source ≠ next.source ∧
            continuation.1.target = next.target) ∨
      ∀ n, startIndex ≤ n -> n < stopIndex ->
        ∃ continuation : CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          canonicalStableRawComponentForestStep
              ends m j k l zero hloop hjk hkl hk0 p hno component
                ⟨((canonicalStableRawComponentDirectForestAdvance
                      ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                    start).1,
                  ((canonicalStableRawComponentDirectForestAdvance
                      ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                    start).2.1⟩ = Sum.inl continuation ∧
            continuation.1 = canonicalStableRawExceptionalEdgeNext
              ends m j k l zero hloop hjk hkl hk0 p hno
                ((canonicalStableRawComponentDirectForestAdvance
                  ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).1 := by
  classical
  by_cases hsibling : ∃ n, startIndex ≤ n ∧ n < stopIndex ∧
      ∃ continuation : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).1,
                ((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).2.1⟩ = Sum.inl continuation ∧
          let next := canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno
              ((canonicalStableRawComponentDirectForestAdvance
                ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                start).1
          continuation.1.source ≠ next.source ∧
            continuation.1.target = next.target
  · exact Or.inl hsibling
  · right
    intro n hnStart hnStop
    obtain ⟨continuation, hstep, hkind⟩ := hsteps n hnStart hnStop
    refine ⟨continuation, hstep, ?_⟩
    rcases hkind with hnext | hsib
    · exact hnext
    · exact False.elim (hsibling ⟨n, hnStart, hnStop,
        continuation, hstep, hsib⟩)




theorem
    canonicalStableRawComponentDirectAllNext_stableTokens_or_allAdvancing
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (startIndex stopIndex : Nat)
    (hallNext : ∀ n, startIndex ≤ n -> n < stopIndex ->
      ∃ continuation : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).1,
                ((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).2.1⟩ = Sum.inl continuation ∧
        continuation.1 = canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno
            ((canonicalStableRawComponentDirectForestAdvance
              ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
              start).1) :
    (∃ n, startIndex ≤ n ∧ n < stopIndex ∧
      ∃ continuation : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        CanonicalStableRawOwnerStableStep
            ends m j k l zero hloop hjk hkl hk0 p hno
              ((canonicalStableRawComponentDirectForestAdvance
                ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                start).1 ∧
          canonicalStableRawComponentForestStep
              ends m j k l zero hloop hjk hkl hk0 p hno component
                ⟨((canonicalStableRawComponentDirectForestAdvance
                      ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                    start).1,
                  ((canonicalStableRawComponentDirectForestAdvance
                      ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                    start).2.1⟩ = Sum.inl continuation ∧
          continuation.1 = canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno
              ((canonicalStableRawComponentDirectForestAdvance
                ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                start).1 ∧
          Nonempty (Fin 2 ↪ CanonicalStableRawComponentToken
            ends m j k l zero hloop hjk hkl hk0 p hno component)) ∨
      ∀ n, startIndex ≤ n -> n < stopIndex ->
        CanonicalStableRawOwnerAdvancingStep
          ends m j k l zero hloop hjk hkl hk0 p hno
            ((canonicalStableRawComponentDirectForestAdvance
              ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
              start).1 := by
  classical
  by_cases hstable : ∃ n, startIndex ≤ n ∧ n < stopIndex ∧
      CanonicalStableRawOwnerStableStep
        ends m j k l zero hloop hjk hkl hk0 p hno
          ((canonicalStableRawComponentDirectForestAdvance
            ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
            start).1
  · left
    obtain ⟨n, hnStart, hnStop, hownerStable⟩ := hstable
    obtain ⟨continuation, hstep, hnext⟩ := hallNext n hnStart hnStop
    refine ⟨n, hnStart, hnStop, continuation, hownerStable,
      hstep, hnext, ?_⟩
    exact canonicalStableRawComponentDirectNext_twoTokenEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ((canonicalStableRawComponentDirectForestAdvance
          ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start)
        continuation hnext
  · right
    intro n hnStart hnStop
    rcases canonicalStableRawExceptionalEdgeNext_advancing_or_ownerStable
        ends m j k l zero hloop hjk hkl hk0 p hno
          ((canonicalStableRawComponentDirectForestAdvance
            ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
            start).1 with hadvancing | hownerStable
    · exact hadvancing
    · exact False.elim (hstable ⟨n, hnStart, hnStop, hownerStable⟩)



theorem canonicalStableRawComponentDirectAllNext_project
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (startIndex stopIndex n : Nat)
    (hn : n ≤ stopIndex - startIndex)
    (hallNext : ∀ q, startIndex ≤ q -> q < stopIndex ->
      ∃ continuation : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[q]
                  start).1,
                ((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[q]
                  start).2.1⟩ = Sum.inl continuation ∧
        continuation.1 = canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno
            ((canonicalStableRawComponentDirectForestAdvance
              ends m j k l zero hloop hjk hkl hk0 p hno component)^[q]
              start).1) :
    let advance := canonicalStableRawComponentDirectForestAdvance
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno
    (advance^[startIndex + n] start).1 =
      (next^[n] (advance^[startIndex] start).1) := by
  classical
  dsimp only
  let advance := canonicalStableRawComponentDirectForestAdvance
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  let base := advance^[startIndex] start
  have hlocal (q : Nat) (hq : q < n) :
      (advance ((advance^[q]) base)).1 = next ((advance^[q]) base).1 := by
    have hindex : startIndex + q < stopIndex := by omega
    obtain ⟨continuation, hforest, hcontinuation⟩ :=
      hallNext (startIndex + q) (by omega) hindex
    have hglobal : (advance^[q]) base =
        advance^[startIndex + q] start := by
      unfold base
      rw [Nat.add_comm startIndex q]
      exact (Function.iterate_add_apply advance q startIndex start).symm
    have hforestLocal : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component
          ⟨((advance^[q]) base).1, ((advance^[q]) base).2.1⟩ =
        Sum.inl continuation := by
      rw [hglobal]
      exact hforest
    have hadvance : advance ((advance^[q]) base) = continuation :=
      canonicalStableRawComponentDirectForestAdvance_eq_of_step
        ends m j k l zero hloop hjk hkl hk0 p hno component
          ((advance^[q]) base) continuation hforestLocal
    calc
      (advance ((advance^[q]) base)).1 = continuation.1 :=
        congrArg Subtype.val hadvance
      _ = next ((advance^[q]) base).1 := by
        rw [hglobal]
        exact hcontinuation
  have hproject := map_iterate_eq_of_step_until
    advance next (fun direct => direct.1) base n hlocal
  have hglobal : advance^[n] base = advance^[startIndex + n] start := by
    unfold base
    rw [Nat.add_comm startIndex n]
    exact (Function.iterate_add_apply advance n startIndex start).symm
  rw [hglobal] at hproject
  exact hproject




theorem canonicalStableRawComponentDirectAllNext_intervalEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (startIndex stopIndex first stop : Nat)
    (hfirstStop : first < stop)
    (hstopLength : stop ≤ stopIndex - startIndex)
    (hallNext : ∀ n, startIndex ≤ n -> n < stopIndex ->
      ∃ continuation : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).1,
                ((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).2.1⟩ = Sum.inl continuation ∧
        continuation.1 = canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno
            ((canonicalStableRawComponentDirectForestAdvance
              ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
              start).1)
    (hdistinct : ∀ a b : Nat, a < b -> b < stop ->
      ((canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno)^[a]
        ((canonicalStableRawComponentDirectForestAdvance
          ends m j k l zero hloop hjk hkl hk0 p hno component)^[startIndex]
          start).1).target ≠
      ((canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno)^[b]
        ((canonicalStableRawComponentDirectForestAdvance
          ends m j k l zero hloop hjk hkl hk0 p hno component)^[startIndex]
          start).1).target) :
    Nonempty (Fin (stop - first) ↪
      CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let advance := canonicalStableRawComponentDirectForestAdvance
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  let base := advance^[startIndex] start
  let f : Fin (stop - first) → Direct := fun i =>
    advance^[startIndex + (first + i.1)] start
  have hproject (n : Nat) (hn : n ≤ stopIndex - startIndex) :
      (advance^[startIndex + n] start).1 = next^[n] base.1 := by
    exact canonicalStableRawComponentDirectAllNext_project
      ends m j k l zero hloop hjk hkl hk0 p hno component
        start startIndex stopIndex n hn hallNext
  refine ⟨⟨f, ?_⟩⟩
  intro x y hxy
  apply Fin.ext
  by_contra hval
  rcases lt_or_gt_of_ne hval with hxyVal | hyxVal
  · have hxStop : first + x.1 < stop := by omega
    have hyStop : first + y.1 < stop := by omega
    have hxProject := hproject (first + x.1) (by omega)
    have hyProject := hproject (first + y.1) (by omega)
    apply hdistinct (first + x.1) (first + y.1) (by omega) hyStop
    calc
      (next^[first + x.1] base.1).target = (f x).1.target := by
        exact congrArg (fun edge => edge.target) hxProject.symm
      _ = (f y).1.target := congrArg (fun direct => direct.1.target) hxy
      _ = (next^[first + y.1] base.1).target := by
        exact congrArg (fun edge => edge.target) hyProject
  · have hxStop : first + x.1 < stop := by omega
    have hyStop : first + y.1 < stop := by omega
    have hxProject := hproject (first + x.1) (by omega)
    have hyProject := hproject (first + y.1) (by omega)
    apply hdistinct (first + y.1) (first + x.1) (by omega) hxStop
    calc
      (next^[first + y.1] base.1).target = (f y).1.target := by
        exact congrArg (fun edge => edge.target) hyProject.symm
      _ = (f x).1.target := congrArg (fun direct => direct.1.target) hxy.symm
      _ = (next^[first + x.1] base.1).target := by
        exact congrArg (fun edge => edge.target) hxProject



theorem canonicalStableRawClosedNextCycle_of_directCycle
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (startIndex stopIndex : Nat) (hlt : startIndex < stopIndex)
    (hrepeat :
      ((canonicalStableRawComponentDirectForestAdvance
          ends m j k l zero hloop hjk hkl hk0 p hno component)^[startIndex]
        start) =
      ((canonicalStableRawComponentDirectForestAdvance
          ends m j k l zero hloop hjk hkl hk0 p hno component)^[stopIndex]
        start))
    (hallNext : ∀ n, startIndex ≤ n -> n < stopIndex ->
      ∃ continuation : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).1,
                ((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).2.1⟩ = Sum.inl continuation ∧
        continuation.1 = canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno
            ((canonicalStableRawComponentDirectForestAdvance
                ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
              start).1) :
    let advance := canonicalStableRawComponentDirectForestAdvance
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno
    (next^[stopIndex - startIndex] (advance^[startIndex] start).1) =
      (advance^[startIndex] start).1 := by
  classical
  dsimp only
  let advance := canonicalStableRawComponentDirectForestAdvance
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  let base := advance^[startIndex] start
  have hlocal (n : Nat) (hn : n < stopIndex - startIndex) :
      ((advance^[n + 1]) base).1 = next ((advance^[n]) base).1 := by
    have hindex : startIndex + n < stopIndex := by omega
    obtain ⟨continuation, hforest, hcontinuation⟩ :=
      hallNext (startIndex + n) (by omega) hindex
    have hglobal : (advance^[n]) base =
        advance^[startIndex + n] start := by
      unfold base
      rw [Nat.add_comm startIndex n]
      exact (Function.iterate_add_apply advance n startIndex start).symm
    have hforestLocal : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component
          ⟨((advance^[n]) base).1, ((advance^[n]) base).2.1⟩ =
        Sum.inl continuation := by
      rw [hglobal]
      exact hforest
    have hadvance : advance ((advance^[n]) base) = continuation := by
      exact canonicalStableRawComponentDirectForestAdvance_eq_of_step
        ends m j k l zero hloop hjk hkl hk0 p hno component
          ((advance^[n]) base) continuation hforestLocal
    calc
      ((advance^[n + 1]) base).1 =
          (advance ((advance^[n]) base)).1 := by
            rw [Function.iterate_succ_apply']
      _ = continuation.1 := congrArg Subtype.val hadvance
      _ = next ((advance^[n]) base).1 := by
        rw [hglobal]
        exact hcontinuation
  have hproject := map_iterate_eq_of_step_until
    advance next (fun direct => direct.1) base (stopIndex - startIndex)
      (fun n hn => by
        simpa only [Function.iterate_succ_apply'] using hlocal n hn)
  have hend : advance^[stopIndex - startIndex] base =
      advance^[stopIndex] start := by
    calc
      advance^[stopIndex - startIndex] base =
          advance^[stopIndex - startIndex] (advance^[startIndex] start) := rfl
      _ = advance^[(stopIndex - startIndex) + startIndex] start :=
        (Function.iterate_add_apply advance (stopIndex - startIndex)
          startIndex start).symm
      _ = advance^[stopIndex] start := by congr 2 <;> omega
  rw [hend, ← hrepeat] at hproject
  exact hproject.symm






theorem canonicalStableRawComponentClosedAllNextCycle_tokenDichotomy
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (startIndex stopIndex : Nat) (hlt : startIndex < stopIndex)
    (hrepeat :
      ((canonicalStableRawComponentDirectForestAdvance
          ends m j k l zero hloop hjk hkl hk0 p hno component)^[startIndex]
        start) =
      ((canonicalStableRawComponentDirectForestAdvance
          ends m j k l zero hloop hjk hkl hk0 p hno component)^[stopIndex]
        start))
    (hallNext : ∀ n, startIndex ≤ n -> n < stopIndex ->
      ∃ continuation : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).1,
                ((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).2.1⟩ = Sum.inl continuation ∧
        continuation.1 = canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno
            ((canonicalStableRawComponentDirectForestAdvance
              ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
              start).1) :
    Nonempty (Fin 2 ↪ CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      let advance := canonicalStableRawComponentDirectForestAdvance
        ends m j k l zero hloop hjk hkl hk0 p hno component
      let next := canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno
      let base := advance^[startIndex] start
      ∃ first stop : Nat, first < stop ∧
        stop ≤ stopIndex - startIndex ∧
        (next^[first] base.1) = (next^[stop] base.1) ∧
        (∀ a b : Nat, a < b -> b < stop ->
          (next^[a] base.1).target ≠ (next^[b] base.1).target) ∧
        (∀ n : Nat, first ≤ n -> n < stop ->
          CanonicalStableRawOwnerAdvancingStep
            ends m j k l zero hloop hjk hkl hk0 p hno
              (next^[n] base.1)) ∧
        Nonempty (Fin (stop - first) ↪
          CanonicalStableRawComponentToken
            ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  dsimp only
  let advance := canonicalStableRawComponentDirectForestAdvance
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  let base := advance^[startIndex] start
  let length := stopIndex - startIndex
  have hlength : 0 < length := by omega
  have hclosed : next^[length] base.1 = base.1 := by
    exact canonicalStableRawClosedNextCycle_of_directCycle
      ends m j k l zero hloop hjk hkl hk0 p hno component
        start startIndex stopIndex hlt hrepeat hallNext
  obtain ⟨first, stop, hfirstStop, hstopLength, htarget, hdistinct⟩ :=
    exists_minimal_iterateKey_repeat_of_closedOrbit
      next (fun edge => edge.target) base.1 length hlength hclosed
  have hproject (n : Nat) (hn : n ≤ length) :
      (advance^[startIndex + n] start).1 = next^[n] base.1 := by
    exact canonicalStableRawComponentDirectAllNext_project
      ends m j k l zero hloop hjk hkl hk0 p hno component
        start startIndex stopIndex n hn hallNext
  by_cases hstable : ∃ n, first ≤ n ∧ n < stop ∧
      CanonicalStableRawOwnerStableStep
        ends m j k l zero hloop hjk hkl hk0 p hno (next^[n] base.1)
  · left
    obtain ⟨n, hnFirst, hnStop, hownerStable⟩ := hstable
    have hnLength : n < length := hnStop.trans_le hstopLength
    obtain ⟨continuation, hstep, hnext⟩ :=
      hallNext (startIndex + n) (by omega) (by omega)
    exact canonicalStableRawComponentDirectNext_twoTokenEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (advance^[startIndex + n] start) continuation hnext
  · have hadvancing : ∀ n : Nat, first ≤ n -> n < stop ->
        CanonicalStableRawOwnerAdvancingStep
          ends m j k l zero hloop hjk hkl hk0 p hno
            (next^[n] base.1) := by
      intro n hnFirst hnStop
      rcases canonicalStableRawExceptionalEdgeNext_advancing_or_ownerStable
          ends m j k l zero hloop hjk hkl hk0 p hno
            (next^[n] base.1) with hadvancing | hownerStable
      · exact hadvancing
      · exact False.elim
          (hstable ⟨n, hnFirst, hnStop, hownerStable⟩)
    rcases canonicalStableRawExceptionalEdge_source_ne_or_eq_of_target_eq
        (next^[first] base.1) (next^[stop] base.1) htarget with
      hsource | hstate
    · left
      let firstDirect := advance^[startIndex + first] start
      let stopDirect := advance^[startIndex + stop] start
      have hfirstProject : firstDirect.1 = next^[first] base.1 :=
        hproject first (by omega)
      have hstopProject : stopDirect.1 = next^[stop] base.1 :=
        hproject stop hstopLength
      have hne : firstDirect ≠ stopDirect := by
        intro heq
        apply hsource
        calc
          (next^[first] base.1).source = firstDirect.1.source :=
            congrArg (fun edge => edge.source) hfirstProject.symm
          _ = stopDirect.1.source := congrArg
            (fun direct => direct.1.source) heq
          _ = (next^[stop] base.1).source :=
            congrArg (fun edge => edge.source) hstopProject
      exact canonicalStableRawComponentDistinctDirect_twoTokenEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component
          firstDirect stopDirect hne
    · right
      refine ⟨first, stop, hfirstStop, hstopLength, hstate,
        hdistinct, hadvancing, ?_⟩
      let firstDirect := advance^[startIndex + first] start
      have hfirstProject : firstDirect.1 = next^[first] base.1 :=
        hproject first (by omega)
      have hcomponent : canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno
              (next^[first] base.1) = component := by
        rw [← hfirstProject]
        exact firstDirect.2.1
      have hemb := canonicalMinimalClosedAdvancingCycle_componentEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno base.1 first stop
          hfirstStop hstate (fun a b _ hab hb => hdistinct a b hab hb)
          hadvancing
      rw [hcomponent] at hemb
      exact hemb





theorem canonicalStableRawComponentClosedAllNextCycle_balancedBlockDichotomy
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (startIndex stopIndex : Nat) (hlt : startIndex < stopIndex)
    (hrepeat :
      ((canonicalStableRawComponentDirectForestAdvance
          ends m j k l zero hloop hjk hkl hk0 p hno component)^[startIndex]
        start) =
      ((canonicalStableRawComponentDirectForestAdvance
          ends m j k l zero hloop hjk hkl hk0 p hno component)^[stopIndex]
        start))
    (hallNext : ∀ n, startIndex ≤ n -> n < stopIndex ->
      ∃ continuation : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).1,
                ((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).2.1⟩ = Sum.inl continuation ∧
        continuation.1 = canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno
            ((canonicalStableRawComponentDirectForestAdvance
              ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
              start).1) :
    (Nonempty (Fin 2 ↪ CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
        Nonempty (Fin 2 ↪ CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component)) ∨
      let advance := canonicalStableRawComponentDirectForestAdvance
        ends m j k l zero hloop hjk hkl hk0 p hno component
      let next := canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno
      let base := advance^[startIndex] start
      ∃ first stop : Nat, first < stop ∧
        stop ≤ stopIndex - startIndex ∧
        (next^[first] base.1) = (next^[stop] base.1) ∧
        (∀ a b : Nat, a < b -> b < stop ->
          (next^[a] base.1).target ≠ (next^[b] base.1).target) ∧
        (∀ n : Nat, first ≤ n -> n < stop ->
          CanonicalStableRawOwnerAdvancingStep
            ends m j k l zero hloop hjk hkl hk0 p hno
              (next^[n] base.1)) ∧
        Nonempty (Fin (stop - first) ↪
          CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
        Nonempty (Fin (stop - first) ↪
          CanonicalStableRawComponentToken
            ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  let advance := canonicalStableRawComponentDirectForestAdvance
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  let base := advance^[startIndex] start
  obtain ⟨continuation, hstep, hnext⟩ :=
    hallNext startIndex (Nat.le_refl _) hlt
  have hdirectPair : Nonempty (Fin 2 ↪
      CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component) :=
    canonicalStableRawComponentDirectNext_twoDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (advance^[startIndex] start) continuation hnext
  rcases canonicalStableRawComponentClosedAllNextCycle_tokenDichotomy
      ends m j k l zero hloop hjk hkl hk0 p hno component
        start startIndex stopIndex hlt hrepeat hallNext with
    htokenPair | hcycle
  · exact Or.inl ⟨hdirectPair, htokenPair⟩
  · right
    dsimp only at hcycle ⊢
    obtain ⟨first, stop, hfirstStop, hstopLength, hstate,
      hdistinct, hadvancing, htokens⟩ := hcycle
    refine ⟨first, stop, hfirstStop, hstopLength, hstate,
      hdistinct, hadvancing, ?_, htokens⟩
    exact canonicalStableRawComponentDirectAllNext_intervalEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component
        start startIndex stopIndex first stop hfirstStop hstopLength
          hallNext hdistinct





theorem
    exists_canonicalStableRawComponentDirect_terminal_or_rankDrop_or_balancedBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    let Direct := CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let Token := CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let advance := canonicalStableRawComponentDirectForestAdvance
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let rank := fun direct : Direct =>
      canonicalStableRawSourceRank ends m j k l zero p direct.1.source
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno
    (∃ n ≤ Nat.card Direct,
      ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ =
          Sum.inr terminal) ∨
      (∃ n < Nat.card Direct, ∃ continuation : Direct,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ =
            Sum.inl continuation ∧
          rank continuation < rank (advance^[n] start)) ∨
      (Nonempty (Fin 2 ↪ Direct) ∧ Nonempty (Fin 2 ↪ Token)) ∨
      ∃ startIndex stopIndex first stop : Nat,
        startIndex < stopIndex ∧ stopIndex ≤ Nat.card Direct ∧
        (advance^[startIndex] start) = (advance^[stopIndex] start) ∧
        (∀ q, startIndex ≤ q -> q < stopIndex ->
          ∃ continuation : Direct,
            canonicalStableRawComponentForestStep
                ends m j k l zero hloop hjk hkl hk0 p hno component
                  ⟨(advance^[q] start).1, (advance^[q] start).2.1⟩ =
              Sum.inl continuation ∧
            continuation.1 = next (advance^[q] start).1) ∧
        let base := advance^[startIndex] start
        first < stop ∧ stop ≤ stopIndex - startIndex ∧
        (next^[first] base.1) = (next^[stop] base.1) ∧
        (∀ a b : Nat, a < b -> b < stop ->
          (next^[a] base.1).target ≠ (next^[b] base.1).target) ∧
        (∀ q : Nat, first ≤ q -> q < stop ->
          CanonicalStableRawOwnerAdvancingStep
            ends m j k l zero hloop hjk hkl hk0 p hno
              (next^[q] base.1)) ∧
        Nonempty (Fin (stop - first) ↪ Direct) ∧
        Nonempty (Fin (stop - first) ↪ Token) := by
  classical
  dsimp only
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Token := CanonicalStableRawComponentToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let advance := canonicalStableRawComponentDirectForestAdvance
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let rank := fun direct : Direct =>
    canonicalStableRawSourceRank ends m j k l zero p direct.1.source
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  rcases
      exists_canonicalStableRawComponentDirect_terminal_or_rankDrop_or_cycle
        ends m j k l zero hloop hjk hkl hk0 p hno component start with
    hterminal | hdrop | hcycle
  · exact Or.inl hterminal
  · exact Or.inr (Or.inl hdrop)
  · obtain ⟨startIndex, stopIndex, hlt, hbound, hrepeat, hsteps⟩ :=
      hcycle
    have hclassified : ∀ q, startIndex ≤ q -> q < stopIndex ->
        ∃ continuation : Direct,
          canonicalStableRawComponentForestStep
              ends m j k l zero hloop hjk hkl hk0 p hno component
                ⟨(advance^[q] start).1, (advance^[q] start).2.1⟩ =
            Sum.inl continuation ∧
          (continuation.1 = next (advance^[q] start).1 ∨
            (continuation.1.source ≠ (next (advance^[q] start).1).source ∧
              continuation.1.target =
                (next (advance^[q] start).1).target)) := by
      intro q _hqStart hqStop
      obtain ⟨continuation, hstep, _hrank, hkind⟩ := hsteps q hqStop
      exact ⟨continuation, hstep, hkind⟩
    rcases canonicalStableRawComponentDirectCycle_sibling_or_allNext
        ends m j k l zero hloop hjk hkl hk0 p hno component
          start startIndex stopIndex hclassified with
      hsibling | hallNext
    · obtain ⟨q, hqStart, hqStop, continuation, hstep, hkind⟩ :=
        hsibling
      exact Or.inr (Or.inr (Or.inl ⟨
        canonicalStableRawComponentDirectSibling_twoDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (advance^[q] start) continuation hkind,
        canonicalStableRawComponentDirectSibling_twoTokenEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (advance^[q] start) continuation hkind⟩))
    · rcases
        canonicalStableRawComponentClosedAllNextCycle_balancedBlockDichotomy
          ends m j k l zero hloop hjk hkl hk0 p hno component
            start startIndex stopIndex hlt hrepeat hallNext with
        hpair | hadvancing
      · exact Or.inr (Or.inr (Or.inl hpair))
      · right
        right
        right
        dsimp only at hadvancing ⊢
        obtain ⟨first, stop, hfirstStop, hstopLength, hstate,
          hdistinct, howners, hdirects, htokens⟩ := hadvancing
        exact ⟨startIndex, stopIndex, first, stop, hlt, hbound,
          hrepeat, hallNext, hfirstStop, hstopLength, hstate,
          hdistinct, howners, hdirects, htokens⟩




theorem exists_canonicalStableRawComponentDirect_terminal_or_balancedBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    let Direct := CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let Token := CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let advance := canonicalStableRawComponentDirectForestAdvance
      ends m j k l zero hloop hjk hkl hk0 p hno component
    (∃ n ≤ Nat.card Direct,
      ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ =
          Sum.inr terminal) ∨
      ∃ size : Nat, 0 < size ∧
        Nonempty (Fin size ↪ Direct) ∧
        Nonempty (Fin size ↪ Token) := by
  classical
  dsimp only
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Token := CanonicalStableRawComponentToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let advance := canonicalStableRawComponentDirectForestAdvance
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  rcases exists_canonicalStableRawComponentDirect_terminal_or_cycle
      ends m j k l zero hloop hjk hkl hk0 p hno component start with
    hterminal | hcycle
  · exact Or.inl hterminal
  · obtain ⟨startIndex, stopIndex, hlt, _hbound, hrepeat, hsteps⟩ :=
      hcycle
    have hclassified : ∀ q, startIndex ≤ q -> q < stopIndex ->
        ∃ continuation : Direct,
          canonicalStableRawComponentForestStep
              ends m j k l zero hloop hjk hkl hk0 p hno component
                ⟨(advance^[q] start).1, (advance^[q] start).2.1⟩ =
            Sum.inl continuation ∧
          (continuation.1 = next (advance^[q] start).1 ∨
            (continuation.1.source ≠ (next (advance^[q] start).1).source ∧
              continuation.1.target =
                (next (advance^[q] start).1).target)) := by
      intro q _hqStart hqStop
      obtain ⟨continuation, hstep, hkind⟩ := hsteps q hqStop
      exact ⟨continuation, hstep, hkind⟩
    rcases canonicalStableRawComponentDirectCycle_sibling_or_allNext
        ends m j k l zero hloop hjk hkl hk0 p hno component
          start startIndex stopIndex hclassified with
      hsibling | hallNext
    · obtain ⟨q, _hqStart, _hqStop, continuation, _hstep, hkind⟩ :=
        hsibling
      exact Or.inr ⟨2, by omega,
        canonicalStableRawComponentDirectSibling_twoDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (advance^[q] start) continuation hkind,
        canonicalStableRawComponentDirectSibling_twoTokenEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (advance^[q] start) continuation hkind⟩
    · rcases
        canonicalStableRawComponentClosedAllNextCycle_balancedBlockDichotomy
          ends m j k l zero hloop hjk hkl hk0 p hno component
            start startIndex stopIndex hlt hrepeat hallNext with
        hpair | hclosed
      · exact Or.inr ⟨2, by omega, hpair.1, hpair.2⟩
      · dsimp only at hclosed
        obtain ⟨first, stop, hfirstStop, _hstopLength, _hstate,
          _hdistinct, _howners, hdirects, htokens⟩ := hclosed
        exact Or.inr ⟨stop - first, by omega, hdirects, htokens⟩




theorem exists_canonicalStableRawComponentDirect_minRank
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hdirect : Nonempty (CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ start : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      ∀ direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawSourceRank ends m j k l zero p start.1.source ≤
          canonicalStableRawSourceRank ends m j k l zero p direct.1.source := by
  classical
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let rank := fun direct : Direct =>
    canonicalStableRawSourceRank ends m j k l zero p direct.1.source
  letI : Fintype Direct := Fintype.ofFinite Direct
  obtain ⟨direct⟩ := hdirect
  have huniv : (Finset.univ : Finset Direct).Nonempty :=
    ⟨direct, Finset.mem_univ direct⟩
  have hranks : (Finset.univ.image rank).Nonempty := huniv.image rank
  let minimum := (Finset.univ.image rank).min' hranks
  have hminimum : minimum ∈ Finset.univ.image rank :=
    Finset.min'_mem _ _
  obtain ⟨start, _, hstart⟩ := Finset.mem_image.mp hminimum
  refine ⟨start, ?_⟩
  intro other
  change rank start ≤ rank other
  rw [hstart]
  exact Finset.min'_le _ _
    (Finset.mem_image.mpr ⟨other, Finset.mem_univ other, rfl⟩)



noncomputable def canonicalStableRawStableCollisionTargetChildBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (target : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p))) :
    Finset (StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) := by
  classical
  let Cross := StatMech.FrontierA.crossCollision
    (canonicalStableRawComponentSelfEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (canonicalStableRawComponentDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component)
  let Self := CanonicalStableRawComponentSelfState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  letI : Fintype Self := Fintype.ofFinite Self
  letI : Fintype Cross := Fintype.ofInjective
    (fun collision => collision.1.1)
    (StatMech.FrontierA.crossCollision_fst_injective
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
  exact Finset.univ.filter fun collision =>
    CanonicalStableRawOwnerStableStep
        ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1 ∧
      (canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno
          collision.1.1.1).target = target




noncomputable def canonicalStableRawAdvancingCollisionSuccessorChildBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (successor : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    Finset (StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) := by
  classical
  let Cross := StatMech.FrontierA.crossCollision
    (canonicalStableRawComponentSelfEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (canonicalStableRawComponentDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component)
  let Self := CanonicalStableRawComponentSelfState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  letI : Fintype Self := Fintype.ofFinite Self
  letI : Fintype Cross := Fintype.ofInjective
    (fun collision => collision.1.1)
    (StatMech.FrontierA.crossCollision_fst_injective
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
  exact Finset.univ.filter fun collision =>
    CanonicalStableRawOwnerAdvancingStep
        ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1 ∧
      canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno
          collision.1.1.1 = successor



theorem canonicalStableRawStableCollisionTargetChildBlock_capacity
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (target : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)))
    (hne : (canonicalStableRawStableCollisionTargetChildBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component target).Nonempty) :
    ∃ sources : Finset ↑(canonicalRawCommonClosure ends m j k l zero p),
      sources.card = (canonicalStableRawStableCollisionTargetChildBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component target).card ∧
      (canonicalStableRawStableCollisionTargetChildBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component target).card ≤
        (StatMech.FrontierA.finiteRelationNeighborhood
          (CanonicalRawGateRelated ends m j k l zero p)
          (sources.map ⟨Subtype.val, Subtype.val_injective⟩)).card := by
  classical
  let A := canonicalStableRawStableCollisionTargetChildBlock
    ends m j k l zero hloop hjk hkl hk0 p hno component target
  obtain ⟨x₀, hx₀⟩ := hne
  have hstable : ∀ x ∈ A, CanonicalStableRawOwnerStableStep
      ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1 := by
    intro x hx
    have hxData : CanonicalStableRawOwnerStableStep
          ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1 ∧
        (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1).target =
          target := by
      simpa only [A, canonicalStableRawStableCollisionTargetChildBlock,
        Finset.mem_filter, Finset.mem_univ, true_and] using hx
    exact hxData.1
  have htarget : ∀ x ∈ A,
      (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1).target =
        (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x₀.1.1.1).target := by
    intro x hx
    have hxData : CanonicalStableRawOwnerStableStep
          ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1 ∧
        (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1).target =
          target := by
      simpa only [A, canonicalStableRawStableCollisionTargetChildBlock,
        Finset.mem_filter, Finset.mem_univ, true_and] using hx
    have hx₀Data : CanonicalStableRawOwnerStableStep
          ends m j k l zero hloop hjk hkl hk0 p hno x₀.1.1.1 ∧
        (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x₀.1.1.1).target =
          target := by
      simpa only [A, canonicalStableRawStableCollisionTargetChildBlock,
        Finset.mem_filter, Finset.mem_univ, true_and] using hx₀
    exact hxData.2.trans hx₀Data.2.symm
  obtain ⟨sources, _, hcard, hcapacity⟩ :=
    card_le_canonicalRawRelationNeighborhood_of_stableCollisionTargetBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component A x₀ hx₀
        hstable htarget
  exact ⟨sources, hcard, hcapacity⟩



theorem canonicalStableRawAdvancingCollisionSuccessorChildBlock_capacity
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (successor : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hne : (canonicalStableRawAdvancingCollisionSuccessorChildBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component
        successor).Nonempty) :
    ∃ sources : Finset ↑(canonicalRawCommonClosure ends m j k l zero p),
      sources.card =
        (canonicalStableRawAdvancingCollisionSuccessorChildBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component
            successor).card ∧
      (canonicalStableRawAdvancingCollisionSuccessorChildBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component
            successor).card ≤
        (StatMech.FrontierA.finiteRelationNeighborhood
          (CanonicalRawGateRelated ends m j k l zero p)
          (sources.map ⟨Subtype.val, Subtype.val_injective⟩)).card := by
  classical
  let A := canonicalStableRawAdvancingCollisionSuccessorChildBlock
    ends m j k l zero hloop hjk hkl hk0 p hno component successor
  obtain ⟨x₀, hx₀⟩ := hne
  have hadvancing : ∀ x ∈ A, CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1 := by
    intro x hx
    have hxData : CanonicalStableRawOwnerAdvancingStep
          ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1 ∧
        canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1 =
          successor := by
      simpa only [A,
        canonicalStableRawAdvancingCollisionSuccessorChildBlock,
        Finset.mem_filter, Finset.mem_univ, true_and] using hx
    exact hxData.1
  have hnext : ∀ x ∈ A,
      canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1 =
        canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x₀.1.1.1 := by
    intro x hx
    have hxData : CanonicalStableRawOwnerAdvancingStep
          ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1 ∧
        canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1 =
          successor := by
      simpa only [A,
        canonicalStableRawAdvancingCollisionSuccessorChildBlock,
        Finset.mem_filter, Finset.mem_univ, true_and] using hx
    have hx₀Data : CanonicalStableRawOwnerAdvancingStep
          ends m j k l zero hloop hjk hkl hk0 p hno x₀.1.1.1 ∧
        canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x₀.1.1.1 =
          successor := by
      simpa only [A,
        canonicalStableRawAdvancingCollisionSuccessorChildBlock,
        Finset.mem_filter, Finset.mem_univ, true_and] using hx₀
    exact hxData.2.trans hx₀Data.2.symm
  obtain ⟨sources, _, hcard, hcapacity⟩ :=
    card_le_canonicalRawRelationNeighborhood_of_advancingCollisionBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component A x₀ hx₀
        hadvancing hnext
  exact ⟨sources, hcard, hcapacity⟩


noncomputable def canonicalStableRawComponentSelfRank
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component) : Nat :=
  canonicalStableRawSourceRank ends m j k l zero p self.1.source


noncomputable def canonicalStableRawComponentImmediateTerminals
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Finset (CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  exact Finset.univ.filter fun terminal =>
    canonicalStableRawComponentForestStep
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ⟨self.1, self.2.1⟩ = Sum.inr terminal





noncomputable def canonicalStableRawComponentCollisionChildren
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Finset (CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  let Self := CanonicalStableRawComponentSelfState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  letI : Fintype Self := Fintype.ofFinite Self
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno self.1
  let stableBlock := canonicalStableRawStableCollisionTargetChildBlock
    ends m j k l zero hloop hjk hkl hk0 p hno component next.target
  let advancingBlock :=
    canonicalStableRawAdvancingCollisionSuccessorChildBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component next
  exact Finset.univ.filter fun child =>
    canonicalStableRawComponentSelfRank
        ends m j k l zero hloop hjk hkl hk0 p hno component child <
      canonicalStableRawComponentSelfRank
        ends m j k l zero hloop hjk hkl hk0 p hno component self ∧
    ((∃ collision ∈ stableBlock, collision.1.1 = child) ∨
      ∃ collision ∈ advancingBlock, collision.1.1 = child)

theorem canonicalStableRawComponentCollisionChildren_rank_lt
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self child : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hchild : child ∈ canonicalStableRawComponentCollisionChildren
      ends m j k l zero hloop hjk hkl hk0 p hno component self) :
    canonicalStableRawComponentSelfRank
        ends m j k l zero hloop hjk hkl hk0 p hno component child <
      canonicalStableRawComponentSelfRank
        ends m j k l zero hloop hjk hkl hk0 p hno component self := by
  classical
  unfold canonicalStableRawComponentCollisionChildren at hchild
  exact (Finset.mem_filter.mp hchild).2.1


noncomputable def canonicalStableRawComponentTerminalSystem
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    FiniteRankTerminalSystem
      (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) where
  rank := canonicalStableRawComponentSelfRank
    ends m j k l zero hloop hjk hkl hk0 p hno component
  terminals := canonicalStableRawComponentImmediateTerminals
    ends m j k l zero hloop hjk hkl hk0 p hno component
  children := canonicalStableRawComponentCollisionChildren
    ends m j k l zero hloop hjk hkl hk0 p hno component
  children_rank_lt := canonicalStableRawComponentCollisionChildren_rank_lt
    ends m j k l zero hloop hjk hkl hk0 p hno component



noncomputable def CanonicalStableRawComponentReachesTerminal
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (terminal : CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) : Prop := by
  classical
  exact (canonicalStableRawComponentTerminalSystem
    ends m j k l zero hloop hjk hkl hk0 p hno component).ReachesTerminal
      self terminal


noncomputable def canonicalStableRawComponentTerminalNeighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    Finset (CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  exact sources.biUnion
    (canonicalStableRawComponentTerminalSystem
      ends m j k l zero hloop hjk hkl hk0 p hno component
        |>.terminalClosure)



theorem exists_canonicalStableRawComponentReachesTerminal_of_ownerStable
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstable : CanonicalStableRawOwnerStableStep
      ends m j k l zero hloop hjk hkl hk0 p hno self.1) :
    ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      CanonicalStableRawComponentReachesTerminal
        ends m j k l zero hloop hjk hkl hk0 p hno component
          self terminal := by
  classical
  have hnotExceptional :=
    canonicalStableRawComponentSuccessorToken_not_exceptional_of_ownerStable
      ends m j k l zero hloop hjk hkl hk0 p hno component self hstable
  let terminal : CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨canonicalStableRawComponentSuccessorToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ⟨self.1, self.2.1⟩, hnotExceptional⟩
  have hterminal : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component
          ⟨self.1, self.2.1⟩ = Sum.inr terminal := by
    unfold canonicalStableRawComponentForestStep
    rw [dif_neg hnotExceptional]
  refine ⟨terminal, ?_⟩
  unfold CanonicalStableRawComponentReachesTerminal
    FiniteRankTerminalSystem.ReachesTerminal
  apply FiniteRankTerminalSystem.terminals_subset_terminalClosure
    (canonicalStableRawComponentTerminalSystem
      ends m j k l zero hloop hjk hkl hk0 p hno component) self
  unfold canonicalStableRawComponentTerminalSystem
    canonicalStableRawComponentImmediateTerminals
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hterminal⟩



theorem exists_canonicalStableRawComponentForestStep_terminal_of_ownerStable
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstable : CanonicalStableRawOwnerStableStep
      ends m j k l zero hloop hjk hkl hk0 p hno self.1) :
    ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      canonicalStableRawComponentForestStep
          ends m j k l zero hloop hjk hkl hk0 p hno component
            ⟨self.1, self.2.1⟩ = Sum.inr terminal := by
  let hterminal :=
    canonicalStableRawComponentSuccessorToken_not_exceptional_of_ownerStable
      ends m j k l zero hloop hjk hkl hk0 p hno component self hstable
  let terminal : CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨canonicalStableRawComponentSuccessorToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ⟨self.1, self.2.1⟩, hterminal⟩
  refine ⟨terminal, ?_⟩
  unfold canonicalStableRawComponentForestStep
  rw [dif_neg hterminal]



theorem exists_canonicalStableRawComponentForestStep_direct_of_advancing
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hadvancing : CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno self.1) :
    ∃ direct : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      canonicalStableRawComponentForestStep
          ends m j k l zero hloop hjk hkl hk0 p hno component
            ⟨self.1, self.2.1⟩ = Sum.inl direct := by
  let hexceptional :=
    canonicalStableRawComponentSuccessorToken_exceptional_of_advancing
      ends m j k l zero hloop hjk hkl hk0 p hno component self hadvancing
  let direct := canonicalStableRawComponentExceptionalSuccessorDirect
    ends m j k l zero hloop hjk hkl hk0 p hno component
      ⟨self.1, self.2.1⟩ hexceptional
  refine ⟨direct, ?_⟩
  unfold canonicalStableRawComponentForestStep
  rw [dif_pos hexceptional]



theorem canonicalStableRawComponentForestStep_token
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (s : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    (match canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component s with
      | Sum.inl direct => canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component direct
      | Sum.inr terminal => terminal.1) =
      canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component s := by
  classical
  by_cases hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawComponentSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component s).1
  · unfold canonicalStableRawComponentForestStep
    rw [dif_pos hexceptional]
    exact canonicalStableRawComponentExceptionalSuccessorDirect_natural
      ends m j k l zero hloop hjk hkl hk0 p hno component s hexceptional
  · unfold canonicalStableRawComponentForestStep
    rw [dif_neg hexceptional]



theorem canonicalStableRawComponentForestStep_direct_output_or_sibling
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (s : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (direct : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstep : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component s =
      Sum.inl direct) :
    ∃ u : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p,
      u.target = direct.1.target ∧
      (CanonicalStableRawOwnerStableOutput
          ends m j k l zero hloop hjk hkl hk0 p s.1 u ∨
        CanonicalStableRawOwnerAdvancingOutput
          ends m j k l zero hloop hjk hkl hk0 p s.1 u) ∧
      canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
      (u = direct.1 ∨ u.source ≠ direct.1.source) := by
  classical
  let token := canonicalStableRawComponentSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component s
  have hincident : CanonicalStableRawStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token.1 s.1 :=
    (canonicalStableRawWitnessedStateTokenIncidence_iff
      ends m j k l zero hloop hjk hkl hk0 p token.1 s.1).1
        (canonicalStableRawComponentSuccessorToken_incident
          ends m j k l zero hloop hjk hkl hk0 p hno component s)
  obtain ⟨u, huTarget, huKind, huComponent⟩ :=
    canonicalStableRawStateTokenIncidence_outputDichotomy
      ends m j k l zero hloop hjk hkl hk0 p hno token.1 s.1 hincident
  have hforestToken := canonicalStableRawComponentForestStep_token
    ends m j k l zero hloop hjk hkl hk0 p hno component s
  rw [hstep] at hforestToken
  have hrawToken :
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component direct).1 =
        token.1 := congrArg Subtype.val hforestToken
  have hdirectTarget : canonicalStableRawLeftTokenTarget
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component direct).1 =
      direct.1.target := by
    apply Subtype.ext
    change (canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1).2.1 =
        direct.1.target.1
    unfold canonicalStableRawStateLeftToken
    rw [dif_neg direct.2.2]
    rfl
  have huDirectTarget : u.target = direct.1.target := by
    calc
      u.target = canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p token.1 := huTarget
      _ = canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p
            (canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component direct).1 :=
        congrArg (canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p) hrawToken.symm
      _ = direct.1.target := hdirectTarget
  refine ⟨u, huDirectTarget, huKind, huComponent.trans s.2, ?_⟩
  by_cases hsource : u.source = direct.1.source
  · exact Or.inl
      (canonicalStableRawExceptionalEdge_eq_of_source_target_eq
        hsource huDirectTarget)
  · exact Or.inr hsource



noncomputable def canonicalStableRawComponentDirectSumNonexceptionalEquivToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    (CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
      CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) ≃
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component := by
  classical
  let exceptional := fun token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component =>
    CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p token.1
  exact (Equiv.sumCongr
    (canonicalStableRawComponentDirectStateEquivExceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (Equiv.refl _)).trans (Equiv.sumCompl exceptional)


noncomputable def canonicalStableRawComponentReferenceOwnerEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component := by
  classical
  let f := fun self : CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component =>
    canonicalStableRawComponentAlternateToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ⟨self.1, self.2.1⟩
  refine ⟨f, ?_⟩
  intro self other htoken
  apply Subtype.ext
  apply canonicalStableRawReferenceOwnerLeftToken_eq_imp
    ends m j k l zero hloop hjk hkl hk0 p
      self.1 other.1 self.2.2 other.2.2
  have hraw := congrArg Subtype.val htoken
  unfold f canonicalStableRawComponentAlternateToken at hraw
  rw [dif_pos self.2.2, dif_pos other.2.2] at hraw
  exact hraw



theorem canonicalStableRawComponentReferenceOwnerEmbedding_ne_self
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (source target : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    canonicalStableRawComponentReferenceOwnerEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component source ≠
      canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component target := by
  classical
  intro heq
  let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p source.1.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p source.1.target⟩
  have hownerSelf : canonicalStableRawSelfBase ends m j k l zero
      hloop hjk hkl hk0 p owner = source.1.target.1 :=
    canonicalStableRawPreferredRightBase_self_eq_of_exists
      ends m j k l zero hloop hjk hkl hk0 p source.1.target
        ⟨source.1.source, source.2.2.symm⟩
  have htoken : canonicalStableRawReferenceOwnerLeftToken
        ends m j k l zero hloop hjk hkl hk0 p source.1 source.2.2 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno target.1 := by
    have hraw := congrArg Subtype.val heq
    change (canonicalStableRawComponentAlternateToken
        ends m j k l zero hloop hjk hkl hk0 p hno component
          ⟨source.1, source.2.1⟩).1 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno target.1 at hraw
    unfold canonicalStableRawComponentAlternateToken at hraw
    rw [dif_pos source.2.2] at hraw
    exact hraw
  have hsourceRaw := congrArg (fun token :
    CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p => token.1.1) htoken
  unfold canonicalStableRawReferenceOwnerLeftToken
    canonicalStableRawStateLeftToken at hsourceRaw
  rw [dif_pos target.2.2] at hsourceRaw
  change owner.1 = target.1.source.1 at hsourceRaw
  have hownerSource : owner = target.1.source := Subtype.ext hsourceRaw
  have htarget : target.1.target = source.1.target := by
    apply Subtype.ext
    calc
      target.1.target.1 = canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p target.1.source := target.2.2
      _ = canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p owner := by rw [hownerSource]
      _ = source.1.target.1 := hownerSelf
  apply target.1.exceptional
  calc
    target.1.source.1 = owner.1 := congrArg Subtype.val hownerSource.symm
    _ = canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p source.1.target := rfl
    _ = canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p target.1.target := by rw [htarget]




noncomputable def canonicalStableRawComponentSelfPairEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    (CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
      CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component) ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component := by
  let reference := canonicalStableRawComponentReferenceOwnerEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let natural := canonicalStableRawComponentSelfEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let f : (CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
        CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component) →
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component
    | Sum.inl self => reference self
    | Sum.inr self => natural self
  refine ⟨f, ?_⟩
  intro x y hxy
  cases x with
  | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (reference.injective hxy)
      | inr y =>
          exact False.elim
            (canonicalStableRawComponentReferenceOwnerEmbedding_ne_self
              ends m j k l zero hloop hjk hkl hk0 p hno component x y hxy)
  | inr x =>
      cases y with
      | inl y =>
          exact False.elim
            (canonicalStableRawComponentReferenceOwnerEmbedding_ne_self
              ends m j k l zero hloop hjk hkl hk0 p hno component y x
                hxy.symm)
      | inr y => exact congrArg Sum.inr (natural.injective hxy)


theorem canonicalStableRawComponent_two_mul_self_card_le_token
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    2 * Nat.card (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component) ≤
      Nat.card (CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  have hcard := Nat.card_le_card_of_injective
    (canonicalStableRawComponentSelfPairEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (canonicalStableRawComponentSelfPairEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component).injective
  simpa only [Nat.card_sum, two_mul] using hcard



noncomputable def canonicalStableRawComponentReferenceStepEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      (CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
        CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) :=
  (canonicalStableRawComponentReferenceOwnerEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component).trans
      (canonicalStableRawComponentDirectSumNonexceptionalEquivToken
        ends m j k l zero hloop hjk hkl hk0 p hno component).symm.toEmbedding



theorem canonicalStableRawComponentReferenceStepEmbedding_inl_rank_lt
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (direct : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstep : canonicalStableRawComponentReferenceStepEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component self =
      Sum.inl direct) :
    canonicalStableRawSourceRank ends m j k l zero p direct.1.source <
      canonicalStableRawSourceRank ends m j k l zero p self.1.source := by
  classical
  let tokenEquiv :=
    canonicalStableRawComponentDirectSumNonexceptionalEquivToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
  have htokenComponent := congrArg tokenEquiv hstep
  change tokenEquiv (tokenEquiv.symm
      (canonicalStableRawComponentReferenceOwnerEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component self)) =
    tokenEquiv (Sum.inl direct) at htokenComponent
  rw [tokenEquiv.apply_symm_apply] at htokenComponent
  have htoken := congrArg Subtype.val htokenComponent
  change (canonicalStableRawComponentAlternateToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ⟨self.1, self.2.1⟩).1 =
    canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1 at htoken
  unfold canonicalStableRawComponentAlternateToken
    canonicalStableRawStateLeftToken at htoken
  rw [dif_pos self.2.2, dif_neg direct.2.2] at htoken
  have hsource : direct.1.source =
      (canonicalStableRawReferenceOwnerLeftToken
        ends m j k l zero hloop hjk hkl hk0 p self.1 self.2.2).1 :=
    (congrArg Sigma.fst htoken).symm
  rw [hsource]
  exact canonicalStableRawReferenceOwnerLeftToken_rank_lt
    ends m j k l zero hloop hjk hkl hk0 p self.1 self.2.2


abbrev CanonicalStableRawComponentSelfBelowRank
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (rankBound : Nat) :=
  {self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component //
    canonicalStableRawComponentSelfRank
      ends m j k l zero hloop hjk hkl hk0 p hno component self < rankBound}


abbrev CanonicalStableRawComponentDirectBelowRank
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (rankBound : Nat) :=
  {direct : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component //
    canonicalStableRawSourceRank ends m j k l zero p direct.1.source <
      rankBound}




noncomputable def canonicalStableRawComponentReferenceStepBelowRankEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (rankBound : Nat) :
    CanonicalStableRawComponentSelfBelowRank
        ends m j k l zero hloop hjk hkl hk0 p hno component rankBound ↪
      (CanonicalStableRawComponentDirectBelowRank
          ends m j k l zero hloop hjk hkl hk0 p hno component rankBound ⊕
        CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  let step := canonicalStableRawComponentReferenceStepEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let f : CanonicalStableRawComponentSelfBelowRank
        ends m j k l zero hloop hjk hkl hk0 p hno component rankBound →
      (CanonicalStableRawComponentDirectBelowRank
          ends m j k l zero hloop hjk hkl hk0 p hno component rankBound ⊕
        CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) := fun self =>
    match hstep : step self.1 with
    | Sum.inl direct => Sum.inl ⟨direct, by
        have hrank :=
          canonicalStableRawComponentReferenceStepEmbedding_inl_rank_lt
            ends m j k l zero hloop hjk hkl hk0 p hno component
              self.1 direct hstep
        exact hrank.trans self.2⟩
    | Sum.inr terminal => Sum.inr terminal
  have hrecover (self : CanonicalStableRawComponentSelfBelowRank
      ends m j k l zero hloop hjk hkl hk0 p hno component rankBound) :
      Sum.map (fun direct => direct.1) id (f self) = step self.1 := by
    unfold f
    split
    next direct hstep => simpa only [Sum.map] using hstep.symm
    next terminal hstep => simpa only [Sum.map] using hstep.symm
  refine ⟨f, ?_⟩
  intro self other heq
  apply Subtype.ext
  apply step.injective
  calc
    step self.1 = Sum.map (fun direct => direct.1) id (f self) :=
      (hrecover self).symm
    _ = Sum.map (fun direct => direct.1) id (f other) := congrArg _ heq
    _ = step other.1 := hrecover other


theorem canonicalStableRawComponentReferenceStepBelowRank_card_le
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (rankBound : Nat) :
    Nat.card (CanonicalStableRawComponentSelfBelowRank
        ends m j k l zero hloop hjk hkl hk0 p hno component rankBound) ≤
      Nat.card (CanonicalStableRawComponentDirectBelowRank
          ends m j k l zero hloop hjk hkl hk0 p hno component rankBound) +
        Nat.card (CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  have hcard := Nat.card_le_card_of_injective
    (canonicalStableRawComponentReferenceStepBelowRankEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component rankBound)
    (canonicalStableRawComponentReferenceStepBelowRankEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component
        rankBound).injective
  simpa only [Nat.card_sum] using hcard




theorem canonicalStableRawComponentCrossCollision_source_eq_direct
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    collision.1.1.1.source = collision.1.2.1.source := by
  have hclassification :=
    canonicalStableRawComponentCrossCollision_classification
      ends m j k l zero hloop hjk hkl hk0 p hno component collision
  rcases hclassification.2.2 with
    ⟨hdirect, hstable⟩ | ⟨_, hsource, _, _⟩
  · rw [hdirect, hstable.1]
  · exact hsource.symm







theorem canonicalStableRawComponentResidualCollision_ranked_sameTarget
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    collision.1.1.1.2.1.target = collision.1.2.1.target ∧
      canonicalStableRawSourceRank ends m j k l zero p
          collision.1.1.1.2.1.source <
        canonicalStableRawSourceRank ends m j k l zero p
          collision.1.2.1.source := by
  constructor
  · exact (canonicalStableRawComponentReferenceSource_directCollision_target
      ends m j k l zero hloop hjk hkl hk0 p hno component collision).symm
  · let self := collision.1.1.1.1.1.1
    have hlower : collision.1.1.1.2.1.source =
        (canonicalStableRawReferenceOwnerLeftToken
          ends m j k l zero hloop hjk hkl hk0 p self.1 self.2.2).1 := by
      apply Subtype.ext
      exact canonicalStableRawComponentReferenceOwner_directOccupant_source
        ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.1
    have hupper : collision.1.2.1.source = self.1.source :=
      canonicalStableRawComponentReferenceSource_directCollision_source
        ends m j k l zero hloop hjk hkl hk0 p hno component collision
    rw [hlower, hupper]
    exact canonicalStableRawReferenceOwnerLeftToken_rank_lt
      ends m j k l zero hloop hjk hkl hk0 p self.1 self.2.2





theorem canonicalStableRawComponentResidualLower_fresh_or_rightCollision
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    let lower := collision.1.1.1.2
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨lower.1, lower.2.1⟩ = Sum.inr terminal ∧
        ∀ direct : CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          terminal.1 ≠ canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component direct) ∨
      ∃ continuation : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨lower.1, lower.2.1⟩ = Sum.inl continuation ∧
        canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component continuation =
          canonicalStableRawComponentSuccessorToken
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨lower.1, lower.2.1⟩ := by
  classical
  dsimp only
  let lower := collision.1.1.1.2
  cases hstep : canonicalStableRawComponentForestStep
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ⟨lower.1, lower.2.1⟩ with
  | inl continuation =>
      right
      refine ⟨continuation, rfl, ?_⟩
      have htoken := canonicalStableRawComponentForestStep_token
        ends m j k l zero hloop hjk hkl hk0 p hno component
          ⟨lower.1, lower.2.1⟩
      rw [hstep] at htoken
      exact htoken
  | inr terminal =>
      left
      refine ⟨terminal, rfl, ?_⟩
      intro direct
      exact canonicalStableRawComponentNonexceptionalToken_ne_direct
        ends m j k l zero hloop hjk hkl hk0 p hno component terminal direct




abbrev CanonicalStableRawComponentSecondAlternateDirectCollision
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :=
  StatMech.FrontierA.crossCollision
    (canonicalStableRawComponentSecondCollisionAlternateToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (canonicalStableRawComponentDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component)



theorem canonicalStableRawComponentResidualLower_rightCollision
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (continuation : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstep : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component
          ⟨collision.1.1.1.2.1, collision.1.1.1.2.2.1⟩ =
        Sum.inl continuation) :
    ∃ third : CanonicalStableRawComponentSecondAlternateDirectCollision
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      third.1.1 = collision.1.1 ∧ third.1.2 = continuation := by
  let lower := collision.1.1.1.2
  have htoken := canonicalStableRawComponentForestStep_token
    ends m j k l zero hloop hjk hkl hk0 p hno component
      ⟨lower.1, lower.2.1⟩
  rw [hstep] at htoken
  have halternate : canonicalStableRawComponentSecondCollisionAlternateToken
        ends m j k l zero hloop hjk hkl hk0 p hno component
          collision.1.1 =
      canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component
          ⟨lower.1, lower.2.1⟩ := by
    apply Subtype.ext
    change canonicalStableRawDirectAlternateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno
          lower.1 lower.2.2 =
      (canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component
          ⟨lower.1, lower.2.1⟩).1
    unfold canonicalStableRawComponentSuccessorToken
    rw [dif_neg lower.2.2]
  let third : CanonicalStableRawComponentSecondAlternateDirectCollision
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨(collision.1.1, continuation), halternate.trans htoken.symm⟩
  exact ⟨third, rfl, rfl⟩






theorem canonicalStableRawComponentResidualLower_continuation_source_split
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (continuation : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstep : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component
          ⟨collision.1.1.1.2.1, collision.1.1.1.2.2.1⟩ =
        Sum.inl continuation) :
    let lower := collision.1.1.1.2
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno lower.1
    let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
      ⟨canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p lower.1.target,
        canonicalStableRawPreferredRightBase_mem ends m j k l zero
          hloop hjk hkl hk0 p lower.1.target⟩
    (next.target.1 = canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p lower.1.source ∧
        continuation.1.source = owner) ∨
      (next.target.1 ≠ canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p lower.1.source ∧
        continuation.1.source = lower.1.source ∧
        canonicalStableRawSourceRank ends m j k l zero p
            continuation.1.source =
          canonicalStableRawSourceRank ends m j k l zero p lower.1.source) := by
  classical
  dsimp only
  let lower := collision.1.1.1.2
  have htoken := canonicalStableRawComponentForestStep_token
    ends m j k l zero hloop hjk hkl hk0 p hno component
      ⟨lower.1, lower.2.1⟩
  rw [hstep] at htoken
  have hsource : continuation.1.source =
      (canonicalStableRawDirectAlternateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno
          lower.1 lower.2.2).1 := by
    apply Subtype.ext
    have hraw := congrArg
      (fun token : CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component => token.1.1.1)
      htoken
    simpa only [canonicalStableRawComponentDirectEmbedding_apply,
      canonicalStableRawStateLeftToken, dif_neg continuation.2.2,
      canonicalStableRawComponentSuccessorToken, dif_neg lower.2.2] using hraw
  rcases canonicalStableRawDirectAlternateLeftToken_source_split
      ends m j k l zero hloop hjk hkl hk0 p hno lower.1 lower.2.2 with
    howner | hsame
  · exact Or.inl ⟨howner.1, hsource.trans howner.2⟩
  · exact Or.inr ⟨hsame.1, hsource.trans hsame.2,
      congrArg (canonicalStableRawSourceRank ends m j k l zero p)
        (hsource.trans hsame.2)⟩


noncomputable def canonicalStableRawComponentSecondAlternateTarget
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :=
  canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p
    (canonicalStableRawComponentSecondCollisionAlternateToken
      ends m j k l zero hloop hjk hkl hk0 p hno component collision).1




theorem exists_canonicalStableRawComponentSecondAlternateFiber_freeTerminal
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hfree : (canonicalStableRawComponentSecondAlternateTarget
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1 ≠
      canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p
          ⟨canonicalStableRawPreferredRightBase ends m j k l zero
              hloop hjk hkl hk0 p
                (canonicalStableRawComponentSecondAlternateTarget
                  ends m j k l zero hloop hjk hkl hk0 p hno component anchor),
            canonicalStableRawPreferredRightBase_mem ends m j k l zero
              hloop hjk hkl hk0 p
                (canonicalStableRawComponentSecondAlternateTarget
                  ends m j k l zero hloop hjk hkl hk0 p hno component anchor)⟩) :
    ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p terminal.1.1 =
        canonicalStableRawComponentSecondAlternateTarget
          ends m j k l zero hloop hjk hkl hk0 p hno component anchor := by
  classical
  let target := canonicalStableRawComponentSecondAlternateTarget
    ends m j k l zero hloop hjk hkl hk0 p hno component anchor
  obtain ⟨u, huTarget, _huKind, huComponent⟩ :=
    canonicalStableRawComponentSecondCollisionAlternateToken_outputDichotomy
      ends m j k l zero hloop hjk hkl hk0 p hno component anchor
  have hfreeU : u.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p u.target,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p u.target⟩ := by
    rw [huTarget]
    exact hfree
  let raw := canonicalStableRawPreferredFreeLeftToken
    ends m j k l zero hloop hjk hkl hk0 p u.target hfreeU
  have hrawComponent : canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno raw = component :=
    (canonicalStableRawPreferredFreeLeftToken_fullComponent
      ends m j k l zero hloop hjk hkl hk0 p hno u hfreeU).trans huComponent
  let token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨raw, hrawComponent⟩
  let terminal : CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨token, canonicalStableRawPreferredFreeLeftToken_not_exceptional
      ends m j k l zero hloop hjk hkl hk0 p u.target hfreeU⟩
  refine ⟨terminal, ?_⟩
  change canonicalStableRawLeftTokenTarget
      ends m j k l zero hloop hjk hkl hk0 p raw = target
  exact (canonicalStableRawPreferredFreeLeftToken_target
    ends m j k l zero hloop hjk hkl hk0 p u.target hfreeU).trans huTarget





theorem exists_canonicalStableRawComponentPreferredSelfOwnerStable_freeTerminal
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (s : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hpreferredSelf : s.1.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p s.1.target,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p s.1.target⟩)
    (hstable : CanonicalStableRawOwnerStableStep
      ends m j k l zero hloop hjk hkl hk0 p hno s.1) :
    ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p terminal.1.1 =
        (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno s.1).target := by
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno s.1
  have hfree :=
    canonicalStableRawOwnerStableStep_nextTarget_free_of_preferredSelf
      ends m j k l zero hloop hjk hkl hk0 p hno s.1 hpreferredSelf hstable
  let raw := canonicalStableRawPreferredFreeLeftToken
    ends m j k l zero hloop hjk hkl hk0 p next.target hfree
  have hrawComponent : canonicalStableRawFullLeftTokenComponent
      ends m j k l zero hloop hjk hkl hk0 p hno raw = component := by
    calc
      canonicalStableRawFullLeftTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno raw =
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno next :=
        canonicalStableRawPreferredFreeLeftToken_fullComponent
          ends m j k l zero hloop hjk hkl hk0 p hno next hfree
      _ = canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno s.1 :=
        canonicalStableRawTokenComponent_next
          ends m j k l zero hloop hjk hkl hk0 p hno s.1
      _ = component := s.2
  let token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨raw, hrawComponent⟩
  let terminal : CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨token, canonicalStableRawPreferredFreeLeftToken_not_exceptional
      ends m j k l zero hloop hjk hkl hk0 p next.target hfree⟩
  refine ⟨terminal, ?_⟩
  exact canonicalStableRawPreferredFreeLeftToken_target
    ends m j k l zero hloop hjk hkl hk0 p next.target hfree



abbrev CanonicalStableRawComponentPreferredDirectState
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :=
  {direct : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component //
    direct.1.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p direct.1.target,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p direct.1.target⟩}



noncomputable def canonicalStableRawComponentPreferredDirectNext
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (direct : CanonicalStableRawComponentPreferredDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hnextPreferred :
      let next := canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno direct.1.1
      next.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p
          ⟨canonicalStableRawPreferredRightBase ends m j k l zero
              hloop hjk hkl hk0 p next.target,
            canonicalStableRawPreferredRightBase_mem ends m j k l zero
              hloop hjk hkl hk0 p next.target⟩) :
    CanonicalStableRawComponentPreferredDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component := by
  classical
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno direct.1.1
  have hadvance : CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1.1 := by
    rcases canonicalStableRawExceptionalEdgeNext_advancing_or_ownerStable
        ends m j k l zero hloop hjk hkl hk0 p hno direct.1.1 with
      hadvance | hstable
    · exact hadvance
    · exfalso
      exact (canonicalStableRawOwnerStableStep_nextTarget_free_of_preferredSelf
        ends m j k l zero hloop hjk hkl hk0 p hno direct.1.1 direct.2
          hstable) hnextPreferred
  let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p direct.1.1.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p direct.1.1.target⟩
  have hsource : next.source = owner := Subtype.ext hadvance
  have hdirect : next.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p next.source := by
    intro hself
    apply canonicalStableRawExceptionalEdgeNext_target_ne
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1.1
    calc
      next.target.1 = canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p next.source := hself
      _ = canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p owner := by rw [hsource]
      _ = direct.1.1.target.1 := direct.2.symm
  let nextDirect : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨next, (canonicalStableRawTokenComponent_next
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1.1).trans
        direct.1.2.1, hdirect⟩
  exact ⟨nextDirect, hnextPreferred⟩



noncomputable def canonicalStableRawComponentPreferredDirectStep
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    CanonicalStableRawComponentPreferredDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component →
      CanonicalStableRawComponentPreferredDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
        CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component := by
  classical
  intro direct
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno direct.1.1
  by_cases hnextPreferred : next.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p next.target,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p next.target⟩
  · exact Sum.inl
      (canonicalStableRawComponentPreferredDirectNext
        ends m j k l zero hloop hjk hkl hk0 p hno component direct
          hnextPreferred)
  · let raw := canonicalStableRawPreferredFreeLeftToken
        ends m j k l zero hloop hjk hkl hk0 p next.target hnextPreferred
    have hrawComponent : canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno raw = component := by
      calc
        canonicalStableRawFullLeftTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno raw =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno next :=
          canonicalStableRawPreferredFreeLeftToken_fullComponent
            ends m j k l zero hloop hjk hkl hk0 p hno next hnextPreferred
        _ = canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno direct.1.1 :=
          canonicalStableRawTokenComponent_next
            ends m j k l zero hloop hjk hkl hk0 p hno direct.1.1
        _ = component := direct.1.2.1
    exact Sum.inr ⟨⟨raw, hrawComponent⟩,
      canonicalStableRawPreferredFreeLeftToken_not_exceptional
        ends m j k l zero hloop hjk hkl hk0 p next.target hnextPreferred⟩

theorem canonicalStableRawComponentPreferredDirectStep_inl_next
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (direct next : CanonicalStableRawComponentPreferredDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstep : canonicalStableRawComponentPreferredDirectStep
        ends m j k l zero hloop hjk hkl hk0 p hno component direct =
      Sum.inl next) :
    next.1.1 = canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1.1 := by
  classical
  unfold canonicalStableRawComponentPreferredDirectStep at hstep
  dsimp only at hstep
  split at hstep
  next hnextPreferred =>
    exact congrArg (fun state => state.1.1) (Sum.inl.inj hstep).symm
  next _ => contradiction

theorem canonicalStableRawComponentPreferredDirectAdvance_eq_of_step
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (direct next : CanonicalStableRawComponentPreferredDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstep : canonicalStableRawComponentPreferredDirectStep
        ends m j k l zero hloop hjk hkl hk0 p hno component direct =
      Sum.inl next) :
    partialForestAdvance
        (canonicalStableRawComponentPreferredDirectStep
          ends m j k l zero hloop hjk hkl hk0 p hno component) direct =
      next := by
  unfold partialForestAdvance
  rw [hstep]





theorem
    canonicalStableRawComponentSecondAlternateFiber_terminal_or_preferredSelfOutput
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p terminal.1.1 =
        canonicalStableRawComponentSecondAlternateTarget
          ends m j k l zero hloop hjk hkl hk0 p hno component anchor) ∨
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawComponentSecondAlternateTarget
          ends m j k l zero hloop hjk hkl hk0 p hno component anchor ∧
        (CanonicalStableRawOwnerStableOutput
            ends m j k l zero hloop hjk hkl hk0 p anchor.1.2.1 u ∨
          CanonicalStableRawOwnerAdvancingOutput
            ends m j k l zero hloop hjk hkl hk0 p anchor.1.2.1 u) ∧
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
        (canonicalStableRawComponentSecondAlternateTarget
          ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1 =
          canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
            ⟨canonicalStableRawPreferredRightBase ends m j k l zero
                hloop hjk hkl hk0 p
                  (canonicalStableRawComponentSecondAlternateTarget
                    ends m j k l zero hloop hjk hkl hk0 p hno component anchor),
              canonicalStableRawPreferredRightBase_mem ends m j k l zero
                hloop hjk hkl hk0 p
                  (canonicalStableRawComponentSecondAlternateTarget
                    ends m j k l zero hloop hjk hkl hk0 p hno component anchor)⟩ := by
  classical
  let target := canonicalStableRawComponentSecondAlternateTarget
    ends m j k l zero hloop hjk hkl hk0 p hno component anchor
  let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p target⟩
  by_cases hfree : target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p owner
  · exact Or.inl
      (exists_canonicalStableRawComponentSecondAlternateFiber_freeTerminal
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor hfree)
  · obtain ⟨u, huTarget, huKind, huComponent⟩ :=
      canonicalStableRawComponentSecondCollisionAlternateToken_outputDichotomy
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor
    exact Or.inr ⟨u, huTarget, huKind, huComponent,
      Classical.not_not.mp hfree⟩





theorem
    canonicalStableRawComponentSecondAlternatePreferredSelfOutput_stepSplit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hpreferredSelf :
      (canonicalStableRawComponentSecondAlternateTarget
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1 =
        canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
          ⟨canonicalStableRawPreferredRightBase ends m j k l zero
              hloop hjk hkl hk0 p
                (canonicalStableRawComponentSecondAlternateTarget
                  ends m j k l zero hloop hjk hkl hk0 p hno component anchor),
            canonicalStableRawPreferredRightBase_mem ends m j k l zero
              hloop hjk hkl hk0 p
                (canonicalStableRawComponentSecondAlternateTarget
                  ends m j k l zero hloop hjk hkl hk0 p hno component anchor)⟩) :
    (∃ self : CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          self.1.target = canonicalStableRawComponentSecondAlternateTarget
            ends m j k l zero hloop hjk hkl hk0 p hno component anchor ∧
          canonicalStableRawComponentReferenceStepEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component self =
            Sum.inr terminal) ∨
      (∃ self : CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ direct : CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          self.1.target = canonicalStableRawComponentSecondAlternateTarget
            ends m j k l zero hloop hjk hkl hk0 p hno component anchor ∧
          canonicalStableRawComponentReferenceStepEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component self =
            Sum.inl direct ∧
          canonicalStableRawSourceRank ends m j k l zero p direct.1.source <
            canonicalStableRawSourceRank ends m j k l zero p self.1.source) ∨
      ∃ direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        direct.1.target = canonicalStableRawComponentSecondAlternateTarget
          ends m j k l zero hloop hjk hkl hk0 p hno component anchor ∧
        (CanonicalStableRawOwnerStableOutput
            ends m j k l zero hloop hjk hkl hk0 p anchor.1.2.1 direct.1 ∨
          CanonicalStableRawOwnerAdvancingOutput
            ends m j k l zero hloop hjk hkl hk0 p anchor.1.2.1 direct.1) ∧
        (canonicalStableRawComponentSecondAlternateTarget
          ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1 =
          canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
            ⟨canonicalStableRawPreferredRightBase ends m j k l zero
                hloop hjk hkl hk0 p
                  (canonicalStableRawComponentSecondAlternateTarget
                    ends m j k l zero hloop hjk hkl hk0 p hno component anchor),
              canonicalStableRawPreferredRightBase_mem ends m j k l zero
                hloop hjk hkl hk0 p
                  (canonicalStableRawComponentSecondAlternateTarget
                    ends m j k l zero hloop hjk hkl hk0 p hno component anchor)⟩ := by
  classical
  obtain ⟨u, huTarget, huKind, huComponent⟩ :=
    canonicalStableRawComponentSecondCollisionAlternateToken_outputDichotomy
      ends m j k l zero hloop hjk hkl hk0 p hno component anchor
  by_cases hself : u.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p u.source
  · let self : CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨u, huComponent, hself⟩
    cases hstep : canonicalStableRawComponentReferenceStepEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component self with
    | inl direct =>
        exact Or.inr (Or.inl ⟨self, direct, huTarget,
          hstep,
          canonicalStableRawComponentReferenceStepEmbedding_inl_rank_lt
            ends m j k l zero hloop hjk hkl hk0 p hno component
              self direct hstep⟩)
    | inr terminal =>
        exact Or.inl ⟨self, terminal, huTarget, hstep⟩
  · let direct : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨u, huComponent, hself⟩
    exact Or.inr (Or.inr
      ⟨direct, huTarget, huKind, hpreferredSelf⟩)




theorem
    canonicalStableRawComponentSecondAlternateFreeFiberRepresentativesEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (A : Finset (StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)))
    (hfree : ∀ anchor ∈ A,
      (canonicalStableRawComponentSecondAlternateTarget
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1 ≠
      canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p
          ⟨canonicalStableRawPreferredRightBase ends m j k l zero
              hloop hjk hkl hk0 p
                (canonicalStableRawComponentSecondAlternateTarget
                  ends m j k l zero hloop hjk hkl hk0 p hno component anchor),
            canonicalStableRawPreferredRightBase_mem ends m j k l zero
              hloop hjk hkl hk0 p
                (canonicalStableRawComponentSecondAlternateTarget
                  ends m j k l zero hloop hjk hkl hk0 p hno component anchor)⟩)
    (htarget : Function.Injective fun anchor : ↑A =>
      canonicalStableRawComponentSecondAlternateTarget
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor.1) :
    Nonempty (↑A ↪ CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  have hexists (anchor : ↑A) :
      ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawLeftTokenTarget
            ends m j k l zero hloop hjk hkl hk0 p terminal.1.1 =
          canonicalStableRawComponentSecondAlternateTarget
            ends m j k l zero hloop hjk hkl hk0 p hno component anchor.1 :=
    exists_canonicalStableRawComponentSecondAlternateFiber_freeTerminal
      ends m j k l zero hloop hjk hkl hk0 p hno component anchor.1
        (hfree anchor.1 anchor.2)
  let f : ↑A → CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component := fun anchor =>
    Classical.choose (hexists anchor)
  have hfTarget (anchor : ↑A) :
      canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p (f anchor).1.1 =
        canonicalStableRawComponentSecondAlternateTarget
          ends m j k l zero hloop hjk hkl hk0 p hno component anchor.1 :=
    Classical.choose_spec (hexists anchor)
  refine ⟨⟨f, ?_⟩⟩
  intro x y hxy
  apply htarget
  calc
    canonicalStableRawComponentSecondAlternateTarget
        ends m j k l zero hloop hjk hkl hk0 p hno component x.1 =
      canonicalStableRawLeftTokenTarget
        ends m j k l zero hloop hjk hkl hk0 p (f x).1.1 := (hfTarget x).symm
    _ = canonicalStableRawLeftTokenTarget
        ends m j k l zero hloop hjk hkl hk0 p (f y).1.1 := congrArg
          (fun terminal : CanonicalStableRawComponentNonexceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component =>
              canonicalStableRawLeftTokenTarget
                ends m j k l zero hloop hjk hkl hk0 p terminal.1.1) hxy
    _ = canonicalStableRawComponentSecondAlternateTarget
        ends m j k l zero hloop hjk hkl hk0 p hno component y.1 :=
      hfTarget y






noncomputable def canonicalStableRawComponentSecondAlternateFiberMinusOne
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    Finset (StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) := by
  classical
  exact (canonicalStableRawComponentSecondCollisionAlternateFiber
    ends m j k l zero hloop hjk hkl hk0 p hno component anchor).erase anchor

noncomputable def canonicalStableRawComponentSecondAlternateFiberMinusOneSourceTransport
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ↑(canonicalStableRawComponentSecondAlternateFiberMinusOne
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor) ↪
      (CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
        CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  let Second := StatMech.FrontierA.crossCollision
    (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (canonicalStableRawComponentDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component)
  let remaining := canonicalStableRawComponentSecondAlternateFiberMinusOne
    ends m j k l zero hloop hjk hkl hk0 p hno component anchor
  let inclusion := Function.Embedding.subtype
    (fun collision : Second => collision ∈ remaining)
  exact (inclusion.trans
    (canonicalStableRawComponentReferenceSourceCollisionEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component)).trans
        (canonicalStableRawComponentDirectSumNonexceptionalEquivToken
          ends m j k l zero hloop hjk hkl hk0 p hno component).symm.toEmbedding




theorem
    canonicalStableRawComponentSecondAlternateFiberMinusOne_directResidual
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (member : ↑(canonicalStableRawComponentSecondAlternateFiberMinusOne
      ends m j k l zero hloop hjk hkl hk0 p hno component anchor))
    (direct : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (htransport : canonicalStableRawComponentSecondAlternateFiberMinusOneSourceTransport
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor member =
      Sum.inl direct) :
    ∃ residual : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component),
      residual.1.1 = member.1 ∧ residual.1.2 = direct ∧
      residual.1.1.1.2.1.target = residual.1.2.1.target ∧
      canonicalStableRawSourceRank ends m j k l zero p
          residual.1.1.1.2.1.source <
        canonicalStableRawSourceRank ends m j k l zero p
          residual.1.2.1.source := by
  let sourceMap := canonicalStableRawComponentReferenceSourceCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let tokenEquiv := canonicalStableRawComponentDirectSumNonexceptionalEquivToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  change tokenEquiv.symm (sourceMap member.1) = Sum.inl direct at htransport
  have htoken := congrArg tokenEquiv htransport
  rw [tokenEquiv.apply_symm_apply] at htoken
  change sourceMap member.1 = directMap direct at htoken
  let residual : StatMech.FrontierA.crossCollision sourceMap directMap :=
    ⟨(member.1, direct), htoken⟩
  have hranked := canonicalStableRawComponentResidualCollision_ranked_sameTarget
    ends m j k l zero hloop hjk hkl hk0 p hno component residual
  exact ⟨residual, rfl, rfl, hranked.1, hranked.2⟩



theorem canonicalStableRawComponentSecondAlternateFiber_erase_card
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    (canonicalStableRawComponentSecondAlternateFiberMinusOne
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor).card + 1 =
      (canonicalStableRawComponentSecondCollisionAlternateFiber
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor).card := by
  classical
  unfold canonicalStableRawComponentSecondAlternateFiberMinusOne
  apply Finset.card_erase_add_one
  simp only [canonicalStableRawComponentSecondCollisionAlternateFiber,
    Finset.mem_filter, Finset.mem_univ, true_and]




theorem canonicalStableRawComponentTokenBlock_add_freshTokenEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (size : Nat)
    (tokens : Fin size ↪ CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (extra : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hfresh : ∀ i, extra ≠ tokens i) :
    Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  let f : Fin size ⊕ Fin 1 → CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
    | Sum.inl i => tokens i
    | Sum.inr _ => extra
  have hinjective : Function.Injective f := by
    intro x y hxy
    cases x with
    | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (tokens.injective hxy)
        | inr y => exact False.elim (hfresh x hxy.symm)
    | inr x =>
        cases y with
        | inl y => exact False.elim (hfresh y hxy)
        | inr y => exact congrArg Sum.inr (Subsingleton.elim x y)
  let block : Fin size ⊕ Fin 1 ↪ CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨f, hinjective⟩
  exact ⟨(finSumFinEquiv (m := size) (n := 1)).symm.toEmbedding.trans block⟩




theorem canonicalStableRawComponentTokenBlock_add_freshSourceCompanion
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (size : Nat)
    (tokens : Fin size ↪ CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hfresh : ∀ i,
      canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component anchor ≠
        tokens i) :
    Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) :=
  canonicalStableRawComponentTokenBlock_add_freshTokenEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component size tokens
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor)
      hfresh






theorem
    canonicalStableRawComponentReferenceSource_fresh_from_preferredSelfCycle
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (size : Nat)
    (directs : Fin size ↪ CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (σ : Equiv.Perm (Fin size))
    (hstep : ∀ i,
      (directs (σ i)).1 = canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno (directs i).1)
    (hpreferredSelf : ∀ i, (directs i).1.target.1 =
      canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p (directs i).1.target,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p (directs i).1.target⟩) :
    ∀ i,
      canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component anchor ≠
        canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component (directs i) := by
  classical
  intro i hcollision
  let sourceMap := canonicalStableRawComponentReferenceSourceCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let residual : StatMech.FrontierA.crossCollision sourceMap directMap :=
    ⟨(anchor, directs i), hcollision⟩
  let previous := σ.symm i
  have hpreviousStep : (directs i).1 =
      canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno
          (directs previous).1 := by
    calc
      (directs i).1 = (directs (σ previous)).1 := by simp [previous]
      _ = canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno
            (directs previous).1 := hstep previous
  have hadvancePrevious : CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno
        (directs previous).1 := by
    rcases canonicalStableRawExceptionalEdgeNext_advancing_or_ownerStable
        ends m j k l zero hloop hjk hkl hk0 p hno
          (directs previous).1 with hadvance | hstable
    · exact hadvance
    · exfalso
      apply canonicalStableRawOwnerStableStep_nextTarget_free_of_preferredSelf
        ends m j k l zero hloop hjk hkl hk0 p hno
          (directs previous).1 (hpreferredSelf previous) hstable
      rw [← hpreviousStep]
      exact hpreferredSelf i
  let previousOwner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p (directs previous).1.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p (directs previous).1.target⟩
  have hupperSource : (directs i).1.source = previousOwner := by
    apply Subtype.ext
    calc
      (directs i).1.source.1 =
          (canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno
              (directs previous).1).source.1 :=
        congrArg (fun edge => edge.source.1) hpreviousStep
      _ = canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p (directs previous).1.target :=
        hadvancePrevious
  have hupperSelf : canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p (directs i).1.source =
      (directs previous).1.target.1 := by
    rw [hupperSource]
    exact (hpreferredSelf previous).symm
  have hranked := canonicalStableRawComponentResidualCollision_ranked_sameTarget
    ends m j k l zero hloop hjk hkl hk0 p hno component residual
  have hbase :=
    canonicalStableRawComponentReferenceSource_directCollision_selfBase_eq
      ends m j k l zero hloop hjk hkl hk0 p hno component residual
  have hlowerSelf : canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p anchor.1.2.1.source =
      (directs previous).1.target.1 := by
    calc
      canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
          anchor.1.2.1.source =
        canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
          (directs i).1.source := by
            simpa only [residual] using hbase.symm
      _ = (directs previous).1.target.1 := hupperSelf
  have hsourceNe : anchor.1.2.1.source ≠ (directs i).1.source := by
    intro heq
    have hbad : canonicalStableRawSourceRank ends m j k l zero p
          (directs i).1.source <
        canonicalStableRawSourceRank ends m j k l zero p
          (directs i).1.source := by
      simpa only [residual, heq] using hranked.2
    exact (Nat.lt_irrefl _ hbad)
  have hnePreferred : anchor.1.2.1.source.1 ≠
      canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p (directs previous).1.target := by
    intro heq
    apply hsourceNe
    exact Subtype.ext (heq.trans (congrArg Subtype.val hupperSource).symm)
  have hreverse := canonicalStableRawPreferredRightBase_rank_lt_of_self
    ends m j k l zero hloop hjk hkl hk0 p (directs previous).1.target
      anchor.1.2.1.source hlowerSelf hnePreferred
  have hreverse' : canonicalStableRawSourceRank ends m j k l zero p
        (directs i).1.source <
      canonicalStableRawSourceRank ends m j k l zero p
        anchor.1.2.1.source := by
    rw [hupperSource]
    exact hreverse
  exact (Nat.not_lt_of_ge (Nat.le_of_lt hranked.2)) hreverse'



theorem
    canonicalStableRawComponentPreferredSelfCycle_strictTokenBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (size : Nat)
    (directs : Fin size ↪ CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (σ : Equiv.Perm (Fin size))
    (hstep : ∀ i,
      (directs (σ i)).1 = canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno (directs i).1)
    (hpreferredSelf : ∀ i, (directs i).1.target.1 =
      canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p (directs i).1.target,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p (directs i).1.target⟩) :
    Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  exact canonicalStableRawComponentTokenBlock_add_freshSourceCompanion
    ends m j k l zero hloop hjk hkl hk0 p hno component anchor size
      (directs.trans (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
      (canonicalStableRawComponentReferenceSource_fresh_from_preferredSelfCycle
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor size
          directs σ hstep hpreferredSelf)




theorem
    exists_canonicalStableRawComponentPreferredDirect_terminal_or_strictTokenBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (start : CanonicalStableRawComponentPreferredDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    let Preferred := CanonicalStableRawComponentPreferredDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let Direct := CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let Token := CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let step := canonicalStableRawComponentPreferredDirectStep
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let advance := partialForestAdvance step
    (∃ n ≤ Nat.card Preferred,
      ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        step (advance^[n] start) = Sum.inr terminal) ∨
      ∃ size : Nat, 0 < size ∧
        Nonempty (Fin size ↪ Direct) ∧
        Nonempty (Fin (size + 1) ↪ Token) := by
  classical
  dsimp only
  let Preferred := CanonicalStableRawComponentPreferredDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Token := CanonicalStableRawComponentToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let step : Preferred → Preferred ⊕
      CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
    canonicalStableRawComponentPreferredDirectStep
      ends m j k l zero hloop hjk hkl hk0 p hno component
  let advance := partialForestAdvance step
  letI : Fintype Preferred := Fintype.ofFinite Preferred
  rcases exists_partialForest_terminal_or_cycle step start with
    hterminal | ⟨startIndex, stopIndex, hlt, hbound, hrepeat, hsteps⟩
  · left
    simpa only [Nat.card_eq_fintype_card] using hterminal
  · let base := advance^[startIndex] start
    let length := stopIndex - startIndex
    have hlength : 0 < length := by omega
    have hshift (n : Nat) : advance^[n] base =
        advance^[startIndex + n] start := by
      calc
        advance^[n] base = advance^[n + startIndex] start := by
          exact (Function.iterate_add_apply advance n startIndex start).symm
        _ = advance^[startIndex + n] start := by rw [Nat.add_comm]
    have hclosed : advance^[length] base = base := by
      calc
        advance^[length] base = advance^[startIndex + length] start := hshift length
        _ = advance^[stopIndex] start := by congr 2 <;> omega
        _ = advance^[startIndex] start := hrepeat.symm
    have hcontinuation (n : Nat) (hn : n < length) :
        ∃ next, step (advance^[n] base) = Sum.inl next := by
      obtain ⟨next, hnext⟩ := hsteps (startIndex + n) (by omega)
      refine ⟨next, ?_⟩
      rw [hshift n]
      exact hnext
    obtain ⟨first, stop, hfirstStop, hstopLength, hstate, hdistinct⟩ :=
      exists_minimal_iterateKey_repeat_of_closedOrbit
        advance id base length hlength hclosed
    have hcyclePos : 0 < stop - first := by omega
    obtain ⟨cycleN, hcycle⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt hcyclePos)
    let cycleState : Fin (cycleN + 1) → Preferred := fun x =>
      advance^[first + x.1] base
    let σ : Equiv.Perm (Fin (cycleN + 1)) := finRotate (cycleN + 1)
    have hcycleStateInjective : Function.Injective cycleState := by
      intro x y hxy
      apply Fin.ext
      by_contra hval
      rcases lt_or_gt_of_ne hval with hxyVal | hyxVal
      · exact (hdistinct (first + x.1) (first + y.1) (by omega)
          (by omega)) hxy
      · exact (hdistinct (first + y.1) (first + x.1) (by omega)
          (by omega)) hxy.symm
    let directs : Fin (cycleN + 1) ↪ Direct :=
      ⟨fun x => (cycleState x).1, fun x y hxy =>
        hcycleStateInjective (Subtype.ext hxy)⟩
    have hcycleStep : ∀ x, cycleState (σ x) =
        advance (cycleState x) := by
      intro x
      by_cases hx : x = Fin.last cycleN
      · subst x
        simp only [cycleState, σ, finRotate_last, Fin.val_zero, Fin.val_last]
        calc
          advance^[first] base = advance^[stop] base := hstate
          _ = advance^[Nat.succ (first + cycleN)] base := by
            congr 2 <;> omega
          _ = advance (advance^[first + cycleN] base) :=
            Function.iterate_succ_apply' advance (first + cycleN) base
      · have hrotate : (σ x).1 = x.1 + 1 :=
          coe_finRotate_of_ne_last hx
        simp only [cycleState]
        rw [hrotate]
        convert Function.iterate_succ_apply' advance (first + x.1) base using 1 <;>
          omega
    have hrawStep : ∀ x, (directs (σ x)).1 =
        canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno (directs x).1 := by
      intro x
      have hxBound : first + x.1 < length := by
        have hxCycle : x.1 < stop - first := by simpa only [hcycle] using x.2
        omega
      obtain ⟨next, hnext⟩ := hcontinuation (first + x.1) hxBound
      have hadvance :=
        canonicalStableRawComponentPreferredDirectAdvance_eq_of_step
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (cycleState x) next hnext
      calc
        (directs (σ x)).1 = (cycleState (σ x)).1.1 := rfl
        _ = (advance (cycleState x)).1.1 := congrArg
          (fun state : Preferred => state.1.1) (hcycleStep x)
        _ = next.1.1 := congrArg (fun state : Preferred => state.1.1) hadvance
        _ = canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno
              (cycleState x).1.1 :=
          canonicalStableRawComponentPreferredDirectStep_inl_next
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (cycleState x) next hnext
        _ = canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno (directs x).1 := rfl
    have hpreferred : ∀ x, (directs x).1.target.1 =
        canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
          ⟨canonicalStableRawPreferredRightBase ends m j k l zero
              hloop hjk hkl hk0 p (directs x).1.target,
            canonicalStableRawPreferredRightBase_mem ends m j k l zero
              hloop hjk hkl hk0 p (directs x).1.target⟩ := fun x =>
      (cycleState x).2
    exact Or.inr ⟨cycleN + 1, by omega, ⟨directs⟩,
      canonicalStableRawComponentPreferredSelfCycle_strictTokenBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor
          (cycleN + 1) directs σ hrawStep hpreferred⟩






theorem
    exists_canonicalStableRawComponentPreferredDirect_strictTokenBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (start : CanonicalStableRawComponentPreferredDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    let Direct := CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let Token := CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
    ∃ size : Nat, 0 < size ∧
      Nonempty (Fin size ↪ Direct) ∧
      Nonempty (Fin (size + 1) ↪ Token) := by
  classical
  dsimp only
  let Preferred := CanonicalStableRawComponentPreferredDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Token := CanonicalStableRawComponentToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let step : Preferred → Preferred ⊕
      CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
    canonicalStableRawComponentPreferredDirectStep
      ends m j k l zero hloop hjk hkl hk0 p hno component
  let advance := partialForestAdvance step
  rcases
      exists_canonicalStableRawComponentPreferredDirect_terminal_or_strictTokenBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor start with
    hterminal | hstrict
  · let P := fun n : Nat => ∃ terminal,
        step (advance^[n] start) = Sum.inr terminal
    have hP : ∃ n, P n := by
      obtain ⟨n, _hn, terminal, hterminal⟩ := hterminal
      exact ⟨n, terminal, hterminal⟩
    let first := Nat.find hP
    obtain ⟨terminal, hfirstTerminal⟩ := Nat.find_spec hP
    have hfirst : ∀ n < first, ∀ other,
        step (advance^[n] start) ≠ Sum.inr other := by
      intro n hn other hother
      have hle := Nat.find_min' hP ⟨other, hother⟩
      exact (Nat.not_le_of_lt hn) hle
    have horbitInjective : Function.Injective fun i : Fin (first + 1) =>
        advance^[i.1] start :=
      partialForest_iterate_injective_through_first_terminal
        step start first ⟨terminal, hfirstTerminal⟩ hfirst
    let preferredOrbit : Fin (first + 1) ↪ Preferred :=
      ⟨fun i => advance^[i.1] start, horbitInjective⟩
    let directs : Fin (first + 1) ↪ Direct :=
      preferredOrbit.trans ⟨Subtype.val, Subtype.val_injective⟩
    refine ⟨first + 1, by omega, ⟨directs⟩, ?_⟩
    exact canonicalStableRawComponentTokenBlock_add_freshTokenEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (first + 1)
        (directs.trans (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component))
        terminal.1 (fun i =>
          canonicalStableRawComponentNonexceptionalToken_ne_direct
            ends m j k l zero hloop hjk hkl hk0 p hno component
              terminal (directs i))
  · exact hstrict





theorem canonicalStableRawComponentDirect_strictTokenBlock_of_anchor
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    ∃ size : Nat, 0 < size ∧
      Nonempty (Fin size ↪ CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
      Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  by_cases hpreferred : start.1.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p start.1.target,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p start.1.target⟩
  · let preferredStart : CanonicalStableRawComponentPreferredDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨start, hpreferred⟩
    exact exists_canonicalStableRawComponentPreferredDirect_strictTokenBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component anchor
        preferredStart
  · let raw := canonicalStableRawPreferredFreeLeftToken
        ends m j k l zero hloop hjk hkl hk0 p start.1.target hpreferred
    have hrawComponent : canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno raw = component :=
      (canonicalStableRawPreferredFreeLeftToken_fullComponent
        ends m j k l zero hloop hjk hkl hk0 p hno start.1 hpreferred).trans
          start.2.1
    let terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨⟨raw, hrawComponent⟩,
        canonicalStableRawPreferredFreeLeftToken_not_exceptional
          ends m j k l zero hloop hjk hkl hk0 p start.1.target hpreferred⟩
    let directs : Fin 1 ↪ CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨fun _ => start, fun x y _ => Subsingleton.elim x y⟩
    refine ⟨1, by omega, ⟨directs⟩, ?_⟩
    exact canonicalStableRawComponentTokenBlock_add_freshTokenEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component 1
        (directs.trans (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component))
        terminal.1 (fun i =>
          canonicalStableRawComponentNonexceptionalToken_ne_direct
            ends m j k l zero hloop hjk hkl hk0 p hno component
              terminal (directs i))






theorem
    exists_canonicalStableRawComponentSecondCollision_strictTokenBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ size : Nat, 0 < size ∧
      Nonempty (Fin size ↪ CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
      Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  have strictOfTerminal
      (terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) :
      ∃ size : Nat, 0 < size ∧
        Nonempty (Fin size ↪ CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
        Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) := by
    let directs : Fin 1 ↪ CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨fun _ => anchor.1.2, fun x y _ => Subsingleton.elim x y⟩
    refine ⟨1, by omega, ⟨directs⟩, ?_⟩
    exact canonicalStableRawComponentTokenBlock_add_freshTokenEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component 1
        (directs.trans (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component))
        terminal.1 (fun i =>
          canonicalStableRawComponentNonexceptionalToken_ne_direct
            ends m j k l zero hloop hjk hkl hk0 p hno component
              terminal (directs i))
  rcases
      canonicalStableRawComponentSecondAlternateFiber_terminal_or_preferredSelfOutput
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor with
    ⟨terminal, _⟩ | ⟨_u, _htarget, _hkind, _hcomponent, hpreferred⟩
  · exact strictOfTerminal terminal
  · rcases
        canonicalStableRawComponentSecondAlternatePreferredSelfOutput_stepSplit
          ends m j k l zero hloop hjk hkl hk0 p hno component anchor
            hpreferred with
      ⟨_self, terminal, _htarget, _hstep⟩ |
      ⟨_self, direct, _htarget, _hstep, _hrank⟩ |
      ⟨direct, _htarget, _hkind, _hpreferred⟩
    · exact strictOfTerminal terminal
    · exact canonicalStableRawComponentDirect_strictTokenBlock_of_anchor
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor direct
    · exact canonicalStableRawComponentDirect_strictTokenBlock_of_anchor
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor direct





theorem
    canonicalStableRawComponentSourceCompanion_strictBlock_or_residualCollision
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (size : Nat)
    (directs : Fin size ↪ CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      ∃ residual : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentReferenceSourceCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        residual.1.1 = anchor ∧
          (∃ i, residual.1.2 = directs i) ∧
          ∀ old : StatMech.FrontierA.crossCollision
              (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
                ends m j k l zero hloop hjk hkl hk0 p hno component)
              (canonicalStableRawComponentDirectEmbedding
                ends m j k l zero hloop hjk hkl hk0 p hno component),
            residual.1.2 ≠ old.1.2 := by
  classical
  let sourceMap := canonicalStableRawComponentReferenceSourceCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  by_cases hfresh : ∀ i, sourceMap anchor ≠ directMap (directs i)
  · left
    exact canonicalStableRawComponentTokenBlock_add_freshSourceCompanion
      ends m j k l zero hloop hjk hkl hk0 p hno component anchor size
        (directs.trans directMap) hfresh
  · right
    push Not at hfresh
    obtain ⟨i, hi⟩ := hfresh
    let residual : StatMech.FrontierA.crossCollision sourceMap directMap :=
      ⟨(anchor, directs i), hi⟩
    let unused :=
      canonicalStableRawReferenceSourceDirectCollisionToUnusedDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component
    exact ⟨residual, rfl, ⟨i, rfl⟩, (unused residual).2⟩





theorem
    canonicalStableRawComponentSourceCompanion_strictBlock_or_lowerRankEntry
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (size : Nat)
    (directs : Fin size ↪ CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      ∃ i,
        anchor.1.2.1.target = (directs i).1.target ∧
        canonicalStableRawSourceRank ends m j k l zero p
            anchor.1.2.1.source <
          canonicalStableRawSourceRank ends m j k l zero p
            (directs i).1.source ∧
        ∀ old : StatMech.FrontierA.crossCollision
            (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component)
            (canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component),
          directs i ≠ old.1.2 := by
  rcases
      canonicalStableRawComponentSourceCompanion_strictBlock_or_residualCollision
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor size
          directs with
    hstrict | ⟨residual, hanchor, ⟨i, hi⟩, hunused⟩
  · exact Or.inl hstrict
  · right
    have hranked := canonicalStableRawComponentResidualCollision_ranked_sameTarget
      ends m j k l zero hloop hjk hkl hk0 p hno component residual
    refine ⟨i, ?_, ?_, ?_⟩
    · simpa only [hanchor, hi] using hranked.1
    · simpa only [hanchor, hi] using hranked.2
    · intro old heq
      exact hunused old (hi.trans heq)


def canonicalStableRawComponentDirectStateEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component where
  toFun direct := ⟨direct.1, direct.2.1⟩
  inj' := by
    intro first second heq
    apply Subtype.ext
    exact congrArg
      (fun state : CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component => state.1) heq



structure CanonicalStableRawComponentRichStrictBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) where
  size : Nat
  positive : 0 < size
  directs : Fin size ↪ CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  tokens : Fin (size + 1) ↪ CanonicalStableRawComponentToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  aligned : ∀ i,
    tokens i.castSucc = canonicalStableRawComponentDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component (directs i)
  extra_nonexceptional : ¬ CanonicalStableRawLeftTokenIsExceptional
    ends m j k l zero hloop hjk hkl hk0 p (tokens (Fin.last size)).1




structure CanonicalStableRawComponentRichIncidenceBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) where
  size : Nat
  positive : 0 < size
  sources : Fin size ↪ CanonicalStableRawComponentState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  tokens : Fin (size + 1) ↪ CanonicalStableRawComponentToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  paired : ∀ i, CanonicalStableRawComponentIncident
    ends m j k l zero hloop hjk hkl hk0 p hno component
      (sources i) (tokens i.castSucc)
  extra_nonexceptional : ¬ CanonicalStableRawLeftTokenIsExceptional
    ends m j k l zero hloop hjk hkl hk0 p (tokens (Fin.last size)).1

def CanonicalStableRawComponentRichStrictBlock.sourceBlock
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Fin block.size ↪ CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
  block.directs.trans
    (canonicalStableRawComponentDirectStateEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component)

def CanonicalStableRawComponentRichStrictBlock.tokenPrefix
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Fin block.size ↪ CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
  Fin.castSuccEmb.trans block.tokens

def CanonicalStableRawComponentRichIncidenceBlock.tokenPrefix
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Fin block.size ↪ CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
  Fin.castSuccEmb.trans block.tokens

def CanonicalStableRawComponentRichIncidenceBlock.IsClosed
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) : Prop :=
  FiniteRelationTokenClosed
    (CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    block.size block.sources block.tokenPrefix


def CanonicalStableRawComponentRichStrictBlock.toIncidenceBlock
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component where
  size := block.size
  positive := block.positive
  sources := block.sourceBlock
  tokens := block.tokens
  paired := by
    intro i
    apply (canonicalStableRawWitnessedStateTokenIncidence_iff
      ends m j k l zero hloop hjk hkl hk0 p
        (block.tokens i.castSucc).1 (block.directs i).1).2
    rw [block.aligned i]
    exact canonicalStableRawStateLeftToken_stateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p hno (block.directs i).1
  extra_nonexceptional := block.extra_nonexceptional



theorem CanonicalStableRawComponentRichIncidenceBlock.extend
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : ∀ i, source ≠ block.sources i)
    (htoken : ∀ q, token ≠ block.tokens q)
    (hincident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component source token) :
    ∃ extended : CanonicalStableRawComponentRichIncidenceBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      extended.size = block.size + 1 := by
  obtain ⟨extendedSources, hsourcePrefix, hsourceLast⟩ :=
    finiteEmbedding_snoc block.size block.sources source hsource
  have htokenPrefixFresh : ∀ i, token ≠ block.tokenPrefix i := by
    intro i
    exact htoken i.castSucc
  obtain ⟨balancedTokens, hbalancedPrefix, hbalancedLast⟩ :=
    finiteEmbedding_snoc block.size block.tokenPrefix token htokenPrefixFresh
  let oldExtra := block.tokens (Fin.last block.size)
  have hextraFresh : ∀ q, oldExtra ≠ balancedTokens q := by
    intro q
    refine Fin.lastCases ?_ (fun i => ?_) q
    · rw [hbalancedLast]
      exact (htoken (Fin.last block.size)).symm
    · rw [hbalancedPrefix]
      intro heq
      exact Fin.castSucc_ne_last i (block.tokens.injective heq.symm)
  obtain ⟨extendedTokens, htokenPrefix, htokenLast⟩ :=
    finiteEmbedding_snoc (block.size + 1) balancedTokens oldExtra hextraFresh
  refine ⟨⟨block.size + 1, by omega, extendedSources, extendedTokens, ?_, ?_⟩,
    rfl⟩
  · intro i
    refine Fin.lastCases ?_ (fun q => ?_) i
    · have hsourceEq : extendedSources (Fin.last block.size) = source :=
        hsourceLast
      have htokenEq : extendedTokens (Fin.last block.size).castSucc = token :=
        (htokenPrefix (Fin.last block.size)).trans hbalancedLast
      rw [hsourceEq, htokenEq]
      exact hincident
    · have hsourceEq : extendedSources q.castSucc = block.sources q :=
        hsourcePrefix q
      have htokenEq : extendedTokens q.castSucc.castSucc =
          block.tokens q.castSucc :=
        (htokenPrefix q.castSucc).trans (hbalancedPrefix q)
      rw [hsourceEq, htokenEq]
      exact block.paired q
  · rw [htokenLast]
    exact block.extra_nonexceptional



noncomputable def CanonicalStableRawComponentRichIncidenceBlock.pivot
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : ∀ i, source ≠ block.sources i) (index : Fin block.size)
    (hincident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component source
        (block.tokens index.castSucc)) :
    CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component where
  size := block.size
  positive := block.positive
  sources := finiteEmbedding_replaceAt block.sources source hsource index
  tokens := block.tokens
  paired := by
    intro other
    by_cases hother : other = index
    · subst other
      rw [finiteEmbedding_replaceAt_same]
      exact hincident
    · rw [finiteEmbedding_replaceAt_ne
        block.sources source hsource index other hother]
      exact block.paired other
  extra_nonexceptional := block.extra_nonexceptional

@[simp] theorem CanonicalStableRawComponentRichIncidenceBlock.pivot_size
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : ∀ i, source ≠ block.sources i) (index : Fin block.size)
    (hincident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component source
        (block.tokens index.castSucc)) :
    (block.pivot source hsource index hincident).size = block.size := rfl

theorem CanonicalStableRawComponentRichIncidenceBlock.pivot_displaced_fresh
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : ∀ i, source ≠ block.sources i) (index : Fin block.size)
    (hincident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component source
        (block.tokens index.castSucc)) :
    ∀ other, block.sources index ≠
      (block.pivot source hsource index hincident).sources other := by
  exact finiteEmbedding_replaceAt_displaced_fresh
    block.sources source hsource index



def CanonicalStableRawComponentRichIncidenceBlock.PivotConfiguration
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :=
  { sources : Fin block.size ↪ CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component //
    ∀ i, CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (sources i) (block.tokens i.castSucc) }



def CanonicalStableRawComponentRichIncidenceBlock.PivotConfiguration.toBlock
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    (config : block.PivotConfiguration) :
    CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component where
  size := block.size
  positive := block.positive
  sources := config.1
  tokens := block.tokens
  paired := config.2
  extra_nonexceptional := block.extra_nonexceptional


def CanonicalStableRawComponentRichIncidenceBlock.basePivotConfiguration
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    block.PivotConfiguration := ⟨block.sources, block.paired⟩


def CanonicalStableRawComponentRichIncidenceBlock.PivotConfiguration.Step
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    (current next : block.PivotConfiguration) : Prop :=
  ∃ source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component,
    ∃ hsource : ∀ i, source ≠ current.1 i,
      ∃ index : Fin block.size,
        ∃ hincident : CanonicalStableRawComponentIncident
          ends m j k l zero hloop hjk hkl hk0 p hno component source
            (block.tokens index.castSucc),
          next.1 = finiteEmbedding_replaceAt
            current.1 source hsource index


noncomputable def CanonicalStableRawComponentRichIncidenceBlock.PivotConfiguration.rankSum
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    (config : block.PivotConfiguration) : Nat :=
  ∑ i, canonicalStableRawSourceRank ends m j k l zero p
    (config.1 i).1.source

theorem CanonicalStableRawComponentRichIncidenceBlock.closed_or_crossing
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    block.IsClosed ∨
      ∃ source token,
        CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component source token ∧
          (∀ i, source ≠ block.sources i) ∧
          ∃ i, token = block.tokenPrefix i := by
  exact finiteRelationTokenClosed_or_crossing
    (CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    block.size block.sources block.tokenPrefix

theorem CanonicalStableRawComponentRichIncidenceBlock.reducedDeficit
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hclosed : block.IsClosed)
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) <
      Fintype.card (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    Fintype.card (FiniteEmbeddingComplement block.size block.tokenPrefix) <
        Fintype.card (FiniteEmbeddingComplement block.size block.sources) ∧
      ∀ source : FiniteEmbeddingComplement block.size block.sources,
        ∀ token,
          CanonicalStableRawComponentIncident
              ends m j k l zero hloop hjk hkl hk0 p hno component
                source.1 token ->
            token ∉ finiteEmbeddingBlock block.size block.tokenPrefix := by
  refine ⟨finiteEmbeddingComplement_strictDeficit
      block.size block.sources block.tokenPrefix hdeficit, ?_⟩
  intro source token hincident
  exact finiteRelationComplement_tokenClosed
    (CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    block.size block.sources block.tokenPrefix hclosed source token hincident

theorem exists_canonicalStableRawComponent_closedRichIncidenceBlock_of_extension
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hextend : ∀ block : CanonicalStableRawComponentRichIncidenceBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      ¬ block.IsClosed ->
        ∃ extended : CanonicalStableRawComponentRichIncidenceBlock
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          extended.size = block.size + 1) :
    ∃ block : CanonicalStableRawComponentRichIncidenceBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      block.IsClosed := by
  apply exists_closedBlock_of_strictExtension
    (Nat.card (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (fun block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component => block.size)
    CanonicalStableRawComponentRichIncidenceBlock.IsClosed
  · intro block
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective
      block.sources block.sources.injective
  · exact hextend
  · exact start




theorem exists_canonicalStableRawComponent_sizeMaximalRichIncidenceBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    ∃ block : CanonicalStableRawComponentRichIncidenceBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      ∀ other : CanonicalStableRawComponentRichIncidenceBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        other.size ≤ block.size := by
  apply exists_sizeMaximalBlock
    (Nat.card (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (fun block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component => block.size)
  · intro block
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective
      block.sources block.sources.injective
  · exact start

theorem CanonicalStableRawComponentRichIncidenceBlock.closureStep
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    block.IsClosed ∨
      (∃ extended : CanonicalStableRawComponentRichIncidenceBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        extended.size = block.size + 1) ∨
      ∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        (∀ i, source ≠ block.sources i) ∧
        ∃ q, canonicalStableRawComponentNaturalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component source =
          block.tokens q := by
  rcases block.closed_or_crossing with hclosed |
      ⟨source, _crossingToken, _hcrossing, hsource, _index, _htoken⟩
  · exact Or.inl hclosed
  · let natural := canonicalStableRawComponentNaturalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component source
    have hnaturalIncident : CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component source natural := by
      apply (canonicalStableRawWitnessedStateTokenIncidence_iff
        ends m j k l zero hloop hjk hkl hk0 p natural.1 source.1).2
      exact canonicalStableRawStateLeftToken_stateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p hno source.1
    by_cases hfresh : ∀ q, natural ≠ block.tokens q
    · exact Or.inr (Or.inl
        (block.extend source natural hsource hfresh hnaturalIncident))
    · right
      right
      push Not at hfresh
      exact ⟨source, hsource, hfresh⟩



theorem canonicalStableRawComponent_naturalToken_target_eq_of_direct
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hdirect : source.1.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p source.1.source) :
    canonicalStableRawLeftTokenTarget
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawComponentNaturalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component source).1 =
      source.1.target := by
  classical
  change canonicalStableRawLeftTokenTarget
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawStateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno source.1) =
    source.1.target
  unfold canonicalStableRawStateLeftToken
  rw [dif_neg hdirect]
  rfl



theorem canonicalStableRawOwnerStableOutput_eq_of_directNaturalTarget
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hdirect : source.1.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p source.1.source)
    (u : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (htarget : u.target = canonicalStableRawLeftTokenTarget
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component source).1)
    (hstable : CanonicalStableRawOwnerStableOutput
      ends m j k l zero hloop hjk hkl hk0 p source.1 u) :
    u = source.1 := by
  apply canonicalStableRawExceptionalEdge_eq_of_source_target_eq
  · exact hstable.1
  · exact htarget.trans
      (canonicalStableRawComponent_naturalToken_target_eq_of_direct
        source hdirect)



theorem canonicalStableRawOwnerAdvancingOutput_false_of_directNaturalTarget
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hdirect : source.1.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p source.1.source)
    (u : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (htarget : u.target = canonicalStableRawLeftTokenTarget
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component source).1)
    (hadvancing : CanonicalStableRawOwnerAdvancingOutput
      ends m j k l zero hloop hjk hkl hk0 p source.1 u) : False := by
  apply u.exceptional
  exact hadvancing.trans (congrArg
    (canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p)
    (htarget.trans
      (canonicalStableRawComponent_naturalToken_target_eq_of_direct
        source hdirect)).symm)

theorem
    CanonicalStableRawComponentRichIncidenceBlock.repeatedNaturalDischarge
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : ∀ i, source ≠ block.sources i)
    (q : Fin (block.size + 1))
    (hrepeat : canonicalStableRawComponentNaturalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component source =
      block.tokens q) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 = canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component source) ∨
      (∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
            ends m j k l zero hloop hjk hkl hk0 p
              (canonicalStableRawComponentNaturalToken
                ends m j k l zero hloop hjk hkl hk0 p hno component source).1 ∧
          CanonicalStableRawOwnerStableOutput
            ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
            ends m j k l zero hloop hjk hkl hk0 p
              (canonicalStableRawComponentNaturalToken
                ends m j k l zero hloop hjk hkl hk0 p hno component source).1 ∧
          CanonicalStableRawOwnerAdvancingOutput
            ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  let natural := canonicalStableRawComponentNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component source
  by_cases hlast : q = Fin.last block.size
  · subst q
    left
    let terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨natural, by
        intro hexceptional
        apply block.extra_nonexceptional
        rw [← hrepeat]
        exact hexceptional⟩
    exact ⟨terminal, rfl⟩
  · have hlt : q < Fin.last block.size :=
      Fin.lt_last_iff_ne_last.mpr hlast
    let i : Fin block.size := ⟨q.1, by
      exact hlt⟩
    have hq : i.castSucc = q := by
      apply Fin.ext
      rfl
    rw [← hq] at hrepeat
    have hnewIncident : CanonicalStableRawWitnessedStateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p natural.1 source.1 := by
      apply (canonicalStableRawWitnessedStateTokenIncidence_iff
        ends m j k l zero hloop hjk hkl hk0 p natural.1 source.1).2
      exact canonicalStableRawStateLeftToken_stateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p hno source.1
    have holdIncident : CanonicalStableRawWitnessedStateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p natural.1
          (block.sources i).1 := by
      have hpaired := block.paired i
      rw [← hrepeat] at hpaired
      exact hpaired
    rcases canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
        ends m j k l zero hloop hjk hkl hk0 p hno natural.1
          source.1 (block.sources i).1 hnewIncident holdIncident with
      heq | ⟨u, htarget, hkind, hcomponent, _⟩ |
        ⟨u, htarget, hkind, hcomponent, _⟩
    · exact False.elim (hsource i (Subtype.ext heq))
    · exact Or.inr (Or.inl
        ⟨u, htarget, hkind, hcomponent.trans source.2⟩)
    · exact Or.inr (Or.inr
        ⟨u, htarget, hkind, hcomponent.trans source.2⟩)

theorem CanonicalStableRawComponentRichIncidenceBlock.closureDischarge
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    block.IsClosed ∨
      (∃ extended : CanonicalStableRawComponentRichIncidenceBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        extended.size = block.size + 1) ∨
      (∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          terminal.1 = canonicalStableRawComponentNaturalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component source) ∨
      (∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          u.target = canonicalStableRawLeftTokenTarget
              ends m j k l zero hloop hjk hkl hk0 p
                (canonicalStableRawComponentNaturalToken
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    source).1 ∧
            CanonicalStableRawOwnerStableOutput
              ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧
            canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨
      ∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          u.target = canonicalStableRawLeftTokenTarget
              ends m j k l zero hloop hjk hkl hk0 p
                (canonicalStableRawComponentNaturalToken
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    source).1 ∧
            CanonicalStableRawOwnerAdvancingOutput
              ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧
            canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  rcases block.closureStep with hclosed | hextended |
      ⟨source, hsource, q, hrepeat⟩
  · exact Or.inl hclosed
  · exact Or.inr (Or.inl hextended)
  · rcases block.repeatedNaturalDischarge source hsource q hrepeat with
      ⟨terminal, hterminal⟩ | ⟨u, htarget, hstable, hcomponent⟩ |
        ⟨u, htarget, hadvancing, hcomponent⟩
    · exact Or.inr (Or.inr (Or.inl ⟨source, terminal, hterminal⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨source, u, htarget, hstable, hcomponent⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨source, u, htarget, hadvancing, hcomponent⟩)))



theorem
    CanonicalStableRawComponentRichIncidenceBlock.extendBySuccessor_or_repeat
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : ∀ i, source ≠ block.sources i) :
    (∃ extended : CanonicalStableRawComponentRichIncidenceBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        extended.size = block.size + 1) ∨
      ∃ q, canonicalStableRawComponentSuccessorToken
            ends m j k l zero hloop hjk hkl hk0 p hno component source =
          block.tokens q := by
  let successor := canonicalStableRawComponentSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component source
  have hsuccessorIncident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component source successor :=
    canonicalStableRawComponentSuccessorToken_incident
      ends m j k l zero hloop hjk hkl hk0 p hno component source
  by_cases hfresh : ∀ q, successor ≠ block.tokens q
  · exact Or.inl (block.extend source successor hsource hfresh hsuccessorIncident)
  · right
    push Not at hfresh
    exact hfresh

theorem
    CanonicalStableRawComponentRichIncidenceBlock.repeatedSuccessorDischarge
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : ∀ i, source ≠ block.sources i)
    (q : Fin (block.size + 1))
    (hrepeat : canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component source =
      block.tokens q) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 = canonicalStableRawComponentSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component source) ∨
      (∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
            ends m j k l zero hloop hjk hkl hk0 p
              (canonicalStableRawComponentSuccessorToken
                ends m j k l zero hloop hjk hkl hk0 p hno component source).1 ∧
          CanonicalStableRawOwnerStableOutput
            ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
            ends m j k l zero hloop hjk hkl hk0 p
              (canonicalStableRawComponentSuccessorToken
                ends m j k l zero hloop hjk hkl hk0 p hno component source).1 ∧
          CanonicalStableRawOwnerAdvancingOutput
            ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  let successor := canonicalStableRawComponentSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component source
  by_cases hlast : q = Fin.last block.size
  · subst q
    left
    let terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨successor, by
        intro hexceptional
        apply block.extra_nonexceptional
        rw [← hrepeat]
        exact hexceptional⟩
    exact ⟨terminal, rfl⟩
  · have hlt : q < Fin.last block.size :=
      Fin.lt_last_iff_ne_last.mpr hlast
    let i : Fin block.size := ⟨q.1, hlt⟩
    have hq : i.castSucc = q := by
      apply Fin.ext
      rfl
    rw [← hq] at hrepeat
    have hnewIncident : CanonicalStableRawWitnessedStateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p successor.1 source.1 :=
      canonicalStableRawComponentSuccessorToken_incident
        ends m j k l zero hloop hjk hkl hk0 p hno component source
    have holdIncident : CanonicalStableRawWitnessedStateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p successor.1
          (block.sources i).1 := by
      have hpaired := block.paired i
      rw [← hrepeat] at hpaired
      exact hpaired
    rcases canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
        ends m j k l zero hloop hjk hkl hk0 p hno successor.1
          source.1 (block.sources i).1 hnewIncident holdIncident with
      heq | ⟨u, htarget, hkind, hcomponent, _⟩ |
        ⟨u, htarget, hkind, hcomponent, _⟩
    · exact False.elim (hsource i (Subtype.ext heq))
    · exact Or.inr (Or.inl
        ⟨u, htarget, hkind, hcomponent.trans source.2⟩)
    · exact Or.inr (Or.inr
        ⟨u, htarget, hkind, hcomponent.trans source.2⟩)



def CanonicalStableRawComponentRichStrictBlock.IsClosed
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) : Prop :=
  FiniteRelationTokenClosed
    (CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    block.size block.sourceBlock block.tokenPrefix



theorem CanonicalStableRawComponentRichStrictBlock.closed_or_crossing
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    block.IsClosed ∨
      ∃ source token,
        CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component source token ∧
          (∀ i, source ≠ block.sourceBlock i) ∧
          ∃ i, token = block.tokenPrefix i := by
  exact finiteRelationTokenClosed_or_crossing
    (CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    block.size block.sourceBlock block.tokenPrefix




theorem CanonicalStableRawComponentRichStrictBlock.reducedDeficit
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hclosed : block.IsClosed)
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) <
      Fintype.card (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    Fintype.card (FiniteEmbeddingComplement block.size block.tokenPrefix) <
        Fintype.card (FiniteEmbeddingComplement block.size block.sourceBlock) ∧
      (∃ extra : FiniteEmbeddingComplement block.size block.tokenPrefix,
        extra.1 = block.tokens (Fin.last block.size)) ∧
      ∀ source : FiniteEmbeddingComplement block.size block.sourceBlock,
        ∀ token,
          CanonicalStableRawComponentIncident
              ends m j k l zero hloop hjk hkl hk0 p hno component
                source.1 token ->
            token ∉ finiteEmbeddingBlock block.size block.tokenPrefix := by
  refine ⟨finiteEmbeddingComplement_strictDeficit
      block.size block.sourceBlock block.tokenPrefix hdeficit, ?_, ?_⟩
  · let extra : FiniteEmbeddingComplement block.size block.tokenPrefix :=
      ⟨block.tokens (Fin.last block.size), by
        intro hmem
        obtain ⟨i, _hi, heq⟩ := Finset.mem_map.mp hmem
        exact Fin.castSucc_ne_last i (block.tokens.injective heq)⟩
    exact ⟨extra, rfl⟩
  · intro source token hincident
    exact finiteRelationComplement_tokenClosed
      (CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      block.size block.sourceBlock block.tokenPrefix hclosed
        source token hincident




theorem
    CanonicalStableRawComponentRichStrictBlock.crossingClassification
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hincident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component source token)
    (hsource : ∀ i, source ≠ block.sourceBlock i)
    (index : Fin block.size) (htoken : token = block.tokenPrefix index) :
    (∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p token.1 ∧
        CanonicalStableRawOwnerStableOutput
          ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p token.1 ∧
        CanonicalStableRawOwnerAdvancingOutput
          ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  have htokenDirect : token =
      canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component
          (block.directs index) := by
    exact htoken.trans (block.aligned index)
  have hsourceIncident : CanonicalStableRawWitnessedStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token.1 source.1 := hincident
  have hdirectIncident : CanonicalStableRawWitnessedStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token.1
        (block.directs index).1 := by
    apply (canonicalStableRawWitnessedStateTokenIncidence_iff
      ends m j k l zero hloop hjk hkl hk0 p token.1
        (block.directs index).1).2
    rw [htokenDirect]
    exact canonicalStableRawStateLeftToken_stateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p hno (block.directs index).1
  rcases canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
      ends m j k l zero hloop hjk hkl hk0 p hno token.1
        source.1 (block.directs index).1 hsourceIncident hdirectIncident with
    heq | ⟨u, htarget, hkind, hcomponent, _⟩ |
      ⟨u, htarget, hkind, hcomponent, _⟩
  · exact False.elim (hsource index (by
      apply Subtype.ext
      exact heq))
  · exact Or.inl ⟨u, htarget, hkind, hcomponent.trans source.2⟩
  · exact Or.inr ⟨u, htarget, hkind, hcomponent.trans source.2⟩




theorem canonicalStableRawComponent_state_terminal_or_crossCollision_or_direct
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (state : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 = canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component state) ∨
      (∃ collision : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        state.1 = collision.1.1.1) ∨
      ∃ direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        state.1 = direct.1 := by
  classical
  let token := canonicalStableRawComponentNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component state
  by_cases hself : state.1.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p state.1.source
  · let self : CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨state.1, state.2, hself⟩
    by_cases hexceptional : CanonicalStableRawLeftTokenIsExceptional
        ends m j k l zero hloop hjk hkl hk0 p token.1
    · let exceptionalToken : CanonicalStableRawComponentExceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
        ⟨token, hexceptional⟩
      let direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
        (canonicalStableRawComponentDirectStateEquivExceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component).symm
            exceptionalToken
      have hdirectToken :
          canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component direct =
            token := by
        exact congrArg Subtype.val
          ((canonicalStableRawComponentDirectStateEquivExceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component).apply_symm_apply
              exceptionalToken)
      have hselfToken :
          canonicalStableRawComponentSelfEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component self =
            token := by
        apply Subtype.ext
        rfl
      let collision : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component) :=
        ⟨(self, direct), hselfToken.trans hdirectToken.symm⟩
      exact Or.inr (Or.inl ⟨collision, rfl⟩)
    · let terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
        ⟨token, hexceptional⟩
      exact Or.inl ⟨terminal, rfl⟩
  · let direct : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨state.1, state.2, hself⟩
    exact Or.inr (Or.inr ⟨direct, rfl⟩)




theorem
    CanonicalStableRawComponentRichIncidenceBlock.closureStep_stateClassification
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    block.IsClosed ∨
      (∃ extended : CanonicalStableRawComponentRichIncidenceBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        extended.size = block.size + 1) ∨
      ∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        (∀ i, source ≠ block.sources i) ∧
        (∃ q, canonicalStableRawComponentNaturalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component source =
          block.tokens q) ∧
        ((∃ terminal : CanonicalStableRawComponentNonexceptionalToken
              ends m j k l zero hloop hjk hkl hk0 p hno component,
            terminal.1 = canonicalStableRawComponentNaturalToken
              ends m j k l zero hloop hjk hkl hk0 p hno component source) ∨
          (∃ collision : StatMech.FrontierA.crossCollision
              (canonicalStableRawComponentSelfEmbedding
                ends m j k l zero hloop hjk hkl hk0 p hno component)
              (canonicalStableRawComponentDirectEmbedding
                ends m j k l zero hloop hjk hkl hk0 p hno component),
            source.1 = collision.1.1.1) ∨
          ∃ direct : CanonicalStableRawComponentDirectState
              ends m j k l zero hloop hjk hkl hk0 p hno component,
            source.1 = direct.1) := by
  rcases block.closureStep with hclosed | hextended |
      ⟨source, hsource, q, hrepeat⟩
  · exact Or.inl hclosed
  · exact Or.inr (Or.inl hextended)
  · refine Or.inr (Or.inr ⟨source, hsource, ⟨q, hrepeat⟩, ?_⟩)
    exact canonicalStableRawComponent_state_terminal_or_crossCollision_or_direct
      ends m j k l zero hloop hjk hkl hk0 p hno component source



theorem canonicalStableRawComponentDirectBlock_add_terminalRichStrictBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (size : Nat) (hsize : 0 < size)
    (directs : Fin size ↪ CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (terminal : CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Nonempty (CanonicalStableRawComponentRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  let natural : Fin size ↪ CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
    directs.trans (canonicalStableRawComponentDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component)
  have hfresh : ∀ i, terminal.1 ≠ natural i := by
    intro i
    exact canonicalStableRawComponentNonexceptionalToken_ne_direct
      ends m j k l zero hloop hjk hkl hk0 p hno component
        terminal (directs i)
  obtain ⟨tokens, haligned, hextra⟩ :=
    finiteEmbedding_snoc size natural terminal.1 hfresh
  refine ⟨⟨size, hsize, directs, tokens, haligned, ?_⟩⟩
  rw [hextra]
  exact terminal.2



theorem CanonicalStableRawComponentRichStrictBlock.extendDirect
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (direct : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hfresh : ∀ q,
      canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component direct ≠
        block.tokens q) :
    ∃ extended : CanonicalStableRawComponentRichStrictBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      extended.size = block.size + 1 := by
  let natural := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component direct
  have hdirectFresh : ∀ i, direct ≠ block.directs i := by
    intro i heq
    apply hfresh i.castSucc
    exact (congrArg
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component) heq).trans
          (block.aligned i).symm
  obtain ⟨extendedDirects, hdirectPrefix, hdirectLast⟩ :=
    finiteEmbedding_snoc block.size block.directs direct hdirectFresh
  have hnaturalFresh : ∀ i, natural ≠ block.tokenPrefix i := by
    intro i
    exact hfresh i.castSucc
  obtain ⟨balancedTokens, hbalancedPrefix, hbalancedLast⟩ :=
    finiteEmbedding_snoc block.size block.tokenPrefix natural hnaturalFresh
  let oldExtra := block.tokens (Fin.last block.size)
  have hextraFresh : ∀ q, oldExtra ≠ balancedTokens q := by
    intro q
    refine Fin.lastCases ?_ (fun i => ?_) q
    · rw [hbalancedLast]
      exact (hfresh (Fin.last block.size)).symm
    · rw [hbalancedPrefix]
      intro heq
      exact Fin.castSucc_ne_last i (block.tokens.injective heq.symm)
  obtain ⟨extendedTokens, htokenPrefix, htokenLast⟩ :=
    finiteEmbedding_snoc (block.size + 1) balancedTokens oldExtra hextraFresh
  refine ⟨⟨block.size + 1, by omega, extendedDirects, extendedTokens, ?_, ?_⟩,
    rfl⟩
  · intro i
    refine Fin.lastCases ?_ (fun q => ?_) i
    · calc
        extendedTokens (Fin.last block.size).castSucc =
            balancedTokens (Fin.last block.size) :=
          htokenPrefix (Fin.last block.size)
        _ = natural := hbalancedLast
        _ = canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component direct := rfl
        _ = canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (extendedDirects (Fin.last block.size)) :=
          congrArg _ hdirectLast.symm
    · calc
        extendedTokens q.castSucc.castSucc = balancedTokens q.castSucc :=
          htokenPrefix q.castSucc
        _ = block.tokenPrefix q := hbalancedPrefix q
        _ = block.tokens q.castSucc := rfl
        _ = canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (block.directs q) := block.aligned q
        _ = canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (extendedDirects q.castSucc) :=
          congrArg _ (hdirectPrefix q).symm
  · rw [htokenLast]
    exact block.extra_nonexceptional





theorem
    CanonicalStableRawComponentRichStrictBlock.extendDirect_of_freshSource
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : ∀ i, source ≠ block.sourceBlock i)
    (direct : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstate : source.1 = direct.1) :
    ∃ extended : CanonicalStableRawComponentRichStrictBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      extended.size = block.size + 1 := by
  have hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component direct).1 := by
    change CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawStateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno direct.1)
    unfold canonicalStableRawStateLeftToken
    rw [dif_neg direct.2.2]
    exact canonicalStableRawDirectLeftToken_isExceptional
      ends m j k l zero hloop hjk hkl hk0 p direct.1 direct.2.2
  obtain ⟨extended, hsize⟩ := block.extendDirect direct (by
    intro q
    refine Fin.lastCases ?_ (fun i => ?_) q
    · intro heq
      apply block.extra_nonexceptional
      rw [← heq]
      exact hexceptional
    · intro heq
      have hdirectEq : direct = block.directs i := by
        apply (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component).injective
        exact heq.trans (block.aligned i)
      apply hsource i
      apply Subtype.ext
      exact hstate.trans (congrArg
        (fun state : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component => state.1)
            hdirectEq))
  exact ⟨extended, hsize⟩



theorem exists_canonicalStableRawComponent_closedRichStrictBlock_of_extension
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hextend : ∀ block : CanonicalStableRawComponentRichStrictBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      ¬ block.IsClosed ->
        ∃ extended : CanonicalStableRawComponentRichStrictBlock
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          extended.size = block.size + 1) :
    ∃ block : CanonicalStableRawComponentRichStrictBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      block.IsClosed := by
  apply exists_closedBlock_of_strictExtension
    (Nat.card (CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (fun block : CanonicalStableRawComponentRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component => block.size)
    CanonicalStableRawComponentRichStrictBlock.IsClosed
  · intro block
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective
      block.directs block.directs.injective
  · exact hextend
  · exact start




theorem CanonicalStableRawComponentRichStrictBlock.closureStep
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    block.IsClosed ∨
      (∃ extended : CanonicalStableRawComponentRichStrictBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        extended.size = block.size + 1) ∨
      (∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          terminal.1 = canonicalStableRawComponentNaturalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component source) ∨
      ∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ collision : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
          source.1 = collision.1.1.1 := by
  rcases block.closed_or_crossing with hclosed |
      ⟨source, _token, _hincident, hsource, _index, _htoken⟩
  · exact Or.inl hclosed
  · rcases canonicalStableRawComponent_state_terminal_or_crossCollision_or_direct
        ends m j k l zero hloop hjk hkl hk0 p hno component source with
      ⟨terminal, _hterminal⟩ | ⟨collision, hself⟩ | ⟨direct, hdirect⟩
    · exact Or.inr (Or.inr (Or.inl ⟨source, terminal, _hterminal⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨source, collision, hself⟩))
    · exact Or.inr (Or.inl
        (block.extendDirect_of_freshSource source hsource direct hdirect))




theorem canonicalStableRawComponentDirectBlock_add_terminalTokenEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (size : Nat)
    (directs : Fin size ↪ CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (terminal : CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  let terminalEmbedding : Fin 1 ↪
      CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨fun _ => terminal, fun x y _ => Subsingleton.elim x y⟩
  let splitEmbedding := Function.Embedding.sumMap directs terminalEmbedding
  let sourceEmbedding : Fin (size + 1) ↪ Fin size ⊕ Fin 1 :=
    (finSumFinEquiv (m := size) (n := 1)).symm.toEmbedding
  exact ⟨(sourceEmbedding.trans splitEmbedding).trans
    (canonicalStableRawComponentDirectSumNonexceptionalEquivToken
      ends m j k l zero hloop hjk hkl hk0 p hno component).toEmbedding⟩





theorem
    exists_canonicalStableRawComponentDirect_terminal_or_strictTokenBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (available : CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    let Direct := CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let Token := CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let advance := canonicalStableRawComponentDirectForestAdvance
      ends m j k l zero hloop hjk hkl hk0 p hno component
    (∃ n ≤ Nat.card Direct,
      ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ =
          Sum.inr terminal) ∨
      ∃ size : Nat, 0 < size ∧
        Nonempty (Fin size ↪ Direct) ∧
        Nonempty (Fin (size + 1) ↪ Token) := by
  classical
  dsimp only
  rcases exists_canonicalStableRawComponentDirect_terminal_or_balancedBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component start with
    hterminal | ⟨size, hsize, hdirects, _htokens⟩
  · exact Or.inl hterminal
  · obtain ⟨directs⟩ := hdirects
    exact Or.inr ⟨size, hsize, ⟨directs⟩,
      canonicalStableRawComponentDirectBlock_add_terminalTokenEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component
          size directs available⟩




theorem exists_canonicalStableRawComponentDirect_strictTokenBlock_of_available
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (available : CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    ∃ size : Nat, 0 < size ∧
      Nonempty (Fin size ↪ CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
      Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let step : Direct -> Direct ⊕
      CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
    canonicalStableRawComponentDirectForestStep
      ends m j k l zero hloop hjk hkl hk0 p hno component
  let advance := partialForestAdvance step
  rcases exists_canonicalStableRawComponentDirect_terminal_or_balancedBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component start with
    hterminal | ⟨size, hsize, hdirects, _htokens⟩
  · let P := fun n : Nat => ∃ terminal,
        step (advance^[n] start) = Sum.inr terminal
    have hP : ∃ n, P n := by
      obtain ⟨n, _hn, terminal, hterminal⟩ := hterminal
      refine ⟨n, terminal, ?_⟩
      simpa only [step, advance,
        canonicalStableRawComponentDirectForestAdvance,
        canonicalStableRawComponentDirectForestStep] using hterminal
    let first := Nat.find hP
    obtain ⟨terminal, hfirstTerminal⟩ := Nat.find_spec hP
    have hfirst : ∀ n < first, ∀ other,
        step (advance^[n] start) ≠ Sum.inr other := by
      intro n hn other hother
      have hle := Nat.find_min' hP ⟨other, hother⟩
      exact (Nat.not_le_of_lt hn) hle
    have horbitInjective : Function.Injective fun i : Fin (first + 1) =>
        advance^[i.1] start :=
      partialForest_iterate_injective_through_first_terminal
        step start first ⟨terminal, hfirstTerminal⟩ hfirst
    let directs : Fin (first + 1) ↪ Direct :=
      ⟨fun i => advance^[i.1] start, horbitInjective⟩
    refine ⟨first + 1, by omega, ⟨directs⟩, ?_⟩
    exact canonicalStableRawComponentDirectBlock_add_terminalTokenEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (first + 1) directs terminal
  · obtain ⟨directs⟩ := hdirects
    exact ⟨size, hsize, ⟨directs⟩,
      canonicalStableRawComponentDirectBlock_add_terminalTokenEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component
          size directs available⟩



theorem exists_canonicalStableRawComponentDirect_richStrictBlock_of_available
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (available : CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Nonempty (CanonicalStableRawComponentRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let step : Direct -> Direct ⊕
      CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
    canonicalStableRawComponentDirectForestStep
      ends m j k l zero hloop hjk hkl hk0 p hno component
  let advance := partialForestAdvance step
  rcases exists_canonicalStableRawComponentDirect_terminal_or_balancedBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component start with
    hterminal | ⟨size, hsize, hdirects, _htokens⟩
  · let P := fun n : Nat => ∃ terminal,
        step (advance^[n] start) = Sum.inr terminal
    have hP : ∃ n, P n := by
      obtain ⟨n, _hn, terminal, hterminal⟩ := hterminal
      refine ⟨n, terminal, ?_⟩
      simpa only [step, advance,
        canonicalStableRawComponentDirectForestAdvance,
        canonicalStableRawComponentDirectForestStep] using hterminal
    let first := Nat.find hP
    obtain ⟨terminal, hfirstTerminal⟩ := Nat.find_spec hP
    have hfirst : ∀ n < first, ∀ other,
        step (advance^[n] start) ≠ Sum.inr other := by
      intro n hn other hother
      have hle := Nat.find_min' hP ⟨other, hother⟩
      exact (Nat.not_le_of_lt hn) hle
    have horbitInjective : Function.Injective fun i : Fin (first + 1) =>
        advance^[i.1] start :=
      partialForest_iterate_injective_through_first_terminal
        step start first ⟨terminal, hfirstTerminal⟩ hfirst
    let directs : Fin (first + 1) ↪ Direct :=
      ⟨fun i => advance^[i.1] start, horbitInjective⟩
    exact canonicalStableRawComponentDirectBlock_add_terminalRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (first + 1) (by omega) directs terminal
  · obtain ⟨directs⟩ := hdirects
    exact canonicalStableRawComponentDirectBlock_add_terminalRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component
        size hsize directs available






theorem
    exists_canonicalStableRawComponentDirect_terminal_or_sourceStrictBlock_or_lowerRankEntry
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    let Direct := CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let Token := CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let advance := canonicalStableRawComponentDirectForestAdvance
      ends m j k l zero hloop hjk hkl hk0 p hno component
    (∃ n ≤ Nat.card Direct,
      ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ =
          Sum.inr terminal) ∨
      ∃ size : Nat, 0 < size ∧
        ∃ directs : Fin size ↪ Direct,
          Nonempty (Fin (size + 1) ↪ Token) ∨
            ∃ i,
              anchor.1.2.1.target = (directs i).1.target ∧
              canonicalStableRawSourceRank ends m j k l zero p
                  anchor.1.2.1.source <
                canonicalStableRawSourceRank ends m j k l zero p
                  (directs i).1.source ∧
              ∀ old : StatMech.FrontierA.crossCollision
                  (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
                    ends m j k l zero hloop hjk hkl hk0 p hno component)
                  (canonicalStableRawComponentDirectEmbedding
                    ends m j k l zero hloop hjk hkl hk0 p hno component),
                directs i ≠ old.1.2 := by
  classical
  dsimp only
  rcases exists_canonicalStableRawComponentDirect_terminal_or_balancedBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component start with
    hterminal | ⟨size, hsize, ⟨directs⟩, _htokens⟩
  · exact Or.inl hterminal
  · right
    refine ⟨size, hsize, directs, ?_⟩
    exact canonicalStableRawComponentSourceCompanion_strictBlock_or_lowerRankEntry
      ends m j k l zero hloop hjk hkl hk0 p hno component anchor size
        directs






theorem
    canonicalStableRawComponentSecondAlternatePreferredSelfOutput_orbitDischarge
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hpreferredSelf :
      (canonicalStableRawComponentSecondAlternateTarget
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1 =
        canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
          ⟨canonicalStableRawPreferredRightBase ends m j k l zero
              hloop hjk hkl hk0 p
                (canonicalStableRawComponentSecondAlternateTarget
                  ends m j k l zero hloop hjk hkl hk0 p hno component anchor),
            canonicalStableRawPreferredRightBase_mem ends m j k l zero
              hloop hjk hkl hk0 p
                (canonicalStableRawComponentSecondAlternateTarget
                  ends m j k l zero hloop hjk hkl hk0 p hno component anchor)⟩) :
    (exists self : CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          self.1.target = canonicalStableRawComponentSecondAlternateTarget
            ends m j k l zero hloop hjk hkl hk0 p hno component anchor ∧
          canonicalStableRawComponentReferenceStepEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component self =
            Sum.inr terminal) ∨
      (exists self : CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ direct : CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          self.1.target = canonicalStableRawComponentSecondAlternateTarget
            ends m j k l zero hloop hjk hkl hk0 p hno component anchor ∧
          canonicalStableRawComponentReferenceStepEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component self =
            Sum.inl direct ∧
          canonicalStableRawSourceRank ends m j k l zero p direct.1.source <
            canonicalStableRawSourceRank ends m j k l zero p self.1.source) ∨
      ∃ start : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        start.1.target = canonicalStableRawComponentSecondAlternateTarget
          ends m j k l zero hloop hjk hkl hk0 p hno component anchor ∧
        (CanonicalStableRawOwnerStableOutput
            ends m j k l zero hloop hjk hkl hk0 p anchor.1.2.1 start.1 ∨
          CanonicalStableRawOwnerAdvancingOutput
            ends m j k l zero hloop hjk hkl hk0 p anchor.1.2.1 start.1) ∧
        (let Direct := CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component
         let Token := CanonicalStableRawComponentToken
            ends m j k l zero hloop hjk hkl hk0 p hno component
         let advance := canonicalStableRawComponentDirectForestAdvance
            ends m j k l zero hloop hjk hkl hk0 p hno component
         (∃ n ≤ Nat.card Direct,
            ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
                ends m j k l zero hloop hjk hkl hk0 p hno component,
              canonicalStableRawComponentForestStep
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ =
                Sum.inr terminal) ∨
           ∃ size : Nat, 0 < size ∧
             ∃ directs : Fin size ↪ Direct,
               Nonempty (Fin (size + 1) ↪ Token) ∨
                 ∃ i,
                   anchor.1.2.1.target = (directs i).1.target ∧
                   canonicalStableRawSourceRank ends m j k l zero p
                       anchor.1.2.1.source <
                     canonicalStableRawSourceRank ends m j k l zero p
                       (directs i).1.source ∧
                   ∀ old : StatMech.FrontierA.crossCollision
                       (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
                         ends m j k l zero hloop hjk hkl hk0 p hno component)
                       (canonicalStableRawComponentDirectEmbedding
                         ends m j k l zero hloop hjk hkl hk0 p hno component),
                     directs i ≠ old.1.2) := by
  rcases canonicalStableRawComponentSecondAlternatePreferredSelfOutput_stepSplit
      ends m j k l zero hloop hjk hkl hk0 p hno component anchor
        hpreferredSelf with
    hterminal | hrank | ⟨start, htarget, hkind, _⟩
  · exact Or.inl hterminal
  · exact Or.inr (Or.inl hrank)
  · exact Or.inr (Or.inr ⟨start, htarget, hkind,
      exists_canonicalStableRawComponentDirect_terminal_or_sourceStrictBlock_or_lowerRankEntry
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor start⟩)




theorem
    canonicalStableRawComponentSecondAlternatePreferredSelfOutput_strictDischarge
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hpreferredSelf :
      (canonicalStableRawComponentSecondAlternateTarget
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1 =
        canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
          ⟨canonicalStableRawPreferredRightBase ends m j k l zero
              hloop hjk hkl hk0 p
                (canonicalStableRawComponentSecondAlternateTarget
                  ends m j k l zero hloop hjk hkl hk0 p hno component anchor),
            canonicalStableRawPreferredRightBase_mem ends m j k l zero
              hloop hjk hkl hk0 p
                (canonicalStableRawComponentSecondAlternateTarget
                  ends m j k l zero hloop hjk hkl hk0 p hno component anchor)⟩) :
    (exists self : CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          self.1.target = canonicalStableRawComponentSecondAlternateTarget
            ends m j k l zero hloop hjk hkl hk0 p hno component anchor ∧
          canonicalStableRawComponentReferenceStepEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component self =
            Sum.inr terminal) ∨
      (exists self : CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ direct : CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          self.1.target = canonicalStableRawComponentSecondAlternateTarget
            ends m j k l zero hloop hjk hkl hk0 p hno component anchor ∧
          canonicalStableRawComponentReferenceStepEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component self =
            Sum.inl direct ∧
          canonicalStableRawSourceRank ends m j k l zero p direct.1.source <
            canonicalStableRawSourceRank ends m j k l zero p self.1.source) ∨
      ∃ start : CanonicalStableRawComponentPreferredDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        start.1.1.target = canonicalStableRawComponentSecondAlternateTarget
          ends m j k l zero hloop hjk hkl hk0 p hno component anchor ∧
        (CanonicalStableRawOwnerStableOutput
            ends m j k l zero hloop hjk hkl hk0 p anchor.1.2.1 start.1.1 ∨
          CanonicalStableRawOwnerAdvancingOutput
            ends m j k l zero hloop hjk hkl hk0 p anchor.1.2.1 start.1.1) ∧
        (let Preferred := CanonicalStableRawComponentPreferredDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component
         let Direct := CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component
         let Token := CanonicalStableRawComponentToken
            ends m j k l zero hloop hjk hkl hk0 p hno component
         let step := canonicalStableRawComponentPreferredDirectStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
         let advance := partialForestAdvance step
         (∃ n ≤ Nat.card Preferred,
            ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
                ends m j k l zero hloop hjk hkl hk0 p hno component,
              step (advance^[n] start) = Sum.inr terminal) ∨
           ∃ size : Nat, 0 < size ∧
             Nonempty (Fin size ↪ Direct) ∧
             Nonempty (Fin (size + 1) ↪ Token)) := by
  rcases canonicalStableRawComponentSecondAlternatePreferredSelfOutput_stepSplit
      ends m j k l zero hloop hjk hkl hk0 p hno component anchor
        hpreferredSelf with
    hterminal | hrank | ⟨start, htarget, hkind, _⟩
  · exact Or.inl hterminal
  · exact Or.inr (Or.inl hrank)
  · have hstartPreferred : start.1.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p
          ⟨canonicalStableRawPreferredRightBase ends m j k l zero
              hloop hjk hkl hk0 p start.1.target,
            canonicalStableRawPreferredRightBase_mem ends m j k l zero
              hloop hjk hkl hk0 p start.1.target⟩ := by
      rw [htarget]
      exact hpreferredSelf
    let preferredStart : CanonicalStableRawComponentPreferredDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨start, hstartPreferred⟩
    exact Or.inr (Or.inr ⟨preferredStart, htarget, hkind,
      exists_canonicalStableRawComponentPreferredDirect_terminal_or_strictTokenBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor
          preferredStart⟩)





theorem
    exists_canonicalStableRawComponentResidualLower_terminal_or_strictTokenBlock_of_freeFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (residual : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hfree : (canonicalStableRawComponentSecondAlternateTarget
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1 ≠
      canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p
          ⟨canonicalStableRawPreferredRightBase ends m j k l zero
              hloop hjk hkl hk0 p
                (canonicalStableRawComponentSecondAlternateTarget
                  ends m j k l zero hloop hjk hkl hk0 p hno component anchor),
            canonicalStableRawPreferredRightBase_mem ends m j k l zero
              hloop hjk hkl hk0 p
                (canonicalStableRawComponentSecondAlternateTarget
                  ends m j k l zero hloop hjk hkl hk0 p hno component anchor)⟩) :
    let Direct := CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let Token := CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let advance := canonicalStableRawComponentDirectForestAdvance
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let lower : Direct := residual.1.1.1.2
    (∃ n ≤ Nat.card Direct,
      ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨(advance^[n] lower).1, (advance^[n] lower).2.1⟩ =
          Sum.inr terminal) ∨
      ∃ size : Nat, 0 < size ∧
        Nonempty (Fin size ↪ Direct) ∧
        Nonempty (Fin (size + 1) ↪ Token) := by
  classical
  dsimp only
  obtain ⟨available, _havailableTarget⟩ :=
    exists_canonicalStableRawComponentSecondAlternateFiber_freeTerminal
      ends m j k l zero hloop hjk hkl hk0 p hno component anchor hfree
  exact exists_canonicalStableRawComponentDirect_terminal_or_strictTokenBlock
    ends m j k l zero hloop hjk hkl hk0 p hno component
      residual.1.1.1.2 available




theorem exists_canonicalStableRawComponentResidualCollision_of_deficit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    Nonempty (StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) := by
  by_contra hnone
  have hdisjoint : ∀ collision direct,
      canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision ≠
        canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component direct := by
    intro collision direct heq
    exact hnone ⟨⟨(collision, direct), heq⟩⟩
  obtain ⟨embedding⟩ :=
    canonicalStableRawTokenComponent_embedding_of_sourceDirectDisjoint
      ends m j k l zero hloop hjk hkl hk0 p hno component hdisjoint
  exact (Nat.not_lt_of_ge
    (Fintype.card_le_of_injective embedding embedding.injective)) hdeficit




theorem
    exists_canonicalStableRawComponentResidualLower_fresh_or_rightCollision_of_deficit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ collision : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component),
      collision.1.1.1.2.1.target = collision.1.2.1.target ∧
      canonicalStableRawSourceRank ends m j k l zero p
          collision.1.1.1.2.1.source <
        canonicalStableRawSourceRank ends m j k l zero p
          collision.1.2.1.source ∧
      (let lower := collision.1.1.1.2
       (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          canonicalStableRawComponentForestStep
              ends m j k l zero hloop hjk hkl hk0 p hno component
                ⟨lower.1, lower.2.1⟩ = Sum.inr terminal ∧
          ∀ direct : CanonicalStableRawComponentDirectState
              ends m j k l zero hloop hjk hkl hk0 p hno component,
            terminal.1 ≠ canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component direct) ∨
        ∃ continuation : CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          canonicalStableRawComponentForestStep
              ends m j k l zero hloop hjk hkl hk0 p hno component
                ⟨lower.1, lower.2.1⟩ = Sum.inl continuation ∧
          canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component
                continuation =
            canonicalStableRawComponentSuccessorToken
              ends m j k l zero hloop hjk hkl hk0 p hno component
                ⟨lower.1, lower.2.1⟩) := by
  obtain ⟨collision⟩ :=
    exists_canonicalStableRawComponentResidualCollision_of_deficit
      ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit
  have hranked := canonicalStableRawComponentResidualCollision_ranked_sameTarget
    ends m j k l zero hloop hjk hkl hk0 p hno component collision
  exact ⟨collision, hranked.1, hranked.2,
    canonicalStableRawComponentResidualLower_fresh_or_rightCollision
      ends m j k l zero hloop hjk hkl hk0 p hno component collision⟩



theorem exists_canonicalStableRawComponent_minRankResidualCollision_of_deficit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ collision : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component),
      ∀ other : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentReferenceSourceCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        canonicalStableRawSourceRank ends m j k l zero p
            collision.1.2.1.source ≤
          canonicalStableRawSourceRank ends m j k l zero p
            other.1.2.1.source := by
  classical
  let sourceMap := canonicalStableRawComponentReferenceSourceCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Residual := StatMech.FrontierA.crossCollision sourceMap directMap
  let rank := fun collision : Residual =>
    canonicalStableRawSourceRank ends m j k l zero p
      collision.1.2.1.source
  letI : Fintype Residual := Fintype.ofInjective
    (fun collision => collision.1.2)
    (StatMech.FrontierA.crossCollision_snd_injective sourceMap directMap)
  obtain ⟨collision⟩ :=
    exists_canonicalStableRawComponentResidualCollision_of_deficit
      ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit
  have huniv : (Finset.univ : Finset Residual).Nonempty :=
    ⟨collision, Finset.mem_univ collision⟩
  have hranks : (Finset.univ.image rank).Nonempty := huniv.image rank
  let minimum := (Finset.univ.image rank).min' hranks
  have hminimum : minimum ∈ Finset.univ.image rank := Finset.min'_mem _ _
  obtain ⟨chosen, _, hchosen⟩ := Finset.mem_image.mp hminimum
  refine ⟨chosen, ?_⟩
  intro other
  change rank chosen ≤ rank other
  rw [hchosen]
  exact Finset.min'_le _ _
    (Finset.mem_image.mpr ⟨other, Finset.mem_univ other, rfl⟩)





noncomputable def canonicalStableRawComponentResidualDirectPairEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (A : Finset (StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))) :
    (↑A ⊕ ↑A) ↪ CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component := by
  let first := canonicalStableRawComponentReferenceOwnerCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let sourceMap := canonicalStableRawComponentReferenceSourceCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let unused :=
    canonicalStableRawReferenceSourceDirectCollisionToUnusedDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component
  let f : ↑A ⊕ ↑A → CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component
    | Sum.inl collision => collision.1.1.1.1.2
    | Sum.inr collision => collision.1.1.2
  refine ⟨f, ?_⟩
  intro x y hxy
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          change x.1.1.1.1.2 = y.1.1.1.1.2 at hxy
          have hfirst : x.1.1.1 = y.1.1.1 :=
            StatMech.FrontierA.crossCollision_snd_injective
              first directMap hxy
          have hresidual : x.1 = y.1 :=
            StatMech.FrontierA.crossCollision_fst_injective
              sourceMap directMap hfirst
          exact congrArg Sum.inl (Subtype.ext hresidual)
      | inr y =>
          exfalso
          change x.1.1.1.1.2 = y.1.1.2 at hxy
          exact (unused y.1).2 x.1.1.1 hxy.symm
  | inr x =>
      cases y with
      | inl y =>
          exfalso
          change x.1.1.2 = y.1.1.1.1.2 at hxy
          exact (unused x.1).2 y.1.1.1 hxy
      | inr y =>
          change x.1.1.2 = y.1.1.2 at hxy
          have hresidual : x.1 = y.1 :=
            StatMech.FrontierA.crossCollision_snd_injective
              sourceMap directMap hxy
          exact congrArg Sum.inr (Subtype.ext hresidual)


theorem canonicalStableRawComponentResidualDirectPair_card_le
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (A : Finset (StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))) :
    2 * A.card ≤ Nat.card (CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  let embedding := canonicalStableRawComponentResidualDirectPairEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component A
  letI : Fintype (CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :=
    Fintype.ofFinite _
  have hcard := Fintype.card_le_of_injective embedding embedding.injective
  simpa only [Fintype.card_sum, Fintype.card_coe,
    Nat.card_eq_fintype_card, two_mul] using hcard





theorem
    exists_canonicalStableRawComponentResidualOrbitDischarge_of_deficit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    let Direct := CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let Token := CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let advance := canonicalStableRawComponentDirectForestAdvance
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let rank := fun direct : Direct =>
      canonicalStableRawSourceRank ends m j k l zero p direct.1.source
    ∃ collision : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component),
      collision.1.1.1.2.1.target = collision.1.2.1.target ∧
      rank collision.1.1.1.2 < rank collision.1.2 ∧
      ((∃ n ≤ Nat.card Direct,
          ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
              ends m j k l zero hloop hjk hkl hk0 p hno component,
            canonicalStableRawComponentForestStep
                ends m j k l zero hloop hjk hkl hk0 p hno component
                  ⟨(advance^[n] collision.1.2).1,
                    (advance^[n] collision.1.2).2.1⟩ = Sum.inr terminal) ∨
        (∃ n < Nat.card Direct, ∃ continuation : Direct,
          canonicalStableRawComponentForestStep
              ends m j k l zero hloop hjk hkl hk0 p hno component
                ⟨(advance^[n] collision.1.2).1,
                  (advance^[n] collision.1.2).2.1⟩ = Sum.inl continuation ∧
            rank continuation < rank (advance^[n] collision.1.2)) ∨
        ∃ size : Nat, 0 < size ∧
          Nonempty (Fin size ↪ Direct) ∧
          Nonempty (Fin size ↪ Token)) := by
  classical
  dsimp only
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Token := CanonicalStableRawComponentToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let advance := canonicalStableRawComponentDirectForestAdvance
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let rank := fun direct : Direct =>
    canonicalStableRawSourceRank ends m j k l zero p direct.1.source
  obtain ⟨collision⟩ :=
    exists_canonicalStableRawComponentResidualCollision_of_deficit
      ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit
  have hranked := canonicalStableRawComponentResidualCollision_ranked_sameTarget
    ends m j k l zero hloop hjk hkl hk0 p hno component collision
  refine ⟨collision, hranked.1, hranked.2, ?_⟩
  rcases
      exists_canonicalStableRawComponentDirect_terminal_or_rankDrop_or_balancedBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component
          collision.1.2 with
    hterminal | hdrop | hpair | hcycle
  · exact Or.inl hterminal
  · exact Or.inr (Or.inl hdrop)
  · exact Or.inr (Or.inr ⟨2, by omega, hpair.1, hpair.2⟩)
  · dsimp only at hcycle
    obtain ⟨startIndex, stopIndex, first, stop, _hlt, _hbound,
      _hrepeat, _hallNext, hfirstStop, _hstopLength, _hstate,
      _hdistinct, _howners, hdirects, htokens⟩ := hcycle
    exact Or.inr (Or.inr
      ⟨stop - first, by omega, hdirects, htokens⟩)




theorem
    exists_canonicalStableRawComponentResidual_terminal_or_balancedBlock_of_deficit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    let Direct := CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let Token := CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let advance := canonicalStableRawComponentDirectForestAdvance
      ends m j k l zero hloop hjk hkl hk0 p hno component
    ∃ collision : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component),
      collision.1.1.1.2.1.target = collision.1.2.1.target ∧
      canonicalStableRawSourceRank ends m j k l zero p
          collision.1.1.1.2.1.source <
        canonicalStableRawSourceRank ends m j k l zero p
          collision.1.2.1.source ∧
      ((∃ n ≤ Nat.card Direct,
          ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
              ends m j k l zero hloop hjk hkl hk0 p hno component,
            canonicalStableRawComponentForestStep
                ends m j k l zero hloop hjk hkl hk0 p hno component
                  ⟨(advance^[n] collision.1.2).1,
                    (advance^[n] collision.1.2).2.1⟩ = Sum.inr terminal) ∨
        ∃ size : Nat, 0 < size ∧
          Nonempty (Fin size ↪ Direct) ∧
          Nonempty (Fin size ↪ Token)) := by
  classical
  dsimp only
  obtain ⟨collision⟩ :=
    exists_canonicalStableRawComponentResidualCollision_of_deficit
      ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit
  have hranked := canonicalStableRawComponentResidualCollision_ranked_sameTarget
    ends m j k l zero hloop hjk hkl hk0 p hno component collision
  refine ⟨collision, hranked.1, hranked.2, ?_⟩
  exact exists_canonicalStableRawComponentDirect_terminal_or_balancedBlock
    ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.2






theorem
    exists_canonicalStableRawComponent_terminalFresh_or_reducedDeficit_of_deficit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    let Self := CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let Direct := CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let Token := CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let advance := canonicalStableRawComponentDirectForestAdvance
      ends m j k l zero hloop hjk hkl hk0 p hno component
    ∃ collision : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component),
      collision.1.1.1.2.1.target = collision.1.2.1.target ∧
      canonicalStableRawSourceRank ends m j k l zero p
          collision.1.1.1.2.1.source <
        canonicalStableRawSourceRank ends m j k l zero p
          collision.1.2.1.source ∧
      ((∃ n ≤ Nat.card Direct,
          ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
              ends m j k l zero hloop hjk hkl hk0 p hno component,
            canonicalStableRawComponentForestStep
                ends m j k l zero hloop hjk hkl hk0 p hno component
                  ⟨(advance^[n] collision.1.2).1,
                    (advance^[n] collision.1.2).2.1⟩ = Sum.inr terminal ∧
            ∀ direct : Direct,
              terminal.1 ≠ canonicalStableRawComponentDirectEmbedding
                ends m j k l zero hloop hjk hkl hk0 p hno component direct) ∨
        ∃ size : Nat, 0 < size ∧
          Nonempty (Fin size ↪ Direct) ∧
          Nonempty (Fin size ↪ Token) ∧
          Nat.card Token - size <
            Nat.card Self + (Nat.card Direct - size)) := by
  classical
  dsimp only
  let Self := CanonicalStableRawComponentSelfState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let State := CanonicalStableRawComponentState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Token := CanonicalStableRawComponentToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  have hstate : Nat.card State = Nat.card Self + Nat.card Direct := by
    let split : State → Self ⊕ Direct := fun state =>
      if hself : state.1.target.1 = canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p state.1.source then
        Sum.inl ⟨state.1, state.2, hself⟩
      else
        Sum.inr ⟨state.1, state.2, hself⟩
    let recover : Self ⊕ Direct → State
      | Sum.inl state => ⟨state.1, state.2.1⟩
      | Sum.inr state => ⟨state.1, state.2.1⟩
    let partition : State ≃ Self ⊕ Direct := by
      refine ⟨split, recover, ?_, ?_⟩
      · intro state
        by_cases hself : state.1.target.1 = canonicalStableRawSelfBase
            ends m j k l zero hloop hjk hkl hk0 p state.1.source
        · simp [split, recover, hself]
        · simp [split, recover, hself]
      · intro state
        cases state with
        | inl state => simp [split, recover, state.2.2]
        | inr state => simp [split, recover, state.2.2]
    simpa only [Nat.card_sum] using Nat.card_congr partition
  have hdeficitNat : Nat.card Token < Nat.card Self + Nat.card Direct := by
    have hraw : Nat.card Token < Nat.card State := by
      simpa only [Nat.card_eq_fintype_card] using hdeficit
    omega
  obtain ⟨collision, htarget, hrank, horbit⟩ :=
    exists_canonicalStableRawComponentResidual_terminal_or_balancedBlock_of_deficit
      ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit
  refine ⟨collision, htarget, hrank, ?_⟩
  rcases horbit with hterminal | hblock
  · left
    obtain ⟨n, hn, terminal, hstep⟩ := hterminal
    exact ⟨n, hn, terminal, hstep, fun direct =>
      canonicalStableRawComponentNonexceptionalToken_ne_direct
        ends m j k l zero hloop hjk hkl hk0 p hno component
          terminal direct⟩
  · right
    obtain ⟨size, hsize, hdirects, htokens⟩ := hblock
    refine ⟨size, hsize, hdirects, htokens, ?_⟩
    exact strictDeficit_sub_balancedEmbeddings size hdeficitNat
      hdirects htokens





theorem canonicalStableRawComponent_minResidual_terminal_or_balancedBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hminimal : ∀ other : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component),
      canonicalStableRawSourceRank ends m j k l zero p
          collision.1.2.1.source ≤
        canonicalStableRawSourceRank ends m j k l zero p
          other.1.2.1.source)
    (horbitBound : ∀ n,
      canonicalStableRawSourceRank ends m j k l zero p
          ((canonicalStableRawComponentDirectForestAdvance
            ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
              collision.1.2).1.source ≤
        canonicalStableRawSourceRank ends m j k l zero p
          collision.1.2.1.source)
    (hresidual : ∀ n continuation,
      canonicalStableRawComponentForestStep
          ends m j k l zero hloop hjk hkl hk0 p hno component
            ⟨((canonicalStableRawComponentDirectForestAdvance
                  ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                collision.1.2).1,
              ((canonicalStableRawComponentDirectForestAdvance
                  ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                collision.1.2).2.1⟩ = Sum.inl continuation ->
      ∃ other : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentReferenceSourceCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        other.1.2 = continuation) :
    let Direct := CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let Token := CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let advance := canonicalStableRawComponentDirectForestAdvance
      ends m j k l zero hloop hjk hkl hk0 p hno component
    (∃ n ≤ Nat.card Direct,
      ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨(advance^[n] collision.1.2).1,
                (advance^[n] collision.1.2).2.1⟩ = Sum.inr terminal) ∨
      ∃ size : Nat, 0 < size ∧
        Nonempty (Fin size ↪ Direct) ∧
        Nonempty (Fin size ↪ Token) := by
  classical
  dsimp only
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Token := CanonicalStableRawComponentToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let advance := canonicalStableRawComponentDirectForestAdvance
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let rank := fun direct : Direct =>
    canonicalStableRawSourceRank ends m j k l zero p direct.1.source
  rcases
      exists_canonicalStableRawComponentDirect_terminal_or_rankDrop_or_balancedBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component
          collision.1.2 with
    hterminal | hdrop | hpair | hcycle
  · exact Or.inl hterminal
  · obtain ⟨n, _hn, continuation, hstep, hrank⟩ := hdrop
    obtain ⟨other, hother⟩ := hresidual n continuation hstep
    have hmin : rank collision.1.2 ≤ rank continuation := by
      change canonicalStableRawSourceRank ends m j k l zero p
          collision.1.2.1.source ≤
        canonicalStableRawSourceRank ends m j k l zero p
          continuation.1.source
      rw [← hother]
      exact hminimal other
    have hbound : rank (advance^[n] collision.1.2) ≤
        rank collision.1.2 := by
      exact horbitBound n
    have hnotDrop : ¬ rank continuation <
        rank (advance^[n] collision.1.2) :=
      Nat.not_lt_of_ge (hbound.trans hmin)
    exact False.elim (hnotDrop hrank)
  · exact Or.inr ⟨2, by omega, hpair.1, hpair.2⟩
  · dsimp only at hcycle
    obtain ⟨startIndex, stopIndex, first, stop, _hlt, _hcard,
      _hrepeat, _hallNext, hfirstStop, _hstopLength, _hstate,
      _hdistinct, _howners, hdirects, htokens⟩ := hcycle
    exact Or.inr ⟨stop - first, by omega, hdirects, htokens⟩


noncomputable def canonicalStableRawComponentReferenceImmediateTerminals
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Finset (CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  exact Finset.univ.filter fun terminal =>
    canonicalStableRawComponentReferenceStepEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component self =
        Sum.inr terminal



noncomputable def canonicalStableRawComponentReferenceChildren
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Finset (CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  let Self := CanonicalStableRawComponentSelfState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  letI : Fintype Self := Fintype.ofFinite Self
  exact Finset.univ.filter fun child =>
    ∃ direct : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      canonicalStableRawComponentReferenceStepEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component self =
        Sum.inl direct ∧
      ∃ collision : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        collision.1.1 = child ∧ collision.1.2 = direct

theorem canonicalStableRawComponentReferenceChildren_rank_lt
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self child : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hchild : child ∈ canonicalStableRawComponentReferenceChildren
      ends m j k l zero hloop hjk hkl hk0 p hno component self) :
    canonicalStableRawComponentSelfRank
        ends m j k l zero hloop hjk hkl hk0 p hno component child <
      canonicalStableRawComponentSelfRank
        ends m j k l zero hloop hjk hkl hk0 p hno component self := by
  classical
  unfold canonicalStableRawComponentReferenceChildren at hchild
  obtain ⟨direct, hstep, collision, hcollisionSelf, hcollisionDirect⟩ :=
    (Finset.mem_filter.mp hchild).2
  have hrank :=
    canonicalStableRawComponentReferenceStepEmbedding_inl_rank_lt
      ends m j k l zero hloop hjk hkl hk0 p hno component
        self direct hstep
  have hsource := canonicalStableRawComponentCrossCollision_source_eq_direct
    ends m j k l zero hloop hjk hkl hk0 p hno component collision
  unfold canonicalStableRawComponentSelfRank
  rw [← hcollisionSelf, hsource, hcollisionDirect]
  exact hrank



noncomputable def canonicalStableRawComponentReferenceTerminalSystem
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    FiniteRankTerminalSystem
      (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) where
  rank := canonicalStableRawComponentSelfRank
    ends m j k l zero hloop hjk hkl hk0 p hno component
  terminals := canonicalStableRawComponentReferenceImmediateTerminals
    ends m j k l zero hloop hjk hkl hk0 p hno component
  children := canonicalStableRawComponentReferenceChildren
    ends m j k l zero hloop hjk hkl hk0 p hno component
  children_rank_lt := canonicalStableRawComponentReferenceChildren_rank_lt
    ends m j k l zero hloop hjk hkl hk0 p hno component


noncomputable def canonicalStableRawComponentReferenceTerminalNeighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    Finset (CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  exact sources.biUnion
    (canonicalStableRawComponentReferenceTerminalSystem
      ends m j k l zero hloop hjk hkl hk0 p hno component
        |>.terminalClosure)


noncomputable def canonicalStableRawComponentReferenceTerminalClosure
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Finset (CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  exact (canonicalStableRawComponentReferenceTerminalSystem
    ends m j k l zero hloop hjk hkl hk0 p hno component).terminalClosure self

theorem canonicalStableRawComponentReferenceTerminal_mem_of_step_inr
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (terminal : CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstep : canonicalStableRawComponentReferenceStepEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component self =
      Sum.inr terminal) :
    terminal ∈ canonicalStableRawComponentReferenceTerminalClosure
      ends m j k l zero hloop hjk hkl hk0 p hno component self := by
  classical
  unfold canonicalStableRawComponentReferenceTerminalClosure
  apply FiniteRankTerminalSystem.terminals_subset_terminalClosure
    (canonicalStableRawComponentReferenceTerminalSystem
      ends m j k l zero hloop hjk hkl hk0 p hno component) self
  unfold canonicalStableRawComponentReferenceTerminalSystem
    canonicalStableRawComponentReferenceImmediateTerminals
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hstep⟩

theorem canonicalStableRawComponentReferenceChild_terminalClosure_subset
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self child : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hchild : child ∈ canonicalStableRawComponentReferenceChildren
      ends m j k l zero hloop hjk hkl hk0 p hno component self) :
    canonicalStableRawComponentReferenceTerminalClosure
        ends m j k l zero hloop hjk hkl hk0 p hno component child ⊆
      canonicalStableRawComponentReferenceTerminalClosure
        ends m j k l zero hloop hjk hkl hk0 p hno component self := by
  classical
  unfold canonicalStableRawComponentReferenceTerminalClosure
  exact FiniteRankTerminalSystem.terminalClosure_subset_of_mem_children
    (canonicalStableRawComponentReferenceTerminalSystem
      ends m j k l zero hloop hjk hkl hk0 p hno component) hchild




theorem canonicalStableRawTokenComponent_embedding_of_forestStepInjective
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hinjective : Function.Injective
      (canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    Nonempty (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  let forest : CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      (CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
        CanonicalStableRawComponentNonexceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component) :=
    ⟨canonicalStableRawComponentForestStep
      ends m j k l zero hloop hjk hkl hk0 p hno component, hinjective⟩
  exact ⟨forest.trans
    (canonicalStableRawComponentDirectSumNonexceptionalEquivToken
      ends m j k l zero hloop hjk hkl hk0 p hno component).toEmbedding⟩


noncomputable def canonicalStableRawComponentStateEquivSelfSumDirect
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component ≃
      CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
        CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component := by
  classical
  let split : CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component →
      CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
        CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component := fun s =>
    if hself : s.1.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p s.1.source then
      Sum.inl ⟨s.1, s.2, hself⟩
    else
      Sum.inr ⟨s.1, s.2, hself⟩
  let recover :
      CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
        CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component →
      CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component
    | Sum.inl s => ⟨s.1, s.2.1⟩
    | Sum.inr s => ⟨s.1, s.2.1⟩
  refine ⟨split, recover, ?_, ?_⟩
  · intro s
    by_cases hself : s.1.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p s.1.source
    · simp [split, recover, hself]
    · simp [split, recover, hself]
  · intro s
    cases s with
    | inl s => simp [split, recover, s.2.2]
    | inr s => simp [split, recover, s.2.2]




theorem canonicalStableRawComponent_cardLE_iff_self_le_nonexceptional
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    Fintype.card (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component) ≤
      Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) ↔
      Nat.card (CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component) ≤
        Nat.card (CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  let exceptional := fun token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component =>
    CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p token.1
  have hstate := Nat.card_congr
    (canonicalStableRawComponentStateEquivSelfSumDirect
      ends m j k l zero hloop hjk hkl hk0 p hno component)
  have hdirect := Nat.card_congr
    (canonicalStableRawComponentDirectStateEquivExceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
  have htoken := (Nat.card_congr (Equiv.sumCompl exceptional)).symm
  simp only [Nat.card_sum] at hstate htoken
  change _ = Nat.card (CanonicalStableRawComponentExceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) +
    Nat.card (CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) at htoken
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  omega



theorem canonicalStableRawTokenComponent_embedding_of_direct_card_le_self
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hdirectSelf : Nat.card (CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component) ≤
      Nat.card (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    Nonempty (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Self := CanonicalStableRawComponentSelfState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Terminal := CanonicalStableRawComponentNonexceptionalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Token := CanonicalStableRawComponentToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  have hdirectSelf' : Nat.card Direct ≤ Nat.card Self := by
    simpa only [Direct, Self] using hdirectSelf
  have hpair : 2 * Nat.card Self ≤ Nat.card Token :=
    canonicalStableRawComponent_two_mul_self_card_le_token
      ends m j k l zero hloop hjk hkl hk0 p hno component
  have htoken : Nat.card Direct + Nat.card Terminal = Nat.card Token := by
    simpa only [Nat.card_sum] using Nat.card_congr
      (canonicalStableRawComponentDirectSumNonexceptionalEquivToken
        ends m j k l zero hloop hjk hkl hk0 p hno component)
  have hselfTerminal : Nat.card Self ≤ Nat.card Terminal := by
    omega
  apply Function.Embedding.nonempty_of_card_le
  exact (canonicalStableRawComponent_cardLE_iff_self_le_nonexceptional
    ends m j k l zero hloop hjk hkl hk0 p hno component).2 hselfTerminal



theorem canonicalStableRawComponent_direct_card_gt_self_of_deficit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    Nat.card (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component) <
      Nat.card (CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  by_contra hnot
  have hdirectSelf : Nat.card (CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component) ≤
      Nat.card (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component) :=
    Nat.le_of_not_gt hnot
  obtain ⟨embedding⟩ :=
    canonicalStableRawTokenComponent_embedding_of_direct_card_le_self
      ends m j k l zero hloop hjk hkl hk0 p hno component hdirectSelf
  exact (Nat.not_lt_of_ge
    (Fintype.card_le_of_injective embedding embedding.injective)) hdeficit




theorem canonicalStableRawTokenComponent_embedding_of_selfNonexceptionalEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (forest : CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component ↪
        CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Nonempty (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  apply Function.Embedding.nonempty_of_card_le
  apply (canonicalStableRawComponent_cardLE_iff_self_le_nonexceptional
    ends m j k l zero hloop hjk hkl hk0 p hno component).2
  exact Nat.card_le_card_of_injective forest forest.injective



theorem canonicalStableRawTokenComponent_embedding_of_terminalClosureHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hhall : ∀ sources : Finset (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      sources.card ≤ (canonicalStableRawComponentTerminalNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card) :
    Nonempty (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  obtain ⟨matching, _⟩ :=
    FiniteRankTerminalSystem.exists_terminalEmbedding_of_hall
      (canonicalStableRawComponentTerminalSystem
        ends m j k l zero hloop hjk hkl hk0 p hno component) (by
          intro sources
          simpa only [canonicalStableRawComponentTerminalNeighborhood] using
            hhall sources)
  exact canonicalStableRawTokenComponent_embedding_of_selfNonexceptionalEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component matching



theorem canonicalStableRawTokenComponent_embedding_of_referenceTerminalHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hhall : ∀ sources : Finset (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      sources.card ≤
        (canonicalStableRawComponentReferenceTerminalNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            sources).card) :
    Nonempty (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  obtain ⟨matching, _⟩ :=
    FiniteRankTerminalSystem.exists_terminalEmbedding_of_hall
      (canonicalStableRawComponentReferenceTerminalSystem
        ends m j k l zero hloop hjk hkl hk0 p hno component) (by
          intro sources
          simpa only [canonicalStableRawComponentReferenceTerminalNeighborhood]
            using hhall sources)
  exact canonicalStableRawTokenComponent_embedding_of_selfNonexceptionalEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component matching



noncomputable def canonicalStableRawComponentIncidentNeighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    Finset (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  exact Finset.univ.filter fun token => ∃ source ∈ sources,
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component source token

theorem canonicalStableRawComponentIncidentNeighborhood_mono
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    Monotone (canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  intro smaller larger hsubset token htoken
  obtain ⟨source, hsource, hincident⟩ :=
    (Finset.mem_filter.mp htoken).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ token,
    source, hsubset hsource, hincident⟩



noncomputable def canonicalStableRawComponentRestrictedIncidentNeighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (family : Finset ↑sources) :
    Finset ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources) := by
  classical
  exact Finset.univ.filter fun token => ∃ state ∈ family,
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1



theorem canonicalStableRawComponent_tightProperHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      smaller ⊂ sources ->
        smaller.card ≤
          (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              smaller).card) :
    ∀ family : Finset ↑sources, family ⊂ Finset.univ ->
      family.card ≤
        (canonicalStableRawComponentRestrictedIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            sources family).card := by
  classical
  let TightState := ↑sources
  let total := canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  let TightToken := ↑total
  let incident : TightState -> TightToken -> Prop := fun state token =>
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1
  intro family hfamily
  let inclusion : TightState ↪ CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let raw := family.map inclusion
  have hrawSubset : raw ⊆ sources := by
    intro state hstate
    obtain ⟨tightState, _htightState, rfl⟩ := Finset.mem_map.mp hstate
    exact tightState.2
  have hrawProper : raw ⊂ sources := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hrawSubset, ?_⟩
    intro heq
    have hlt := Finset.card_lt_card hfamily
    have hrawCard : raw.card = family.card := Finset.card_map _
    have hunivCard : (Finset.univ : Finset TightState).card = sources.card := by
      simp only [Finset.card_univ, TightState, Fintype.card_coe]
    rw [← hrawCard, hunivCard, heq] at hlt
    exact Nat.lt_irrefl _ hlt
  let rawNeighborhood := canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component raw
  let tightNeighborhood : Finset TightToken :=
    canonicalStableRawComponentRestrictedIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources family
  have hrawNeighborhoodSubset : rawNeighborhood ⊆ total :=
    canonicalStableRawComponentIncidentNeighborhood_mono
      ends m j k l zero hloop hjk hkl hk0 p hno component hrawSubset
  let forward : ↑rawNeighborhood -> ↑tightNeighborhood := fun token =>
    ⟨⟨token.1, hrawNeighborhoodSubset token.2⟩, by
      have hmem := (Finset.mem_filter.mp token.2).2
      obtain ⟨source, hsource, hincident⟩ := hmem
      obtain ⟨state, hstate, hsourceEq⟩ := Finset.mem_map.mp hsource
      subst source
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, state, hstate, hincident⟩⟩
  let backward : ↑tightNeighborhood -> ↑rawNeighborhood := fun token =>
    ⟨token.1.1, by
      have hmem := (Finset.mem_filter.mp token.2).2
      obtain ⟨state, hstate, hincident⟩ := hmem
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, state.1,
        Finset.mem_map.mpr ⟨state, hstate, rfl⟩, hincident⟩⟩
  let neighborhoodEquiv : ↑rawNeighborhood ≃ ↑tightNeighborhood :=
    { toFun := forward
      invFun := backward
      left_inv := by
        intro token
        apply Subtype.ext
        rfl
      right_inv := by
        intro token
        apply Subtype.ext
        apply Subtype.ext
        rfl }
  have hneighborhoodCard : rawNeighborhood.card = tightNeighborhood.card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr neighborhoodEquiv
  have hhall := hproper raw hrawProper
  have hrawCard : raw.card = family.card := Finset.card_map _
  rw [hrawCard, hneighborhoodCard] at hhall
  simpa only [tightNeighborhood] using hhall



theorem exists_canonicalStableRawComponent_minimalIncidentObstruction_of_deficit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ sources : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      sources.Nonempty ∧
        (canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            sources).card + 1 = sources.card ∧
        (∀ source ∈ sources,
          canonicalStableRawComponentIncidentNeighborhood
              ends m j k l zero hloop hjk hkl hk0 p hno component
                (sources.erase source) =
            canonicalStableRawComponentIncidentNeighborhood
              ends m j k l zero hloop hjk hkl hk0 p hno component
                sources) ∧
        ∀ smaller : Finset (CanonicalStableRawComponentState
            ends m j k l zero hloop hjk hkl hk0 p hno component),
          smaller ⊂ sources ->
            smaller.card ≤
              (canonicalStableRawComponentIncidentNeighborhood
                ends m j k l zero hloop hjk hkl hk0 p hno component
                  smaller).card := by
  classical
  apply exists_minimal_deficiency_one_family
    (canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (canonicalStableRawComponentIncidentNeighborhood_mono
      ends m j k l zero hloop hjk hkl hk0 p hno component)
  refine ⟨Finset.univ, ?_⟩
  have hneighborhood :
      (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component
          Finset.univ).card ≤
        Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) := by
    exact Finset.card_le_univ _
  simpa only [Finset.card_univ] using hneighborhood.trans_lt hdeficit



theorem exists_other_mem_of_incident_of_delete_invariant
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : source ∈ sources)
    (herase : canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component
          (sources.erase source) =
      canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hincident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component source token) :
    ∃ other ∈ sources, other ≠ source ∧
      CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component other token := by
  classical
  have htoken : token ∈ canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ token,
      source, hsource, hincident⟩
  rw [← herase] at htoken
  obtain ⟨other, hother, hotherIncident⟩ := (Finset.mem_filter.mp htoken).2
  have hotherData := Finset.mem_erase.mp hother
  exact ⟨other, hotherData.2, hotherData.1, hotherIncident⟩




theorem exists_canonicalStableRawComponent_deleteMatching
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : source ∈ sources)
    (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      smaller ⊂ sources ->
        smaller.card ≤
          (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              smaller).card) :
    ∃ matching : ↑(sources.erase source) ↪
        CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
      ∀ remaining,
        CanonicalStableRawComponentIncident
          ends m j k l zero hloop hjk hkl hk0 p hno component
            remaining.1 (matching remaining) := by
  classical
  let Deleted := ↑(sources.erase source)
  let Token := CanonicalStableRawComponentToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let neighbors : Deleted -> Finset Token := fun remaining =>
    Finset.univ.filter fun token =>
      CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component
          remaining.1 token
  have hhall : ∀ family : Finset Deleted,
      family.card ≤ (family.biUnion neighbors).card := by
    intro family
    let inclusion : Deleted ↪
        CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨Subtype.val, Subtype.val_injective⟩
    let smaller := family.map inclusion
    have hsmallerSubset : smaller ⊆ sources := by
      intro state hstate
      obtain ⟨remaining, _hremainingFamily, hremaining⟩ :=
        Finset.mem_map.mp hstate
      rw [← hremaining]
      exact Finset.mem_of_mem_erase remaining.2
    have hsourceNot : source ∉ smaller := by
      intro hmem
      obtain ⟨remaining, _hremainingFamily, hremaining⟩ :=
        Finset.mem_map.mp hmem
      apply Finset.ne_of_mem_erase remaining.2
      exact hremaining
    have hsmallerProper : smaller ⊂ sources :=
      Finset.ssubset_iff_subset_ne.mpr
        ⟨hsmallerSubset, fun heq => hsourceNot (heq ▸ hsource)⟩
    have hcard := hproper smaller hsmallerProper
    have hfamilyCard : smaller.card = family.card := Finset.card_map _
    have hneighborhood :
        canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component smaller =
          family.biUnion neighbors := by
      ext token
      simp only [canonicalStableRawComponentIncidentNeighborhood,
        Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        smaller, Finset.mem_map]
      constructor
      · rintro ⟨state, ⟨remaining, hremaining, hstate⟩, hincident⟩
        subst state
        refine ⟨remaining, hremaining, ?_⟩
        simpa only [neighbors, Finset.mem_filter, Finset.mem_univ,
          true_and] using hincident
      · rintro ⟨remaining, hremaining, htoken⟩
        refine ⟨remaining.1, ⟨remaining, hremaining, rfl⟩, ?_⟩
        simpa only [neighbors, Finset.mem_filter, Finset.mem_univ,
          true_and] using htoken
    rw [hneighborhood, hfamilyCard] at hcard
    exact hcard
  obtain ⟨matching, hinjective, hincident⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective neighbors).mp hhall
  refine ⟨⟨matching, hinjective⟩, ?_⟩
  intro remaining
  simpa only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and] using
    hincident remaining




theorem exists_canonicalStableRawComponent_tightHoleState
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : source ∈ sources)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card)
    (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      smaller ⊂ sources ->
        smaller.card ≤
          (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              smaller).card) :
    let TightState := ↑sources
    let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    let incident : TightState -> TightToken -> Prop := fun state token =>
      CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component
          state.1 token.1
    ∃ state : StatMech.FrontierA.RelationPartialMatching.HoleState incident,
      state.hole.1 = source ∧
        state.matching.support = Finset.univ.erase state.hole := by
  classical
  dsimp only
  let TightState := ↑sources
  let neighborhood := canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  let TightToken := ↑neighborhood
  let incident : TightState -> TightToken -> Prop := fun state token =>
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1
  obtain ⟨deletedMatching, hdeletedIncident⟩ :=
    exists_canonicalStableRawComponent_deleteMatching
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources source hsource hproper
  let liftToken : ↑(sources.erase source) -> TightToken := fun remaining =>
    ⟨deletedMatching remaining, by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, remaining.1,
        Finset.mem_of_mem_erase remaining.2, hdeletedIncident remaining⟩⟩
  have hliftInjective : Function.Injective liftToken := by
    intro x y hxy
    apply deletedMatching.injective
    exact congrArg (fun token : TightToken => token.1) hxy
  let hole : TightState := ⟨source, hsource⟩
  let toFun : TightState -> Option TightToken := fun state =>
    if hne : state.1 ≠ source then
      some (liftToken ⟨state.1, Finset.mem_erase.mpr ⟨hne, state.2⟩⟩)
    else none
  have hrelated : ∀ {state token}, toFun state = some token ->
      incident state token := by
    intro state token htoken
    by_cases hne : state.1 ≠ source
    · simp only [toFun, dif_pos hne, Option.some.injEq] at htoken
      subst token
      exact hdeletedIncident
        ⟨state.1, Finset.mem_erase.mpr ⟨hne, state.2⟩⟩
    · simp only [toFun, dif_neg hne] at htoken
      contradiction
  have hinjective : ∀ {x y token}, toFun x = some token ->
      toFun y = some token -> x = y := by
    intro x y token hx hy
    by_cases hxne : x.1 ≠ source
    · by_cases hyne : y.1 ≠ source
      · simp only [toFun, dif_pos hxne, Option.some.injEq] at hx
        simp only [toFun, dif_pos hyne, Option.some.injEq] at hy
        apply Subtype.ext
        have hremaining := hliftInjective (hx.trans hy.symm)
        exact congrArg
          (fun remaining : ↑(sources.erase source) => remaining.1) hremaining
      · simp only [toFun, dif_neg hyne] at hy
        contradiction
    · simp only [toFun, dif_neg hxne] at hx
      contradiction
  let matching : StatMech.FrontierA.RelationPartialMatching incident :=
    ⟨toFun, hrelated, hinjective⟩
  have hsupport : matching.support = Finset.univ.erase hole := by
    ext state
    simp only [StatMech.FrontierA.RelationPartialMatching.mem_support_iff,
      Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨token, htoken⟩ heq
      subst state
      simp [matching, toFun, hole] at htoken
    · intro hne
      have hrawNe : state.1 ≠ source := by
        intro hraw
        apply hne
        apply Subtype.ext
        exact hraw
      exact ⟨liftToken
          ⟨state.1, Finset.mem_erase.mpr ⟨hrawNe, state.2⟩⟩,
        by simp only [matching, toFun, dif_pos hrawNe]⟩
  have hmaximum : matching.IsMaximum := by
    intro other
    have hother := other.card_support_le_target
    have hmatchingCard : matching.support.card = Fintype.card TightToken := by
      rw [hsupport, Finset.card_erase_of_mem (Finset.mem_univ hole),
        Finset.card_univ]
      change Fintype.card TightState - 1 = Fintype.card TightToken
      simpa only [TightState, TightToken, neighborhood, Fintype.card_coe]
        using congrArg (fun n => n - 1) htight.symm
    rw [hmatchingCard]
    exact hother
  have hholeUnmatched : hole ∉ matching.support := by
    rw [hsupport]
    simp
  exact ⟨⟨matching, hmaximum, hole, hholeUnmatched⟩, rfl, hsupport⟩




theorem exists_canonicalStableRawComponent_saturatedTightHoleState
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : source ∈ sources)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card)
    (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      smaller ⊂ sources ->
        smaller.card ≤
          (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              smaller).card) :
    let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    let incident : ↑sources -> TightToken -> Prop := fun state token =>
      CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component
          state.1 token.1
    ∃ state : StatMech.FrontierA.RelationPartialMatching.HoleState incident,
      state.hole.1 = source ∧
        ∀ token : TightToken,
          ∃ matched, state.matching.toFun matched = some token := by
  classical
  dsimp only
  let TightState := ↑sources
  let neighborhood := canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  let TightToken := ↑neighborhood
  let incident : TightState -> TightToken -> Prop := fun state token =>
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1
  obtain ⟨state, hhole, hsupport⟩ :=
    exists_canonicalStableRawComponent_tightHoleState
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources source hsource htight hproper
  have hcard : state.matching.support.card = Fintype.card TightToken := by
    rw [hsupport, Finset.card_erase_of_mem (Finset.mem_univ state.hole),
      Finset.card_univ]
    change Fintype.card TightState - 1 = Fintype.card TightToken
    simpa only [TightState, TightToken, neighborhood, Fintype.card_coe]
      using congrArg (fun n => n - 1) htight.symm
  exact ⟨state, hhole, fun token =>
    state.matching.saturates_all_targets_of_card_support_eq hcard token⟩




theorem
    exists_canonicalStableRawComponent_fourSourceEmbedding_of_threeTightTokens
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : source ∈ sources)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card)
    (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      smaller ⊂ sources ->
        smaller.card ≤
          (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              smaller).card)
    (hthree : Nonempty (Fin 3 ↪
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources))) :
    Nonempty (Fin 4 ↪ ↑sources) := by
  classical
  let TightState := ↑sources
  let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  let incident : TightState -> TightToken -> Prop := fun state token =>
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1
  obtain ⟨state, _hhole, hsaturated⟩ :=
    exists_canonicalStableRawComponent_saturatedTightHoleState
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources source hsource htight hproper
  obtain ⟨tokens⟩ := hthree
  simpa only [Nat.reduceAdd] using
    (saturatedHoleState_sourceEmbedding_add_hole state hsaturated 3 tokens)



noncomputable def canonicalStableRawComponentTightNaturalToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (state : ↑sources) :
    ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources) :=
  ⟨canonicalStableRawComponentNaturalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1,
    by
      classical
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, state.1, state.2,
        canonicalStableRawComponentNaturalToken_incident
          ends m j k l zero hloop hjk hkl hk0 p hno component state.1⟩⟩

theorem canonicalStableRawComponentTightNaturalToken_incident
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (state : ↑sources) :
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1
        (canonicalStableRawComponentTightNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component
            sources state).1 :=
  canonicalStableRawComponentNaturalToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component state.1



noncomputable def canonicalStableRawComponentTightSuccessorToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (state : ↑sources) :
    ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources) :=
  ⟨canonicalStableRawComponentSuccessorToken
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1,
    by
      classical
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, state.1, state.2,
        canonicalStableRawComponentSuccessorToken_incident
          ends m j k l zero hloop hjk hkl hk0 p hno component state.1⟩⟩

theorem canonicalStableRawComponentTightSuccessorToken_incident
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (state : ↑sources) :
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1
        (canonicalStableRawComponentTightSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component
            sources state).1 :=
  canonicalStableRawComponentSuccessorToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component state.1



theorem canonicalStableRawComponent_directOutput_mem_tightNeighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (state : ↑sources)
    (token : ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources))
    (hincident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1)
    (u : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (huTarget : u.target = canonicalStableRawLeftTokenTarget
      ends m j k l zero hloop hjk hkl hk0 p token.1.1)
    (huKind : CanonicalStableRawOwnerStableOutput
        ends m j k l zero hloop hjk hkl hk0 p state.1.1 u ∨
      CanonicalStableRawOwnerAdvancingOutput
        ends m j k l zero hloop hjk hkl hk0 p state.1.1 u)
    (huComponent : canonicalStableRawTokenComponent
      ends m j k l zero hloop hjk hkl hk0 p hno u = component)
    (huDirect : u.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p u.source) :
    let direct : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
        ⟨u, huComponent, huDirect⟩
    canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component direct ∈
      canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
  classical
  dsimp only
  let direct : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨u, huComponent, huDirect⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, state.1, state.2, ?_⟩
  apply (canonicalStableRawWitnessedStateTokenIncidence_iff
    ends m j k l zero hloop hjk hkl hk0 p _ state.1.1).2
  have horiginal := (canonicalStableRawWitnessedStateTokenIncidence_iff
    ends m j k l zero hloop hjk hkl hk0 p token.1.1 state.1.1).1 hincident
  change CanonicalStableRawStateTokenIncidence
    ends m j k l zero hloop hjk hkl hk0 p
      (canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno u) state.1.1
  unfold canonicalStableRawStateLeftToken
  rw [dif_neg huDirect]
  dsimp only [CanonicalStableRawStateTokenIncidence,
    canonicalStableRawDirectLeftToken]
  dsimp only [CanonicalStableRawStateTokenIncidence] at horiginal
  have htarget : u.target.1 = token.1.1.2.1 :=
    congrArg Subtype.val huTarget
  refine ⟨?_, ?_, ?_⟩
  · rcases huKind with huStable | huAdvancing
    · exact Or.inl huStable.1
    · exact Or.inr (Subtype.ext huAdvancing)
  · rw [htarget]
    exact horiginal.2.1
  · rw [htarget]
    exact horiginal.2.2



abbrev CanonicalStableRawComponentTightDirectState
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)) :=
  {direct : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component //
    canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component direct ∈
      canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources}



abbrev CanonicalStableRawComponentTightTerminalToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)) :=
  {terminal : CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component //
    terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}



noncomputable def canonicalStableRawComponentTightForestStep
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (state : ↑sources) :
    CanonicalStableRawComponentTightDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component sources ⊕
      CanonicalStableRawComponentTightTerminalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
  classical
  cases hstep : canonicalStableRawComponentForestStep
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 with
  | inl direct =>
      refine Sum.inl ⟨direct, ?_⟩
      have htoken := canonicalStableRawComponentForestStep_token
        ends m j k l zero hloop hjk hkl hk0 p hno component state.1
      rw [hstep] at htoken
      change canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component direct =
        canonicalStableRawComponentSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component state.1 at htoken
      rw [htoken]
      exact (canonicalStableRawComponentTightSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component sources state).2
  | inr terminal =>
      refine Sum.inr ⟨terminal, ?_⟩
      have htoken := canonicalStableRawComponentForestStep_token
        ends m j k l zero hloop hjk hkl hk0 p hno component state.1
      rw [hstep] at htoken
      change terminal.1 = canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component state.1 at htoken
      rw [htoken]
      exact (canonicalStableRawComponentTightSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component sources state).2



theorem canonicalStableRawComponentTightSuccessorEdge_direct_incident
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (s t : ↑sources)
    (ht : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component t.1
        (canonicalStableRawComponentTightSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component sources s).1)
    (direct : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstep : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component s.1 =
      Sum.inl direct) :
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component t.1
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component direct) := by
  have htoken := canonicalStableRawComponentForestStep_token
    ends m j k l zero hloop hjk hkl hk0 p hno component s.1
  rw [hstep] at htoken
  change canonicalStableRawComponentDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component direct =
    canonicalStableRawComponentSuccessorToken
      ends m j k l zero hloop hjk hkl hk0 p hno component s.1 at htoken
  rw [htoken]
  exact ht



theorem canonicalStableRawComponentTightSuccessorEdge_terminal_incident
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (s t : ↑sources)
    (ht : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component t.1
        (canonicalStableRawComponentTightSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component sources s).1)
    (terminal : CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstep : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component s.1 =
      Sum.inr terminal) :
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component t.1 terminal.1 := by
  have htoken := canonicalStableRawComponentForestStep_token
    ends m j k l zero hloop hjk hkl hk0 p hno component s.1
  rw [hstep] at htoken
  change terminal.1 = canonicalStableRawComponentSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component s.1 at htoken
  rw [htoken]
  exact ht



noncomputable def canonicalStableRawComponentTightSuccessorOther
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (state : ↑sources) : ↑sources := by
  classical
  let token := canonicalStableRawComponentSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component state.1
  have hother := exists_other_mem_of_incident_of_delete_invariant
    ends m j k l zero hloop hjk hkl hk0 p hno component
      sources state.1 state.2 (herase state.1 state.2) token
      (canonicalStableRawComponentSuccessorToken_incident
        ends m j k l zero hloop hjk hkl hk0 p hno component state.1)
  exact ⟨Classical.choose hother, (Classical.choose_spec hother).1⟩

theorem canonicalStableRawComponentTightSuccessorOther_ne
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (state : ↑sources) :
    canonicalStableRawComponentTightSuccessorOther
        ends m j k l zero hloop hjk hkl hk0 p hno component
          sources herase state ≠ state := by
  classical
  let token := canonicalStableRawComponentSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component state.1
  have hother := exists_other_mem_of_incident_of_delete_invariant
    ends m j k l zero hloop hjk hkl hk0 p hno component
      sources state.1 state.2 (herase state.1 state.2) token
      (canonicalStableRawComponentSuccessorToken_incident
        ends m j k l zero hloop hjk hkl hk0 p hno component state.1)
  intro heq
  exact (Classical.choose_spec hother).2.1
    (congrArg Subtype.val heq)

theorem canonicalStableRawComponentTightSuccessorOther_incident
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (state : ↑sources) :
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (canonicalStableRawComponentTightSuccessorOther
          ends m j k l zero hloop hjk hkl hk0 p hno component
            sources herase state).1
        (canonicalStableRawComponentTightSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component
            sources state).1 := by
  classical
  let token := canonicalStableRawComponentSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component state.1
  have hother := exists_other_mem_of_incident_of_delete_invariant
    ends m j k l zero hloop hjk hkl hk0 p hno component
      sources state.1 state.2 (herase state.1 state.2) token
      (canonicalStableRawComponentSuccessorToken_incident
        ends m j k l zero hloop hjk hkl hk0 p hno component state.1)
  exact (Classical.choose_spec hother).2.2



theorem canonicalStableRawComponentTightSuccessorOther_forestStep_incident
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (state : ↑sources) :
    let next := canonicalStableRawComponentTightSuccessorOther
      ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
    (∃ direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component state.1 =
          Sum.inl direct ∧
        CanonicalStableRawComponentIncident
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (next state).1
            (canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component direct)) ∨
      ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component state.1 =
          Sum.inr terminal ∧
        CanonicalStableRawComponentIncident
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (next state).1 terminal.1 := by
  classical
  dsimp only
  let next := canonicalStableRawComponentTightSuccessorOther
    ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
  have hnext := canonicalStableRawComponentTightSuccessorOther_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component sources herase state
  cases hstep : canonicalStableRawComponentForestStep
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 with
  | inl direct =>
      refine Or.inl ⟨direct, rfl, ?_⟩
      exact
        canonicalStableRawComponentTightSuccessorEdge_direct_incident
          ends m j k l zero hloop hjk hkl hk0 p hno component sources
            state (next state) hnext direct hstep
  | inr terminal =>
      refine Or.inr ⟨terminal, rfl, ?_⟩
      exact
        canonicalStableRawComponentTightSuccessorEdge_terminal_incident
          ends m j k l zero hloop hjk hkl hk0 p hno component sources
            state (next state) hnext terminal hstep



theorem exists_canonicalStableRawComponentTightSuccessorOther_repeat
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hnonempty : sources.Nonempty)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    let next := canonicalStableRawComponentTightSuccessorOther
      ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
    ∃ start : ↑sources, ∃ a b : Nat,
      a < b ∧ b ≤ Fintype.card ↑sources ∧
        next^[a] start = next^[b] start ∧
        ∀ state, next state ≠ state := by
  classical
  dsimp only
  let next := canonicalStableRawComponentTightSuccessorOther
    ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
  let start : ↑sources := ⟨hnonempty.choose, hnonempty.choose_spec⟩
  obtain ⟨a, b, hab, hb, hrepeat⟩ :=
    exists_function_iterate_repeat next start
  exact ⟨start, a, b, hab, hb, hrepeat, fun state =>
    canonicalStableRawComponentTightSuccessorOther_ne
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources herase state⟩



theorem
    exists_canonicalStableRawComponentTightSuccessorOther_localized_repeat
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hnonempty : sources.Nonempty)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    let next := canonicalStableRawComponentTightSuccessorOther
      ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
    ∃ start : ↑sources, ∃ a b : Nat,
      a < b ∧ b ≤ Fintype.card ↑sources ∧
        next^[a] start = next^[b] start ∧
        (∀ state, next state ≠ state) ∧
        ∀ state,
          (∃ direct : CanonicalStableRawComponentDirectState
                ends m j k l zero hloop hjk hkl hk0 p hno component,
              canonicalStableRawComponentForestStep
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    state.1 = Sum.inl direct ∧
              CanonicalStableRawComponentIncident
                ends m j k l zero hloop hjk hkl hk0 p hno component
                  (next state).1
                  (canonicalStableRawComponentDirectEmbedding
                    ends m j k l zero hloop hjk hkl hk0 p hno component
                      direct)) ∨
            ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
                ends m j k l zero hloop hjk hkl hk0 p hno component,
              canonicalStableRawComponentForestStep
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    state.1 = Sum.inr terminal ∧
              CanonicalStableRawComponentIncident
                ends m j k l zero hloop hjk hkl hk0 p hno component
                  (next state).1 terminal.1 := by
  classical
  dsimp only
  let next := canonicalStableRawComponentTightSuccessorOther
    ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
  obtain ⟨start, a, b, hab, hb, hrepeat, hne⟩ :=
    exists_canonicalStableRawComponentTightSuccessorOther_repeat
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources hnonempty herase
  exact ⟨start, a, b, hab, hb, hrepeat, hne, fun state =>
    canonicalStableRawComponentTightSuccessorOther_forestStep_incident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources herase state⟩



theorem exists_canonicalStableRawComponentTightSuccessorOther_rankNondrop
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hnonempty : sources.Nonempty)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    let next := canonicalStableRawComponentTightSuccessorOther
      ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
    ∃ state : ↑sources,
      ¬ canonicalStableRawSourceRank ends m j k l zero p
            (next state).1.1.source <
          canonicalStableRawSourceRank ends m j k l zero p state.1.1.source := by
  classical
  dsimp only
  let next := canonicalStableRawComponentTightSuccessorOther
    ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
  let rank : ↑sources -> Nat := fun state =>
    canonicalStableRawSourceRank ends m j k l zero p state.1.1.source
  let start : ↑sources := ⟨hnonempty.choose, hnonempty.choose_spec⟩
  by_contra hnone
  have hall (state : ↑sources) : rank (next state) < rank state := by
    by_contra hnot
    exact hnone ⟨state, hnot⟩
  have hbound : ∀ n : Nat,
      rank ((next^[n]) start) + n ≤ rank start := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        have hdrop := hall ((next^[n]) start)
        omega
  have hfinal := hbound (rank start + 1)
  omega



theorem
    exists_canonicalStableRawComponent_minimalTightRankNondrop_of_deficit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ sources : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      ∃ herase : ∀ source ∈ sources,
        canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (sources.erase source) =
          canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources,
        sources.Nonempty ∧
        (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              sources).card + 1 = sources.card ∧
        (∀ smaller : Finset (CanonicalStableRawComponentState
            ends m j k l zero hloop hjk hkl hk0 p hno component),
          smaller ⊂ sources ->
            smaller.card ≤
              (canonicalStableRawComponentIncidentNeighborhood
                ends m j k l zero hloop hjk hkl hk0 p hno component
                  smaller).card) ∧
        let next := canonicalStableRawComponentTightSuccessorOther
          ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
        ∃ state : ↑sources,
          ¬ canonicalStableRawSourceRank ends m j k l zero p
                (next state).1.1.source <
              canonicalStableRawSourceRank ends m j k l zero p
                state.1.1.source := by
  classical
  obtain ⟨sources, hnonempty, htight, herase, hproper⟩ :=
    exists_canonicalStableRawComponent_minimalIncidentObstruction_of_deficit
      ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit
  refine ⟨sources, herase, hnonempty, htight, hproper, ?_⟩
  exact exists_canonicalStableRawComponentTightSuccessorOther_rankNondrop
    ends m j k l zero hloop hjk hkl hk0 p hno component
      sources hnonempty herase





theorem exists_canonicalStableRawComponent_tightSuccessorOrbit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : source ∈ sources)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card)
    (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      smaller ⊂ sources ->
        smaller.card ≤
          (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              smaller).card) :
    let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    let incident : ↑sources -> TightToken -> Prop := fun state token =>
      CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component
          state.1 token.1
    let successor := canonicalStableRawComponentTightSuccessorToken
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
    ∃ state : StatMech.FrontierA.RelationPartialMatching.HoleState incident,
      ∃ next : ↑sources -> ↑sources,
        state.hole.1 = source ∧
        (∀ s, state.matching.toFun (next s) = some (successor s)) ∧
        (∀ s, incident (next s) (successor s)) ∧
        (∀ s, next s ≠ state.hole) ∧
        ∃ i j : Nat, i < j ∧ j ≤ Fintype.card ↑sources ∧
          next^[i] (next state.hole) = next^[j] (next state.hole) := by
  classical
  dsimp only
  let TightState := ↑sources
  let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  let incident : TightState -> TightToken -> Prop := fun state token =>
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1
  let successor := canonicalStableRawComponentTightSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  obtain ⟨state, hhole, hsaturated⟩ :=
    exists_canonicalStableRawComponent_saturatedTightHoleState
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources source hsource htight hproper
  let next : TightState -> TightState := fun s =>
    state.matching.targetPreimage hsaturated (successor s)
  have hnext (s : TightState) :
      state.matching.toFun (next s) = some (successor s) :=
    state.matching.targetPreimage_spec hsaturated (successor s)
  have hrelated (s : TightState) : incident (next s) (successor s) :=
    state.matching.related (hnext s)
  have hneHole (s : TightState) : next s ≠ state.hole := by
    intro heq
    apply state.hole_unmatched
    apply (StatMech.FrontierA.RelationPartialMatching.mem_support_iff
      state.matching state.hole).2
    exact ⟨successor s, heq ▸ hnext s⟩
  obtain ⟨i, j, hij, hj, hrepeat⟩ :=
    exists_function_iterate_repeat next (next state.hole)
  exact ⟨state, next, hhole, hnext, hrelated, hneHole,
    i, j, hij, hj, hrepeat⟩




theorem exists_canonicalStableRawComponent_tightSuccessorCycle
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : source ∈ sources)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card)
    (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      smaller ⊂ sources ->
        smaller.card ≤
          (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              smaller).card) :
    let TightState := ↑sources
    let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    let incident : TightState -> TightToken -> Prop := fun state token =>
      CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component
          state.1 token.1
    let successor := canonicalStableRawComponentTightSuccessorToken
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
    ∃ size : Nat, 0 < size ∧
      ∃ cycle : Fin size ↪ TightState, ∃ σ : Equiv.Perm (Fin size),
        ∃ tokens : Fin size ↪ TightToken,
          ∃ missing : TightState,
            (∀ i, cycle i ≠ missing) ∧
            (∀ i, tokens i = successor (cycle i)) ∧
            (∀ i, incident (cycle (σ i)) (tokens i)) ∧
            ∃ external : TightState,
              (∀ q, external ≠ cycle q) ∧
              ∃ i, incident external (tokens i) := by
  classical
  dsimp only
  let TightState := ↑sources
  let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  let incident : TightState -> TightToken -> Prop := fun state token =>
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1
  let successor := canonicalStableRawComponentTightSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  obtain ⟨state, next, _hhole, hnext, hrelated, hneHole,
      _a, _b, _hab, _hb, _hrepeat⟩ :=
    exists_canonicalStableRawComponent_tightSuccessorOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources source hsource htight hproper
  obtain ⟨size, hsize, cycle, σ, hcycle⟩ :=
    exists_function_cycleEmbedding next (next state.hole)
  let tokenMap : Fin size -> TightToken := fun i => successor (cycle i)
  have htokenInjective : Function.Injective tokenMap := by
    intro i q hiq
    have hnextEq : next (cycle i) = next (cycle q) := by
      exact state.matching.injective_some (hnext (cycle i))
        ((hnext (cycle q)).trans (congrArg some hiq.symm))
    have hcycleEq : cycle (σ i) = cycle (σ q) := by
      rw [hcycle i, hcycle q]
      exact hnextEq
    exact σ.injective (cycle.injective hcycleEq)
  let tokens : Fin size ↪ TightToken := ⟨tokenMap, htokenInjective⟩
  have hcycleNeHole (i : Fin size) : cycle i ≠ state.hole := by
    intro heq
    apply hneHole (cycle (σ.symm i))
    calc
      next (cycle (σ.symm i)) = cycle (σ (σ.symm i)) :=
        (hcycle (σ.symm i)).symm
      _ = cycle i := congrArg cycle (σ.apply_symm_apply i)
      _ = state.hole := heq
  letI : DecidableRel incident := fun _ _ => Classical.propDecidable _
  have htightCard : Fintype.card TightToken + 1 =
      Fintype.card TightState := by
    simpa only [TightToken, TightState, Fintype.card_coe] using htight
  have hproperRelation : ∀ smaller : Finset TightState,
      smaller ⊂ Finset.univ ->
        smaller.card ≤
          (Finset.univ.filter fun token =>
            ∃ source ∈ smaller, incident source token).card := by
    intro smaller hsmaller
    have hhall := canonicalStableRawComponent_tightProperHall
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources hproper smaller hsmaller
    simpa only [canonicalStableRawComponentRestrictedIncidentNeighborhood,
      incident] using hhall
  obtain ⟨index, external, hexternal, hexternalIncident⟩ :=
    exists_external_incident_of_tight_properHall
      incident htightCard hproperRelation size hsize cycle tokens
  refine ⟨size, hsize, cycle, σ, tokens, state.hole,
    hcycleNeHole, fun i => rfl, ?_, external, hexternal,
      index, hexternalIncident⟩
  intro i
  change incident (cycle (σ i)) (successor (cycle i))
  rw [hcycle i]
  exact hrelated (cycle i)



theorem canonicalStableRawComponentTightSuccessorEdge_classification
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (s t : ↑sources)
    (hne : s.1 ≠ t.1)
    (ht : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component t.1
        (canonicalStableRawComponentTightSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component sources s).1) :
    ∃ u : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p,
      u.target = canonicalStableRawLeftTokenTarget
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawComponentTightSuccessorToken
            ends m j k l zero hloop hjk hkl hk0 p hno component sources s).1 ∧
      (CanonicalStableRawOwnerStableOutput
          ends m j k l zero hloop hjk hkl hk0 p s.1.1 u ∨
        CanonicalStableRawOwnerAdvancingOutput
          ends m j k l zero hloop hjk hkl hk0 p s.1.1 u) ∧
      canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  have hs := canonicalStableRawComponentTightSuccessorToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component sources s
  have hclassification :=
    canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
      ends m j k l zero hloop hjk hkl hk0 p hno
        (canonicalStableRawComponentTightSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component sources s).1
        s.1 t.1 hs ht
  rcases hclassification with heq | hstable | hadvancing
  · exact False.elim (hne (Subtype.ext heq))
  · exact ⟨hstable.choose, hstable.choose_spec.1,
      Or.inl hstable.choose_spec.2.1,
      hstable.choose_spec.2.2.1.trans s.1.2⟩
  · exact ⟨hadvancing.choose, hadvancing.choose_spec.1,
      Or.inr hadvancing.choose_spec.2.1,
      hadvancing.choose_spec.2.2.1.trans s.1.2⟩




theorem exists_canonicalStableRawComponent_tightSuccessorBoundaryOutput
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : source ∈ sources)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card)
    (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      smaller ⊂ sources ->
        smaller.card ≤
          (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              smaller).card) :
    ∃ size : Nat, 0 < size ∧
      ∃ cycle : Fin size ↪ ↑sources,
        ∃ index : Fin size, ∃ external : ↑sources,
          (∀ q, external ≠ cycle q) ∧
          CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component external.1
              (canonicalStableRawComponentTightSuccessorToken
                ends m j k l zero hloop hjk hkl hk0 p hno component
                  sources (cycle index)).1 ∧
          ∃ u : CanonicalStableRawExceptionalEdge
              ends m j k l zero hloop hjk hkl hk0 p,
            u.target = canonicalStableRawLeftTokenTarget
              ends m j k l zero hloop hjk hkl hk0 p
                (canonicalStableRawComponentTightSuccessorToken
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    sources (cycle index)).1 ∧
            (CanonicalStableRawOwnerStableOutput
                ends m j k l zero hloop hjk hkl hk0 p
                  (cycle index).1.1 u ∨
              CanonicalStableRawOwnerAdvancingOutput
                ends m j k l zero hloop hjk hkl hk0 p
                  (cycle index).1.1 u) ∧
            canonicalStableRawTokenComponent
                ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  classical
  let TightState := ↑sources
  let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  let incident : TightState -> TightToken -> Prop := fun state token =>
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1
  let successor := canonicalStableRawComponentTightSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  obtain ⟨size, hsize, cycle, _σ, _tokens, _missing, _hmissing,
      htokens, _hcycleIncident, external, hexternal,
      index, hexternalIncident⟩ :=
    exists_canonicalStableRawComponent_tightSuccessorCycle
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources source hsource htight hproper
  have hexternalSuccessor : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component external.1
        (successor (cycle index)).1 := by
    have heq := htokens index
    exact congrArg Subtype.val heq ▸ hexternalIncident
  have hne : (cycle index).1 ≠ external.1 := by
    intro heq
    apply hexternal index
    exact Subtype.ext heq.symm
  obtain ⟨u, huTarget, huKind, huComponent⟩ :=
    canonicalStableRawComponentTightSuccessorEdge_classification
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
        (cycle index) external hne hexternalSuccessor
  exact ⟨size, hsize, cycle, index, external, hexternal,
    hexternalSuccessor, u, huTarget, huKind, huComponent⟩




theorem
    exists_canonicalStableRawComponent_tightSuccessorCycle_terminal_or_directBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : source ∈ sources)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card)
    (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      smaller ⊂ sources ->
        smaller.card ≤
          (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              smaller).card) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      ∃ size : Nat, 0 < size ∧
        ∃ directs : Fin size ↪ CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          ∃ tokens : Fin size ↪
              ↑(canonicalStableRawComponentIncidentNeighborhood
                ends m j k l zero hloop hjk hkl hk0 p hno component sources),
            ∀ i,
              canonicalStableRawComponentDirectEmbedding
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    (directs i) =
                (tokens i).1 := by
  classical
  obtain ⟨size, hsize, _cycle, _σ, tokens, _missing, _hmissing,
      _htokens, _hcycleIncident, _external, _hexternal,
      _index, _hexternalIncident⟩ :=
    exists_canonicalStableRawComponent_tightSuccessorCycle
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources source hsource htight hproper
  by_cases hallExceptional : ∀ i,
      CanonicalStableRawLeftTokenIsExceptional
        ends m j k l zero hloop hjk hkl hk0 p (tokens i).1.1
  · let exceptionalTokens : Fin size ↪
        CanonicalStableRawComponentExceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component := by
      let toExceptional : Fin size ->
          CanonicalStableRawComponentExceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component := fun i =>
        ⟨(tokens i).1, hallExceptional i⟩
      refine ⟨toExceptional, ?_⟩
      intro i q hiq
      apply tokens.injective
      exact Subtype.ext (congrArg
        (fun token : CanonicalStableRawComponentExceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component => token.1)
        hiq)
    let exceptionalEquiv :=
      canonicalStableRawComponentDirectStateEquivExceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component
    let directs : Fin size ↪ CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      exceptionalTokens.trans exceptionalEquiv.symm.toEmbedding
    refine Or.inr ⟨size, hsize, directs, tokens, ?_⟩
    intro i
    change (exceptionalEquiv (exceptionalEquiv.symm (exceptionalTokens i))).1 =
      (tokens i).1
    rw [exceptionalEquiv.apply_symm_apply]
    rfl
  · push_neg at hallExceptional
    obtain ⟨i, hi⟩ := hallExceptional
    let terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨(tokens i).1, hi⟩
    exact Or.inl ⟨terminal, (tokens i).2⟩




theorem
    exists_canonicalStableRawComponent_tightSuccessorBoundary_direct_or_self
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : source ∈ sources)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card)
    (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      smaller ⊂ sources ->
        smaller.card ≤
          (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              smaller).card) :
    Nonempty (CanonicalStableRawComponentTightDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      Nonempty (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  obtain ⟨_size, _hsize, cycle, index, _external, _hexternal,
      _hexternalSuccessor, u, huTarget, huKind, huComponent⟩ :=
    exists_canonicalStableRawComponent_tightSuccessorBoundaryOutput
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources source hsource htight hproper
  let token := canonicalStableRawComponentTightSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
      sources (cycle index)
  have hincident := canonicalStableRawComponentTightSuccessorToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component
      sources (cycle index)
  by_cases huDirect : u.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p u.source
  · let direct : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨u, huComponent, huDirect⟩
    have hmem := canonicalStableRawComponent_directOutput_mem_tightNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
        (cycle index) token hincident u huTarget huKind huComponent huDirect
    exact Or.inl ⟨⟨direct, hmem⟩⟩
  · have huSelf : u.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p u.source :=
      Classical.not_not.mp huDirect
    exact Or.inr ⟨⟨u, huComponent, huSelf⟩⟩





theorem
    exists_canonicalStableRawComponent_tightSuccessorCycle_externalDischarge
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : source ∈ sources)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card)
    (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      smaller ⊂ sources ->
        smaller.card ≤
          (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              smaller).card) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      ∃ size : Nat, 0 < size ∧
        ∃ cycle : Fin size ↪ ↑sources,
          ∃ directs : Fin size ↪ CanonicalStableRawComponentDirectState
              ends m j k l zero hloop hjk hkl hk0 p hno component,
            ∃ tokens : Fin size ↪
                ↑(canonicalStableRawComponentIncidentNeighborhood
                  ends m j k l zero hloop hjk hkl hk0 p hno component sources),
              ∃ external : ↑sources,
                (∀ q, external ≠ cycle q) ∧
                (∀ i,
                  canonicalStableRawComponentDirectEmbedding
                      ends m j k l zero hloop hjk hkl hk0 p hno component
                        (directs i) =
                    (tokens i).1) ∧
                (Nonempty (Fin (size + 1) ↪
                    ↑(canonicalStableRawComponentIncidentNeighborhood
                      ends m j k l zero hloop hjk hkl hk0 p hno component
                        sources)) ∨
                  (∃ i, external.1.1 = (directs i).1) ∨
                  ∃ collision : StatMech.FrontierA.crossCollision
                      (canonicalStableRawComponentSelfEmbedding
                        ends m j k l zero hloop hjk hkl hk0 p hno component)
                      (canonicalStableRawComponentDirectEmbedding
                        ends m j k l zero hloop hjk hkl hk0 p hno component),
                    external.1.1 = collision.1.1.1) := by
  classical
  let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  let natural := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  obtain ⟨size, hsize, cycle, _σ, tokens, _missing, _hmissing,
      _htokens, _hcycleIncident, external, hexternal,
      _index, _hexternalIncident⟩ :=
    exists_canonicalStableRawComponent_tightSuccessorCycle
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources source hsource htight hproper
  by_cases hallExceptional : ∀ i,
      CanonicalStableRawLeftTokenIsExceptional
        ends m j k l zero hloop hjk hkl hk0 p (tokens i).1.1
  · let exceptionalTokens : Fin size ↪
        CanonicalStableRawComponentExceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component := by
      let toExceptional : Fin size ->
          CanonicalStableRawComponentExceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component := fun i =>
        ⟨(tokens i).1, hallExceptional i⟩
      refine ⟨toExceptional, ?_⟩
      intro i q hiq
      apply tokens.injective
      exact Subtype.ext (congrArg
        (fun token : CanonicalStableRawComponentExceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component => token.1)
        hiq)
    let exceptionalEquiv :=
      canonicalStableRawComponentDirectStateEquivExceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component
    let directs : Fin size ↪ CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      exceptionalTokens.trans exceptionalEquiv.symm.toEmbedding
    have hdirect (i : Fin size) :
        canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (directs i) =
          (tokens i).1 := by
      change (exceptionalEquiv
        (exceptionalEquiv.symm (exceptionalTokens i))).1 = (tokens i).1
      rw [exceptionalEquiv.apply_symm_apply]
      rfl
    refine Or.inr ⟨size, hsize, cycle, directs, tokens, external,
      hexternal, hdirect, ?_⟩
    by_cases hfresh : ∀ i, natural external ≠ tokens i
    · exact Or.inl (finiteEmbedding_add_fresh size tokens
        (natural external) hfresh)
    · push_neg at hfresh
      obtain ⟨i, hi⟩ := hfresh
      have hraw : canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno external.1.1 =
          canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno (directs i).1 := by
        calc
          canonicalStableRawStateLeftToken
              ends m j k l zero hloop hjk hkl hk0 p hno external.1.1 =
              (tokens i).1.1 :=
            congrArg (fun token : TightToken => token.1.1) hi
          _ = (canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component
                (directs i)).1 := congrArg Subtype.val (hdirect i).symm
          _ = canonicalStableRawStateLeftToken
              ends m j k l zero hloop hjk hkl hk0 p hno (directs i).1 := rfl
      rcases canonicalStableRawStateLeftToken_eq_imp
          ends m j k l zero hloop hjk hkl hk0 p hno
            external.1.1 (directs i).1 hraw with
        heq | hforward | hreverse
      · exact Or.inr (Or.inl ⟨i, heq⟩)
      · let self : CanonicalStableRawComponentSelfState
            ends m j k l zero hloop hjk hkl hk0 p hno component :=
          ⟨external.1.1, external.1.2, hforward.1⟩
        let collision : StatMech.FrontierA.crossCollision
            (canonicalStableRawComponentSelfEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component)
            (canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component) :=
          ⟨(self, directs i), by
            apply Subtype.ext
            exact hraw⟩
        exact Or.inr (Or.inr ⟨collision, rfl⟩)
      · exact False.elim ((directs i).2.2 hreverse.1)
  · push_neg at hallExceptional
    obtain ⟨i, hi⟩ := hallExceptional
    let terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨(tokens i).1, hi⟩
    exact Or.inl ⟨terminal, (tokens i).2⟩




theorem
    exists_canonicalStableRawComponent_tightSuccessorCycle_fresh_or_exhausts
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : source ∈ sources)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card)
    (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      smaller ⊂ sources ->
        smaller.card ≤
          (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              smaller).card) :
    let TightState := ↑sources
    let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    ∃ size : Nat, 0 < size ∧
      ∃ cycle : Fin size ↪ TightState,
        ∃ external : TightState,
          (∀ q, external ≠ cycle q) ∧
          (Nonempty (Fin (size + 1) ↪ TightToken) ∨
            ∀ state : TightState,
              state = external ∨ ∃ i, state = cycle i) := by
  classical
  dsimp only
  let TightState := ↑sources
  let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  let incident : TightState -> TightToken -> Prop := fun state token =>
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1
  obtain ⟨size, hsize, cycle, _σ, _tokens, _missing, _hmissing,
      _htokens, _hcycleIncident, external, hexternal,
      _index, _hexternalIncident⟩ :=
    exists_canonicalStableRawComponent_tightSuccessorCycle
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources source hsource htight hproper
  letI : DecidableRel incident := fun _ _ => Classical.propDecidable _
  have hproperRelation : ∀ smaller : Finset TightState,
      smaller ⊂ Finset.univ ->
        smaller.card ≤
          (Finset.univ.filter fun token =>
            ∃ state ∈ smaller, incident state token).card := by
    intro smaller hsmaller
    have hhall := canonicalStableRawComponent_tightProperHall
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources hproper smaller hsmaller
    simpa only [canonicalStableRawComponentRestrictedIncidentNeighborhood,
      incident] using hhall
  have hboundary := tightProperHall_externalSource_freshToken_or_exhausts
    incident hproperRelation size cycle external hexternal
  exact ⟨size, hsize, cycle, external, hexternal, hboundary⟩



theorem canonicalStableRawComponent_no_fullTightTokenBlock_of_exhaustiveCycle
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card)
    (size : Nat) (cycle : Fin size ↪ ↑sources) (external : ↑sources)
    (hcover : ∀ state : ↑sources,
      state = external ∨ ∃ i, state = cycle i)
    (htokens : Nonempty (Fin (size + 1) ↪
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources))) : False := by
  let cover : Fin size ⊕ Fin 1 -> ↑sources
    | Sum.inl i => cycle i
    | Sum.inr _ => external
  have hsurjective : Function.Surjective cover := by
    intro state
    rcases hcover state with heq | ⟨i, heq⟩
    · exact ⟨Sum.inr 0, by simpa only [cover] using heq.symm⟩
    · exact ⟨Sum.inl i, by simpa only [cover] using heq.symm⟩
  have hsourcesCard : sources.card ≤ size + 1 := by
    have hcard := Fintype.card_le_of_surjective cover hsurjective
    simpa only [Fintype.card_coe, Fintype.card_sum, Fintype.card_fin,
      Nat.add_comm] using hcard
  obtain ⟨tokens⟩ := htokens
  have htokensCard : size + 1 ≤
      (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      Fintype.card_le_of_injective tokens tokens.injective
  omega




theorem canonicalStableRawComponent_referenceOwnerCollision_mem_tightNeighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (external : ↑sources)
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hself : external.1.1 = collision.1.1.1) :
    canonicalStableRawComponentReferenceOwnerCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision ∈
      canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, external.1, external.2, ?_⟩
  apply (canonicalStableRawWitnessedStateTokenIncidence_iff
    ends m j k l zero hloop hjk hkl hk0 p _ external.1.1).2
  rw [hself]
  exact canonicalStableRawReferenceOwnerLeftToken_stateTokenIncidence
    ends m j k l zero hloop hjk hkl hk0 p
      collision.1.1.1 collision.1.1.2.2




theorem
    canonicalStableRawComponent_referenceSourceCollision_mem_tightNeighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (external : ↑sources)
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hself : external.1.1 = collision.1.1.1) :
    canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision ∈
      canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, external.1, external.2, ?_⟩
  apply (canonicalStableRawWitnessedStateTokenIncidence_iff
    ends m j k l zero hloop hjk hkl hk0 p _ external.1.1).2
  rw [hself]
  exact canonicalStableRawReferenceSourceLeftToken_stateTokenIncidence
    ends m j k l zero hloop hjk hkl hk0 p
      collision.1.1.1 collision.1.1.2.2




theorem canonicalStableRawComponent_referenceSourceCollision_ne_ownerCollision
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component collision ≠
      canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component collision := by
  intro heq
  have hsource := congrArg
    (fun token : CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component =>
      token.1.1.1) heq
  change collision.1.1.1.source.1 =
    canonicalStableRawPreferredRightBase ends m j k l zero
      hloop hjk hkl hk0 p collision.1.1.1.target at hsource
  exact collision.1.1.1.exceptional hsource




theorem
    CanonicalStableRawComponentRichIncidenceBlock.extendByReferenceCharges_or_repeats
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : ∀ i, source ≠ block.sources i)
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hself : source.1 = collision.1.1.1) :
    (∃ extended : CanonicalStableRawComponentRichIncidenceBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        extended.size = block.size + 1) ∨
      ∃ q r : Fin (block.size + 1), q ≠ r ∧
        canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component collision =
          block.tokens q ∧
        canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component collision =
          block.tokens r := by
  let sourceToken :=
    canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component collision
  let ownerToken := canonicalStableRawComponentReferenceOwnerCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component collision
  have hsourceIncident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component source sourceToken := by
    apply (canonicalStableRawWitnessedStateTokenIncidence_iff
      ends m j k l zero hloop hjk hkl hk0 p sourceToken.1 source.1).2
    rw [hself]
    exact canonicalStableRawReferenceSourceLeftToken_stateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        collision.1.1.1 collision.1.1.2.2
  have hownerIncident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component source ownerToken := by
    apply (canonicalStableRawWitnessedStateTokenIncidence_iff
      ends m j k l zero hloop hjk hkl hk0 p ownerToken.1 source.1).2
    rw [hself]
    exact canonicalStableRawReferenceOwnerLeftToken_stateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        collision.1.1.1 collision.1.1.2.2
  by_cases hsourceFresh : ∀ q, sourceToken ≠ block.tokens q
  · exact Or.inl
      (block.extend source sourceToken hsource hsourceFresh hsourceIncident)
  · push Not at hsourceFresh
    obtain ⟨q, hq⟩ := hsourceFresh
    by_cases hownerFresh : ∀ r, ownerToken ≠ block.tokens r
    · exact Or.inl
        (block.extend source ownerToken hsource hownerFresh hownerIncident)
    · push Not at hownerFresh
      obtain ⟨r, hr⟩ := hownerFresh
      right
      refine ⟨q, r, ?_, hq, hr⟩
      intro hqr
      apply canonicalStableRawComponent_referenceSourceCollision_ne_ownerCollision
        ends m j k l zero hloop hjk hkl hk0 p hno component collision
      exact hq.trans (hqr ▸ hr.symm)





theorem
    CanonicalStableRawComponentRichIncidenceBlock.closureStep_localized
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    block.IsClosed ∨
      (∃ extended : CanonicalStableRawComponentRichIncidenceBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        extended.size = block.size + 1) ∨
      (∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        (∀ i, source ≠ block.sources i) ∧
        ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          terminal.1 = canonicalStableRawComponentNaturalToken
              ends m j k l zero hloop hjk hkl hk0 p hno component source ∧
            ∃ q, canonicalStableRawComponentNaturalToken
                ends m j k l zero hloop hjk hkl hk0 p hno component source =
              block.tokens q) ∨
      (∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ direct : CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          source.1 = direct.1 ∧
          (∀ i, source ≠ block.sources i) ∧
          ∃ q r : Fin (block.size + 1), q ≠ r ∧
            canonicalStableRawComponentNaturalToken
                ends m j k l zero hloop hjk hkl hk0 p hno component source =
              block.tokens q ∧
            canonicalStableRawComponentSuccessorToken
                ends m j k l zero hloop hjk hkl hk0 p hno component source =
              block.tokens r) ∨
      ∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ collision : StatMech.FrontierA.crossCollision
            (canonicalStableRawComponentSelfEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component)
            (canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component),
          source.1 = collision.1.1.1 ∧
          (∀ i, source ≠ block.sources i) ∧
          ∃ q r s : Fin (block.size + 1), r ≠ s ∧
            canonicalStableRawComponentNaturalToken
                ends m j k l zero hloop hjk hkl hk0 p hno component source =
              block.tokens q ∧
            canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
                ends m j k l zero hloop hjk hkl hk0 p hno component collision =
              block.tokens r ∧
            canonicalStableRawComponentReferenceOwnerCollisionEmbedding
                ends m j k l zero hloop hjk hkl hk0 p hno component collision =
              block.tokens s := by
  rcases block.closureStep_stateClassification with
      hclosed | hextended |
        ⟨source, hsource, ⟨q, hnatural⟩, hterminal | hcollision | hdirect⟩
  · exact Or.inl hclosed
  · exact Or.inr (Or.inl hextended)
  · obtain ⟨terminal, hterminal⟩ := hterminal
    exact Or.inr (Or.inr (Or.inl
      ⟨source, hsource, terminal, hterminal, q, hnatural⟩))
  · obtain ⟨collision, hself⟩ := hcollision
    rcases block.extendByReferenceCharges_or_repeats
        source hsource collision hself with hextended | ⟨r, s, hrs, hr, hs⟩
    · exact Or.inr (Or.inl hextended)
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨source, collision, hself, hsource, q, r, s, hrs,
          hnatural, hr, hs⟩)))
  · obtain ⟨direct, hdirect⟩ := hdirect
    rcases block.extendBySuccessor_or_repeat source hsource with
      hextended | ⟨r, hsuccessor⟩
    · exact Or.inr (Or.inl hextended)
    · have hqr : q ≠ r := by
        intro hqr
        apply canonicalStableRawComponentSuccessorToken_ne_natural
          ends m j k l zero hloop hjk hkl hk0 p hno component source
        exact hsuccessor.trans (hqr ▸ hnatural.symm)
      exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨source, direct, hdirect, hsource, q, r, hqr,
          hnatural, hsuccessor⟩)))


def CanonicalStableRawComponentRichIncidenceBlock.HasLocalizedObstruction
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) : Prop :=
  (∃ source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component,
    (∀ i, source ≠ block.sources i) ∧
    ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      terminal.1 = canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component source ∧
        ∃ q, canonicalStableRawComponentNaturalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component source =
          block.tokens q) ∨
  (∃ source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component,
    ∃ direct : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      source.1 = direct.1 ∧
      (∀ i, source ≠ block.sources i) ∧
      ∃ q r : Fin (block.size + 1), q ≠ r ∧
        canonicalStableRawComponentNaturalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component source =
          block.tokens q ∧
        canonicalStableRawComponentSuccessorToken
            ends m j k l zero hloop hjk hkl hk0 p hno component source =
          block.tokens r) ∨
  ∃ source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component,
    ∃ collision : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component),
      source.1 = collision.1.1.1 ∧
      (∀ i, source ≠ block.sources i) ∧
      ∃ q r s : Fin (block.size + 1), r ≠ s ∧
        canonicalStableRawComponentNaturalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component source =
          block.tokens q ∧
        canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component collision =
          block.tokens r ∧
        canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component collision =
          block.tokens s




theorem exists_canonicalStableRawComponent_sizeMaximal_closed_or_localized
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    ∃ block : CanonicalStableRawComponentRichIncidenceBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      (∀ other : CanonicalStableRawComponentRichIncidenceBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        other.size ≤ block.size) ∧
      (block.IsClosed ∨ block.HasLocalizedObstruction) := by
  obtain ⟨block, hmax⟩ :=
    exists_canonicalStableRawComponent_sizeMaximalRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component start
  refine ⟨block, hmax, ?_⟩
  rcases block.closureStep_localized with
    hclosed | ⟨extended, hextended⟩ | hterminal | hdirect | hcollision
  · exact Or.inl hclosed
  · exact False.elim (by
      have hle := hmax extended
      omega)
  · exact Or.inr (Or.inl hterminal)
  · exact Or.inr (Or.inr (Or.inl hdirect))
  · exact Or.inr (Or.inr (Or.inr hcollision))



theorem
    CanonicalStableRawComponentRichIncidenceBlock.HasLocalizedObstruction.extension_or_pivot
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hobstruction : block.HasLocalizedObstruction) :
    (∃ extended : CanonicalStableRawComponentRichIncidenceBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        extended.size = block.size + 1) ∨
      ∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        (∀ i, source ≠ block.sources i) ∧
        ∃ index : Fin block.size,
          CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component source
              (block.tokens index.castSucc) := by
  rcases hobstruction with hterminal | hdirect | hcollision
  · obtain ⟨source, hsource, terminal, _hterminal, q, hnatural⟩ := hterminal
    have hnaturalIncident : CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component source
          (canonicalStableRawComponentNaturalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component source) :=
      canonicalStableRawComponentNaturalToken_incident
        ends m j k l zero hloop hjk hkl hk0 p hno component source
    by_cases hq : q = Fin.last block.size
    · rcases block.extendBySuccessor_or_repeat source hsource with
        hextended | ⟨r, hsuccessor⟩
      · exact Or.inl hextended
      · have hr : r ≠ Fin.last block.size := by
          intro hr
          apply canonicalStableRawComponentSuccessorToken_ne_natural
            ends m j k l zero hloop hjk hkl hk0 p hno component source
          exact hsuccessor.trans
            ((congrArg block.tokens (hr.trans hq.symm)).trans hnatural.symm)
        obtain ⟨index, hindex⟩ :=
          exists_fin_castSucc_eq_of_ne_last r hr
        right
        refine ⟨source, hsource, index, ?_⟩
        rw [hindex, ← hsuccessor]
        exact canonicalStableRawComponentSuccessorToken_incident
          ends m j k l zero hloop hjk hkl hk0 p hno component source
    · obtain ⟨index, hindex⟩ :=
        exists_fin_castSucc_eq_of_ne_last q hq
      right
      refine ⟨source, hsource, index, ?_⟩
      rw [hindex, ← hnatural]
      exact hnaturalIncident
  · obtain ⟨source, _direct, _hdirect, hsource, q, r, hqr,
        hnatural, hsuccessor⟩ := hdirect
    obtain ⟨index, hindex | hindex⟩ :=
      exists_fin_castSucc_eq_left_or_right_of_ne q r hqr
    · right
      refine ⟨source, hsource, index, ?_⟩
      rw [hindex, ← hnatural]
      exact canonicalStableRawComponentNaturalToken_incident
        ends m j k l zero hloop hjk hkl hk0 p hno component source
    · right
      refine ⟨source, hsource, index, ?_⟩
      rw [hindex, ← hsuccessor]
      exact canonicalStableRawComponentSuccessorToken_incident
        ends m j k l zero hloop hjk hkl hk0 p hno component source
  · obtain ⟨source, collision, hself, hsource, _q, r, s, hrs,
        _hnatural, hsourceToken, hownerToken⟩ := hcollision
    obtain ⟨index, hindex | hindex⟩ :=
      exists_fin_castSucc_eq_left_or_right_of_ne r s hrs
    · right
      refine ⟨source, hsource, index, ?_⟩
      rw [hindex, ← hsourceToken]
      apply (canonicalStableRawWitnessedStateTokenIncidence_iff
        ends m j k l zero hloop hjk hkl hk0 p _ source.1).2
      rw [hself]
      exact canonicalStableRawReferenceSourceLeftToken_stateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p
          collision.1.1.1 collision.1.1.2.2
    · right
      refine ⟨source, hsource, index, ?_⟩
      rw [hindex, ← hownerToken]
      apply (canonicalStableRawWitnessedStateTokenIncidence_iff
        ends m j k l zero hloop hjk hkl hk0 p _ source.1).2
      rw [hself]
      exact canonicalStableRawReferenceOwnerLeftToken_stateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p
          collision.1.1.1 collision.1.1.2.2



theorem
    CanonicalStableRawComponentRichIncidenceBlock.HasLocalizedObstruction.pivot_of_sizeMaximal
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hmax : ∀ other : CanonicalStableRawComponentRichIncidenceBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      other.size ≤ block.size)
    (hobstruction : block.HasLocalizedObstruction) :
    ∃ source : CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      ∃ hsource : ∀ i, source ≠ block.sources i,
        ∃ index : Fin block.size,
          ∃ hincident : CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component source
              (block.tokens index.castSucc),
            (∀ other, block.sources index ≠
              (block.pivot source hsource index hincident).sources other) := by
  rcases hobstruction.extension_or_pivot block with
    ⟨extended, hextended⟩ | ⟨source, hsource, index, hincident⟩
  · have hle := hmax extended
    omega
  · exact ⟨source, hsource, index, hincident,
      block.pivot_displaced_fresh source hsource index hincident⟩



theorem
    CanonicalStableRawComponentRichIncidenceBlock.PivotConfiguration.exists_step_of_not_closed
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hmax : ∀ other : CanonicalStableRawComponentRichIncidenceBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      other.size ≤ block.size)
    (config : block.PivotConfiguration)
    (hnotClosed : ¬ config.toBlock.IsClosed) :
    ∃ next : block.PivotConfiguration, config.Step next ∧ next ≠ config := by
  let current := config.toBlock
  have hmaxCurrent : ∀ other : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component,
      other.size ≤ current.size := by
    intro other
    simpa only [current,
      CanonicalStableRawComponentRichIncidenceBlock.PivotConfiguration.toBlock]
      using hmax other
  have hobstruction : current.HasLocalizedObstruction := by
    rcases current.closureStep_localized with
      hclosed | ⟨extended, hextended⟩ | hterminal | hdirect | hcollision
    · exact False.elim (hnotClosed hclosed)
    · have hle := hmax extended
      dsimp only [current,
        CanonicalStableRawComponentRichIncidenceBlock.PivotConfiguration.toBlock]
        at hextended
      exact False.elim (by omega)
    · exact Or.inl hterminal
    · exact Or.inr (Or.inl hdirect)
    · exact Or.inr (Or.inr hcollision)
  obtain ⟨source, hsource, index, hincident, _hdisplaced⟩ :=
    hobstruction.pivot_of_sizeMaximal current hmaxCurrent
  let pivoted := current.pivot source hsource index hincident
  let next : block.PivotConfiguration := ⟨pivoted.sources, pivoted.paired⟩
  refine ⟨next, ?_, ?_⟩
  · exact ⟨source, hsource, index, hincident, rfl⟩
  · intro heq
    have hvalue := congrArg
      (fun candidate : block.PivotConfiguration => candidate.1 index) heq
    apply hsource index
    exact (finiteEmbedding_replaceAt_same
      config.1 source hsource index).symm.trans hvalue




theorem
    CanonicalStableRawComponentRichIncidenceBlock.PivotConfiguration.Step.outputClassification
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    {current next : block.PivotConfiguration}
    (hstep : current.Step next) :
    ∃ source : CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      ∃ hsource : ∀ i, source ≠ current.1 i,
        ∃ index : Fin block.size,
          next.1 = finiteEmbedding_replaceAt
              current.1 source hsource index ∧
          ((∃ u : CanonicalStableRawExceptionalEdge
                ends m j k l zero hloop hjk hkl hk0 p,
              u.target = canonicalStableRawLeftTokenTarget
                  ends m j k l zero hloop hjk hkl hk0 p
                    (block.tokens index.castSucc).1 ∧
              CanonicalStableRawOwnerStableOutput
                  ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧
              canonicalStableRawTokenComponent
                  ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨
            ∃ u : CanonicalStableRawExceptionalEdge
                ends m j k l zero hloop hjk hkl hk0 p,
              u.target = canonicalStableRawLeftTokenTarget
                  ends m j k l zero hloop hjk hkl hk0 p
                    (block.tokens index.castSucc).1 ∧
              CanonicalStableRawOwnerAdvancingOutput
                  ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧
              canonicalStableRawTokenComponent
                  ends m j k l zero hloop hjk hkl hk0 p hno u = component) := by
  obtain ⟨source, hsource, index, hincident, hnext⟩ := hstep
  have holdIncident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (current.1 index) (block.tokens index.castSucc) := current.2 index
  have hclassification :=
    canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
      ends m j k l zero hloop hjk hkl hk0 p hno
        (block.tokens index.castSucc).1 source.1 (current.1 index).1
          hincident holdIncident
  refine ⟨source, hsource, index, hnext, ?_⟩
  rcases hclassification with heq | ⟨u, htarget, hstable, hcomponent, _⟩ |
      ⟨u, htarget, hadvancing, hcomponent, _⟩
  · exact False.elim (hsource index (Subtype.ext heq))
  · exact Or.inl ⟨u, htarget, hstable, hcomponent.trans source.2⟩
  · exact Or.inr ⟨u, htarget, hadvancing, hcomponent.trans source.2⟩


theorem
    CanonicalStableRawComponentRichIncidenceBlock.exists_rankSumMaximalPivotConfiguration
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    ∃ best : block.PivotConfiguration,
      ∀ other : block.PivotConfiguration, other.rankSum ≤ best.rankSum := by
  classical
  letI : Finite block.PivotConfiguration := Finite.of_injective
    (fun config : block.PivotConfiguration => config.1)
    (by
      intro first second heq
      exact Subtype.ext heq)
  letI : Fintype block.PivotConfiguration := Fintype.ofFinite _
  letI : Nonempty block.PivotConfiguration := ⟨block.basePivotConfiguration⟩
  exact exists_fintype_score_maximal
    CanonicalStableRawComponentRichIncidenceBlock.PivotConfiguration.rankSum



theorem
    CanonicalStableRawComponentRichIncidenceBlock.PivotConfiguration.Step.enteringRank_le_displaced_of_rankSumMaximal
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    {current next : block.PivotConfiguration}
    (hmax : ∀ other : block.PivotConfiguration,
      other.rankSum ≤ current.rankSum)
    (hstep : current.Step next) :
    ∃ source : CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      ∃ index : Fin block.size,
        canonicalStableRawSourceRank ends m j k l zero p source.1.source ≤
          canonicalStableRawSourceRank ends m j k l zero p
            (current.1 index).1.source := by
  classical
  obtain ⟨source, hsource, index, _hincident, hnext⟩ := hstep
  let oldRank := fun i : Fin block.size =>
    canonicalStableRawSourceRank ends m j k l zero p
      (current.1 i).1.source
  let newRank := fun i : Fin block.size =>
    canonicalStableRawSourceRank ends m j k l zero p
      (next.1 i).1.source
  let rest := ∑ i ∈ (Finset.univ.erase index), oldRank i
  have hnewIndex : newRank index =
      canonicalStableRawSourceRank ends m j k l zero p source.1.source := by
    dsimp only [newRank]
    rw [hnext, finiteEmbedding_replaceAt_same]
  have hrest : (∑ i ∈ (Finset.univ.erase index), newRank i) = rest := by
    apply Finset.sum_congr rfl
    intro i hi
    have hine : i ≠ index := Finset.ne_of_mem_erase hi
    dsimp only [newRank, oldRank]
    rw [hnext, finiteEmbedding_replaceAt_ne
      current.1 source hsource index i hine]
  have holdSum : current.rankSum = rest + oldRank index := by
    change (∑ i, oldRank i) = rest + oldRank index
    simpa only [rest] using
      (Finset.sum_erase_add Finset.univ oldRank
        (Finset.mem_univ index)).symm
  have hnewSum : next.rankSum = rest +
      canonicalStableRawSourceRank ends m j k l zero p source.1.source := by
    change (∑ i, newRank i) = rest +
      canonicalStableRawSourceRank ends m j k l zero p source.1.source
    calc
      (∑ i, newRank i) =
          (∑ i ∈ Finset.univ.erase index, newRank i) + newRank index :=
        (Finset.sum_erase_add Finset.univ newRank
          (Finset.mem_univ index)).symm
      _ = rest + newRank index := by rw [hrest]
      _ = rest + canonicalStableRawSourceRank
          ends m j k l zero p source.1.source := by rw [hnewIndex]
  have hle := hmax next
  rw [holdSum, hnewSum] at hle
  have hrank : canonicalStableRawSourceRank
      ends m j k l zero p source.1.source ≤ oldRank index := by
    omega
  exact ⟨source, index, by simpa only [oldRank] using hrank⟩




theorem
    CanonicalStableRawComponentRichIncidenceBlock.closedConfiguration_or_pivotCycle
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hmax : ∀ other : CanonicalStableRawComponentRichIncidenceBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      other.size ≤ block.size) :
    (∃ config : block.PivotConfiguration, config.toBlock.IsClosed) ∨
      ∃ size : Nat, 1 < size ∧
        ∃ cycle : Fin size ↪ block.PivotConfiguration,
          ∃ σ : Equiv.Perm (Fin size),
      ∀ i, (cycle i).Step (cycle (σ i)) := by
  classical
  letI : Finite block.PivotConfiguration := Finite.of_injective
    (fun config : block.PivotConfiguration => config.1)
    (by
      intro first second heq
      exact Subtype.ext heq)
  letI : Fintype block.PivotConfiguration := Fintype.ofFinite _
  by_cases hclosed : ∃ config : block.PivotConfiguration,
      config.toBlock.IsClosed
  · exact Or.inl hclosed
  · have hnotClosed : ∀ config : block.PivotConfiguration,
        ¬ config.toBlock.IsClosed := by
      intro config hconfig
      exact hclosed ⟨config, hconfig⟩
    let next : block.PivotConfiguration -> block.PivotConfiguration :=
      fun config => Classical.choose
        (config.exists_step_of_not_closed block hmax (hnotClosed config))
    have hnextStep : ∀ config : block.PivotConfiguration,
        config.Step (next config) := by
      intro config
      exact (Classical.choose_spec
        (config.exists_step_of_not_closed block hmax
          (hnotClosed config))).1
    have hnextNe : ∀ config : block.PivotConfiguration,
        next config ≠ config := by
      intro config
      exact (Classical.choose_spec
        (config.exists_step_of_not_closed block hmax
          (hnotClosed config))).2
    obtain ⟨size, hsize, cycle, σ, hcycle⟩ :=
      exists_function_cycleEmbedding next block.basePivotConfiguration
    have hsizeTwo : 1 < size := by
      have hsizeNe : size ≠ 1 := by
        intro hsizeOne
        have hnonempty : Nonempty (Fin size) := Fin.pos_iff_nonempty.mp hsize
        let i : Fin size := hnonempty.some
        have hsigma : σ i = i := by
          apply Fin.ext
          have hsigmaBound := (σ i).2
          have hiBound := i.2
          omega
        apply hnextNe (cycle i)
        calc
          next (cycle i) = cycle (σ i) := (hcycle i).symm
          _ = cycle i := congrArg cycle hsigma
      omega
    right
    refine ⟨size, hsizeTwo, cycle, σ, ?_⟩
    intro i
    rw [hcycle i]
    exact hnextStep (cycle i)



theorem
    canonicalStableRawComponent_referenceOwner_eq_selfOwnerReroute_of_sourceNormalized
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (state : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hself : state.1 = collision.1.1.1)
    (hnormalized :
      canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision =
        canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component state) :
    (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component collision).1 =
      canonicalStableRawSelfOwnerRerouteLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno
          collision.1.1.1 collision.1.1.2.2 := by
  have hraw := congrArg Subtype.val hnormalized
  change canonicalStableRawReferenceSourceLeftToken
      ends m j k l zero hloop hjk hkl hk0 p
        collision.1.1.1 collision.1.1.2.2 =
    canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno state.1 at hraw
  rw [hself] at hraw
  unfold canonicalStableRawStateLeftToken at hraw
  rw [dif_pos collision.1.1.2.2] at hraw
  exact canonicalStableRawReferenceOwnerLeftToken_eq_selfOwnerReroute
    ends m j k l zero hloop hjk hkl hk0 p hno
      collision.1.1.1 collision.1.1.2.2 hraw



theorem
    canonicalStableRawComponent_referenceOwner_eq_successor_of_sourceNormalized
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (state : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hself : state.1 = collision.1.1.1)
    (hnormalized :
      canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision =
        canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component state) :
    canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component collision =
      canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component state := by
  apply Subtype.ext
  have howner :=
    canonicalStableRawComponent_referenceOwner_eq_selfOwnerReroute_of_sourceNormalized
      ends m j k l zero hloop hjk hkl hk0 p hno component state collision
        hself hnormalized
  have hstateSelf : state.1.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p state.1.source := by
    rw [hself]
    exact collision.1.1.2.2
  unfold canonicalStableRawComponentSuccessorToken
  rw [dif_pos hstateSelf]
  simpa only [hself] using howner



theorem canonicalStableRawComponent_sourceNormalized_terminal_or_advancing
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (external : ↑sources)
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hself : external.1.1 = collision.1.1.1)
    (hnormalized :
      canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision =
        canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component external.1) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      CanonicalStableRawOwnerAdvancingStep
        ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1 := by
  rcases canonicalStableRawComponentCrossCollision_stable_or_advancing
      ends m j k l zero hloop hjk hkl hk0 p hno component collision with
    hstable | hadvancing
  · left
    let owner := canonicalStableRawComponentReferenceOwnerCollisionEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component collision
    have hownerMem : owner ∈ canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources :=
      canonicalStableRawComponent_referenceOwnerCollision_mem_tightNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          external collision hself
    have hownerEq : owner.1 = canonicalStableRawSelfOwnerRerouteLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno
          collision.1.1.1 collision.1.1.2.2 :=
      canonicalStableRawComponent_referenceOwner_eq_selfOwnerReroute_of_sourceNormalized
        ends m j k l zero hloop hjk hkl hk0 p hno component external.1
          collision hself hnormalized
    have hnonexceptional : ¬ CanonicalStableRawLeftTokenIsExceptional
        ends m j k l zero hloop hjk hkl hk0 p owner.1 := by
      rw [hownerEq]
      exact canonicalStableRawSelfOwnerReroute_not_exceptional_of_ownerStable
        ends m j k l zero hloop hjk hkl hk0 p hno
          collision.1.1.1 collision.1.1.2.2 hstable
    exact ⟨⟨owner, hnonexceptional⟩, hownerMem⟩
  · exact Or.inr hadvancing




theorem
    canonicalStableRawComponentTightSuccessorOther_normalizedAdvancingEdge
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (state : ↑sources)
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hself : state.1.1 = collision.1.1.1)
    (hnormalized :
      canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision =
        canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component state.1)
    (hadvancing : CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1) :
    let next := canonicalStableRawComponentTightSuccessorOther
      ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
    ∃ direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
      canonicalStableRawComponentForestStep
          ends m j k l zero hloop hjk hkl hk0 p hno component state.1 =
        Sum.inl direct ∧
      canonicalStableRawComponentReferenceOwnerCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision =
        canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component direct ∧
      CanonicalStableRawComponentIncident
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (next state).1
            (canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component direct) ∧
      canonicalStableRawSourceRank ends m j k l zero p direct.1.source <
        canonicalStableRawSourceRank ends m j k l zero p
          collision.1.1.1.source := by
  classical
  dsimp only
  let self := collision.1.1
  let selfState : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨self.1, self.2.1⟩
  have hstate : state.1 = selfState := by
    apply Subtype.ext
    exact hself
  let hexceptional :=
    canonicalStableRawComponentSuccessorToken_exceptional_of_advancing
      ends m j k l zero hloop hjk hkl hk0 p hno component self hadvancing
  let direct := canonicalStableRawComponentExceptionalSuccessorDirect
    ends m j k l zero hloop hjk hkl hk0 p hno component
      selfState hexceptional
  have hstepSelf : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component selfState =
      Sum.inl direct := by
    unfold canonicalStableRawComponentForestStep
    rw [dif_pos hexceptional]
  have hstep : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component state.1 =
      Sum.inl direct := by
    rw [hstate]
    exact hstepSelf
  have hdirectSuccessor :
      canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component direct =
        canonicalStableRawComponentSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component selfState :=
    canonicalStableRawComponentExceptionalSuccessorDirect_natural
      ends m j k l zero hloop hjk hkl hk0 p hno component
        selfState hexceptional
  have hownerSuccessor :=
    canonicalStableRawComponent_referenceOwner_eq_successor_of_sourceNormalized
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1
        collision hself hnormalized
  have hownerDirect :
      canonicalStableRawComponentReferenceOwnerCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision =
        canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component direct := by
    rw [hstate] at hownerSuccessor
    exact hownerSuccessor.trans hdirectSuccessor.symm
  let next := canonicalStableRawComponentTightSuccessorOther
    ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
  have hnext := canonicalStableRawComponentTightSuccessorOther_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component sources herase state
  have hnextDirect : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (next state).1
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component direct) := by
    change CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (next state).1
        (canonicalStableRawComponentSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component state.1) at hnext
    rw [hstate, ← hdirectSuccessor] at hnext
    exact hnext
  have hrank : canonicalStableRawSourceRank ends m j k l zero p
        direct.1.source <
      canonicalStableRawSourceRank ends m j k l zero p self.1.source :=
    canonicalStableRawComponentExceptionalSuccessorDirect_rank_lt_of_advancing
      ends m j k l zero hloop hjk hkl hk0 p hno component self hadvancing
  exact ⟨direct, hstep, hownerDirect, hnextDirect, hrank⟩





theorem
    canonicalStableRawComponentTightSuccessorOther_normalizedAdvancingSplit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (state : ↑sources)
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hself : state.1.1 = collision.1.1.1)
    (hnormalized :
      canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision =
        canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component state.1)
    (hadvancing : CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1) :
    let next := canonicalStableRawComponentTightSuccessorOther
      ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
    canonicalStableRawSourceRank ends m j k l zero p (next state).1.1.source <
        canonicalStableRawSourceRank ends m j k l zero p
          collision.1.1.1.source ∨
      ∃ direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        CanonicalStableRawOwnerAdvancingOutput
          ends m j k l zero hloop hjk hkl hk0 p (next state).1.1 direct.1 ∧
        Nonempty (StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)) ∧
        CanonicalStableRawComponentIncident
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (next state).1
            (canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component direct) ∧
        canonicalStableRawSourceRank ends m j k l zero p direct.1.source <
          canonicalStableRawSourceRank ends m j k l zero p
            collision.1.1.1.source := by
  classical
  dsimp only
  let next := canonicalStableRawComponentTightSuccessorOther
    ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
  obtain ⟨direct, _hstep, hownerDirect, hnextDirect, hrank⟩ :=
    canonicalStableRawComponentTightSuccessorOther_normalizedAdvancingEdge
      ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
        state collision hself hnormalized hadvancing
  have htokenSource :
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component direct).1.1 =
        direct.1.source := by
    change (canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1).1 = direct.1.source
    unfold canonicalStableRawStateLeftToken
    rw [dif_neg direct.2.2]
    unfold canonicalStableRawDirectLeftToken
    rfl
  change CanonicalStableRawWitnessedStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component direct).1
        (next state).1.1 at hnextDirect
  rcases hnextDirect.1.1 with hsource | howner
  · left
    have hdirectSource : direct.1.source = (next state).1.1.source :=
      htokenSource.symm.trans hsource
    rw [← hdirectSource]
    exact hrank
  · right
    have hownerOutput : CanonicalStableRawOwnerAdvancingOutput
        ends m j k l zero hloop hjk hkl hk0 p (next state).1.1 direct.1 := by
      change direct.1.source.1 = canonicalStableRawPreferredRightBase
        ends m j k l zero hloop hjk hkl hk0 p (next state).1.1.target
      exact congrArg Subtype.val (htokenSource.symm.trans howner)
    let second : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component) :=
      ⟨(collision, direct), hownerDirect⟩
    exact ⟨direct, hownerOutput, ⟨second⟩, hnextDirect, hrank⟩




theorem
    canonicalStableRawComponentTightSuccessorOther_secondCharge_of_normalizedAdvancing_rankNondrop
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (state : ↑sources)
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hself : state.1.1 = collision.1.1.1)
    (hnormalized :
      canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision =
        canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component state.1)
    (hadvancing : CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1)
    (hnondrop :
      let next := canonicalStableRawComponentTightSuccessorOther
        ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
      ¬ canonicalStableRawSourceRank ends m j k l zero p
            (next state).1.1.source <
          canonicalStableRawSourceRank ends m j k l zero p
            collision.1.1.1.source) :
    let next := canonicalStableRawComponentTightSuccessorOther
      ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
    ∃ direct : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      CanonicalStableRawOwnerAdvancingOutput
          ends m j k l zero hloop hjk hkl hk0 p (next state).1.1 direct.1 ∧
      Nonempty (StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)) ∧
      CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component
          (next state).1
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component direct) ∧
      canonicalStableRawSourceRank ends m j k l zero p direct.1.source <
        canonicalStableRawSourceRank ends m j k l zero p
          collision.1.1.1.source := by
  dsimp only at hnondrop ⊢
  rcases
      canonicalStableRawComponentTightSuccessorOther_normalizedAdvancingSplit
        ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
          state collision hself hnormalized hadvancing with
    hdrop | hexit
  · exact False.elim (hnondrop hdrop)
  · exact hexit




theorem canonicalStableRawComponent_tightState_terminal_or_crossCollision_or_direct
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (state : ↑sources) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      (∃ collision : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        state.1.1 = collision.1.1.1 ∧
        canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component
              collision.1.2 ∈
          canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      ∃ direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        state.1.1 = direct.1 := by
  classical
  let token := canonicalStableRawComponentNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component state.1
  have htokenMem : token ∈ canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources :=
    (canonicalStableRawComponentTightNaturalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component sources state).2
  by_cases hself : state.1.1.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p state.1.1.source
  · let self : CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨state.1.1, state.1.2, hself⟩
    by_cases hexceptional : CanonicalStableRawLeftTokenIsExceptional
        ends m j k l zero hloop hjk hkl hk0 p token.1
    · let exceptionalToken : CanonicalStableRawComponentExceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
        ⟨token, hexceptional⟩
      let direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
        (canonicalStableRawComponentDirectStateEquivExceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component).symm
            exceptionalToken
      have hdirectToken :
          canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component direct =
            token := by
        exact congrArg Subtype.val
          ((canonicalStableRawComponentDirectStateEquivExceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component).apply_symm_apply
              exceptionalToken)
      have hselfToken :
          canonicalStableRawComponentSelfEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component self =
            token := by
        apply Subtype.ext
        change canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno self.1 =
          canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno state.1.1
        rfl
      let collision : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component) :=
        ⟨(self, direct), hselfToken.trans hdirectToken.symm⟩
      exact Or.inr (Or.inl ⟨collision, rfl, hdirectToken ▸ htokenMem⟩)
    · let terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
        ⟨token, hexceptional⟩
      exact Or.inl ⟨terminal, htokenMem⟩
  · let direct : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨state.1.1, state.1.2, hself⟩
    exact Or.inr (Or.inr ⟨direct, rfl⟩)




theorem
    canonicalStableRawComponent_tightCrossCollision_localDischarge
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (state : ↑sources)
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hself : state.1.1 = collision.1.1.1) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      Nonempty (Fin 3 ↪
        ↑(canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨
      ∃ second : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component second.1.2 ∈
          canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
  classical
  let naturalToken := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources state
  let sourceToken :
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) :=
    ⟨canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component collision,
      canonicalStableRawComponent_referenceSourceCollision_mem_tightNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          state collision hself⟩
  let ownerToken :
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) :=
    ⟨canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component collision,
      canonicalStableRawComponent_referenceOwnerCollision_mem_tightNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          state collision hself⟩
  by_cases hnormalizedTight : sourceToken = naturalToken
  · have hnormalized :
        canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component collision =
          canonicalStableRawComponentNaturalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component state.1 :=
      congrArg Subtype.val hnormalizedTight
    rcases canonicalStableRawComponent_sourceNormalized_terminal_or_advancing
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          state collision hself hnormalized with
      hterminal | hadvancing
    · exact Or.inl hterminal
    · obtain ⟨direct, _hstep, hownerDirect, hincident, _hrank⟩ :=
        canonicalStableRawComponentTightSuccessorOther_normalizedAdvancingEdge
          ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
            state collision hself hnormalized hadvancing
      let second : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component) :=
        ⟨(collision, direct), hownerDirect⟩
      right
      right
      refine ⟨second, ?_⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,
        (canonicalStableRawComponentTightSuccessorOther
          ends m j k l zero hloop hjk hkl hk0 p hno component
            sources herase state).1,
        (canonicalStableRawComponentTightSuccessorOther
          ends m j k l zero hloop hjk hkl hk0 p hno component
            sources herase state).2,
        hincident⟩
  · have hsourceOwner : sourceToken ≠ ownerToken := by
      intro heq
      apply canonicalStableRawComponent_referenceSourceCollision_ne_ownerCollision
        ends m j k l zero hloop hjk hkl hk0 p hno component collision
      exact congrArg Subtype.val heq
    have hnatural : naturalToken.1 =
        canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.1 := by
      apply Subtype.ext
      change canonicalStableRawStateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno state.1.1 =
        canonicalStableRawStateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1
      rw [hself]
    have hnaturalOwner : naturalToken ≠ ownerToken := by
      intro heq
      apply canonicalStableRawComponentReferenceOwnerCollisionEmbedding_ne_self
        ends m j k l zero hloop hjk hkl hk0 p hno component
          collision collision.1.1
      exact (congrArg Subtype.val heq).symm.trans hnatural
    exact Or.inr (Or.inl
      (finiteEmbedding_three_of_pairwise_ne sourceToken naturalToken ownerToken
        hnormalizedTight hsourceOwner hnaturalOwner))




theorem canonicalStableRawComponent_distinctTightStates_localDischarge
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (x y : ↑sources) (hne : x ≠ y) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      Nonempty (Fin 3 ↪
        ↑(canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨
      (∃ second : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component second.1.2 ∈
          canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      ∃ first second : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        first ≠ second ∧ x.1.1 = first.1 ∧ y.1.1 = second.1 := by
  classical
  rcases canonicalStableRawComponent_tightState_terminal_or_crossCollision_or_direct
      ends m j k l zero hloop hjk hkl hk0 p hno component sources x with
    hterminal | ⟨collision, hself, _hdirectMem⟩ | ⟨first, hfirst⟩
  · exact Or.inl hterminal
  · rcases canonicalStableRawComponent_tightCrossCollision_localDischarge
        ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
          x collision hself with hterminal | hthree | hsecond
    · exact Or.inl hterminal
    · exact Or.inr (Or.inl hthree)
    · exact Or.inr (Or.inr (Or.inl hsecond))
  · rcases canonicalStableRawComponent_tightState_terminal_or_crossCollision_or_direct
        ends m j k l zero hloop hjk hkl hk0 p hno component sources y with
      hterminal | ⟨collision, hself, _hdirectMem⟩ | ⟨second, hsecond⟩
    · exact Or.inl hterminal
    · rcases canonicalStableRawComponent_tightCrossCollision_localDischarge
          ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
            y collision hself with hterminal | hthree | hsecondCharge
      · exact Or.inl hterminal
      · exact Or.inr (Or.inl hthree)
      · exact Or.inr (Or.inr (Or.inl hsecondCharge))
    · refine Or.inr (Or.inr (Or.inr ⟨first, second, ?_, hfirst, hsecond⟩))
      intro heq
      apply hne
      apply Subtype.ext
      apply Subtype.ext
      exact hfirst.trans ((congrArg
        (fun direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component => direct.1)
            heq).trans hsecond.symm)




theorem
    exists_canonicalStableRawComponent_tightSuccessorCycle_localDischarge
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : source ∈ sources)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card)
    (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      smaller ⊂ sources ->
        smaller.card ≤
          (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              smaller).card) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      ∃ size : Nat, 0 < size ∧
        ∃ cycle : Fin size ↪ ↑sources,
          ∃ directs : Fin size ↪ CanonicalStableRawComponentDirectState
              ends m j k l zero hloop hjk hkl hk0 p hno component,
            ∃ tokens : Fin size ↪
                ↑(canonicalStableRawComponentIncidentNeighborhood
                  ends m j k l zero hloop hjk hkl hk0 p hno component sources),
              ∃ external : ↑sources,
                (∀ q, external ≠ cycle q) ∧
                (∀ i,
                  canonicalStableRawComponentDirectEmbedding
                      ends m j k l zero hloop hjk hkl hk0 p hno component
                        (directs i) = (tokens i).1) ∧
                (Nonempty (Fin (size + 1) ↪
                    ↑(canonicalStableRawComponentIncidentNeighborhood
                      ends m j k l zero hloop hjk hkl hk0 p hno component
                        sources)) ∨
                  (∃ i, external.1.1 = (directs i).1) ∨
                  (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
                        ends m j k l zero hloop hjk hkl hk0 p hno component,
                      terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
                        ends m j k l zero hloop hjk hkl hk0 p hno component
                          sources) ∨
                  Nonempty (Fin 3 ↪
                    ↑(canonicalStableRawComponentIncidentNeighborhood
                      ends m j k l zero hloop hjk hkl hk0 p hno component
                        sources)) ∨
                  ∃ second : StatMech.FrontierA.crossCollision
                      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
                        ends m j k l zero hloop hjk hkl hk0 p hno component)
                      (canonicalStableRawComponentDirectEmbedding
                        ends m j k l zero hloop hjk hkl hk0 p hno component),
                    canonicalStableRawComponentDirectEmbedding
                        ends m j k l zero hloop hjk hkl hk0 p hno component
                          second.1.2 ∈
                      canonicalStableRawComponentIncidentNeighborhood
                        ends m j k l zero hloop hjk hkl hk0 p hno component
                          sources) := by
  classical
  rcases exists_canonicalStableRawComponent_tightSuccessorCycle_externalDischarge
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources source hsource htight hproper with
    hterminal | ⟨size, hsize, cycle, directs, tokens, external,
      hexternal, hdirect, hboundary⟩
  · exact Or.inl hterminal
  · right
    refine ⟨size, hsize, cycle, directs, tokens, external,
      hexternal, hdirect, ?_⟩
    rcases hboundary with hfresh | heq | ⟨collision, hself⟩
    · exact Or.inl hfresh
    · exact Or.inr (Or.inl heq)
    · rcases canonicalStableRawComponent_tightCrossCollision_localDischarge
          ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
            external collision hself with
        hterminal | hthree | hsecond
      · exact Or.inr (Or.inr (Or.inl hterminal))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hthree)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hsecond)))





theorem
    exists_canonicalStableRawComponent_minimalRankNondropDischarge_of_deficit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ sources : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      ∃ herase : ∀ source ∈ sources,
        canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (sources.erase source) =
          canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources,
        sources.Nonempty ∧
        (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              sources).card + 1 = sources.card ∧
        (∀ smaller : Finset (CanonicalStableRawComponentState
            ends m j k l zero hloop hjk hkl hk0 p hno component),
          smaller ⊂ sources ->
            smaller.card ≤
              (canonicalStableRawComponentIncidentNeighborhood
                ends m j k l zero hloop hjk hkl hk0 p hno component
                  smaller).card) ∧
        ∃ state : ↑sources,
          (let next := canonicalStableRawComponentTightSuccessorOther
            ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
          ¬ canonicalStableRawSourceRank ends m j k l zero p
                (next state).1.1.source <
              canonicalStableRawSourceRank ends m j k l zero p
                state.1.1.source) ∧
          ((∃ terminal : CanonicalStableRawComponentNonexceptionalToken
                ends m j k l zero hloop hjk hkl hk0 p hno component,
              terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
                  ends m j k l zero hloop hjk hkl hk0 p hno component sources ∧
              ∃ size : Nat, 0 < size ∧
                Nonempty (Fin size ↪
                  CanonicalStableRawComponentDirectState
                    ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
                Nonempty (Fin (size + 1) ↪
                  CanonicalStableRawComponentToken
                    ends m j k l zero hloop hjk hkl hk0 p hno component)) ∨
            (∃ collision : StatMech.FrontierA.crossCollision
                (canonicalStableRawComponentSelfEmbedding
                  ends m j k l zero hloop hjk hkl hk0 p hno component)
                (canonicalStableRawComponentDirectEmbedding
                  ends m j k l zero hloop hjk hkl hk0 p hno component),
              state.1.1 = collision.1.1.1 ∧
              canonicalStableRawComponentDirectEmbedding
                    ends m j k l zero hloop hjk hkl hk0 p hno component
                      collision.1.2 ∈
                canonicalStableRawComponentIncidentNeighborhood
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    sources ∧
              Nonempty (Fin 3 ↪
                ↑(canonicalStableRawComponentIncidentNeighborhood
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    sources)) ∧
              (let Direct := CanonicalStableRawComponentDirectState
                  ends m j k l zero hloop hjk hkl hk0 p hno component
               let Token := CanonicalStableRawComponentToken
                  ends m j k l zero hloop hjk hkl hk0 p hno component
               let advance := canonicalStableRawComponentDirectForestAdvance
                  ends m j k l zero hloop hjk hkl hk0 p hno component
               (∃ n ≤ Nat.card Direct,
                  ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
                      ends m j k l zero hloop hjk hkl hk0 p hno component,
                    canonicalStableRawComponentForestStep
                        ends m j k l zero hloop hjk hkl hk0 p hno component
                          ⟨(advance^[n] collision.1.2).1,
                            (advance^[n] collision.1.2).2.1⟩ =
                      Sum.inr terminal) ∨
                ∃ size : Nat, 0 < size ∧
                  Nonempty (Fin size ↪ Direct) ∧
                  Nonempty (Fin size ↪ Token))) ∨
            (∃ second : StatMech.FrontierA.crossCollision
                (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
                  ends m j k l zero hloop hjk hkl hk0 p hno component)
                (canonicalStableRawComponentDirectEmbedding
                  ends m j k l zero hloop hjk hkl hk0 p hno component),
              canonicalStableRawComponentDirectEmbedding
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    second.1.2 ∈
                canonicalStableRawComponentIncidentNeighborhood
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    sources ∧
              ∃ size : Nat, 0 < size ∧
                Nonempty (Fin size ↪
                  CanonicalStableRawComponentDirectState
                    ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
                Nonempty (Fin (size + 1) ↪
                  CanonicalStableRawComponentToken
                    ends m j k l zero hloop hjk hkl hk0 p hno component)) ∨
            ∃ direct : CanonicalStableRawComponentDirectState
                ends m j k l zero hloop hjk hkl hk0 p hno component,
              state.1.1 = direct.1 ∧
              (let Direct := CanonicalStableRawComponentDirectState
                  ends m j k l zero hloop hjk hkl hk0 p hno component
               let Token := CanonicalStableRawComponentToken
                  ends m j k l zero hloop hjk hkl hk0 p hno component
               let advance := canonicalStableRawComponentDirectForestAdvance
                  ends m j k l zero hloop hjk hkl hk0 p hno component
               (∃ n ≤ Nat.card Direct,
                  ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
                      ends m j k l zero hloop hjk hkl hk0 p hno component,
                    canonicalStableRawComponentForestStep
                        ends m j k l zero hloop hjk hkl hk0 p hno component
                          ⟨(advance^[n] direct).1,
                            (advance^[n] direct).2.1⟩ = Sum.inr terminal) ∨
                ∃ size : Nat, 0 < size ∧
                  Nonempty (Fin size ↪ Direct) ∧
                  Nonempty (Fin size ↪ Token))) := by
  classical
  obtain ⟨sources, herase, hnonempty, htight, hproper, state, hnondrop⟩ :=
    exists_canonicalStableRawComponent_minimalTightRankNondrop_of_deficit
      ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit
  refine ⟨sources, herase, hnonempty, htight, hproper, state, hnondrop, ?_⟩
  have strictOfTerminal
      (terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) :
      ∃ size : Nat, 0 < size ∧
        Nonempty (Fin size ↪ CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
        Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) := by
    have hdirectGt := canonicalStableRawComponent_direct_card_gt_self_of_deficit
      ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit
    have hdirectPos : 0 < Nat.card (CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
      omega
    let start : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      (Nat.card_pos_iff.mp hdirectPos).1.some
    exact exists_canonicalStableRawComponentDirect_strictTokenBlock_of_available
      ends m j k l zero hloop hjk hkl hk0 p hno component start terminal
  rcases canonicalStableRawComponent_tightState_terminal_or_crossCollision_or_direct
      ends m j k l zero hloop hjk hkl hk0 p hno component sources state with
    hterminal | hcollision | hdirect
  · obtain ⟨terminal, hterminalMem⟩ := hterminal
    exact Or.inl ⟨terminal, hterminalMem, strictOfTerminal terminal⟩
  · obtain ⟨collision, hself, hdirectMem⟩ := hcollision
    rcases canonicalStableRawComponent_tightCrossCollision_localDischarge
        ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
          state collision hself with
      hterminal | hthree | hsecond
    · obtain ⟨terminal, hterminalMem⟩ := hterminal
      exact Or.inl ⟨terminal, hterminalMem, strictOfTerminal terminal⟩
    · refine Or.inr (Or.inl
        ⟨collision, hself, hdirectMem, hthree, ?_⟩)
      exact exists_canonicalStableRawComponentDirect_terminal_or_balancedBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.2
    · obtain ⟨second, hsecondMem⟩ := hsecond
      refine Or.inr (Or.inr (Or.inl
        ⟨second, hsecondMem, ?_⟩))
      exact exists_canonicalStableRawComponentSecondCollision_strictTokenBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component second
  · obtain ⟨direct, hstateDirect⟩ := hdirect
    refine Or.inr (Or.inr (Or.inr
      ⟨direct, hstateDirect, ?_⟩))
    exact exists_canonicalStableRawComponentDirect_terminal_or_balancedBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component direct



theorem canonicalStableRawComponent_tightCrossCollision_twoAlternateTokenEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (external : ↑sources)
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hself : external.1.1 = collision.1.1.1) :
    Nonempty (Fin 2 ↪
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources)) := by
  let sourceToken :
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) :=
    ⟨canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component collision,
      canonicalStableRawComponent_referenceSourceCollision_mem_tightNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          external collision hself⟩
  let ownerToken :
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) :=
    ⟨canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component collision,
      canonicalStableRawComponent_referenceOwnerCollision_mem_tightNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          external collision hself⟩
  let block : Fin 1 ↪
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) :=
    ⟨fun _ => sourceToken, fun x y _ => Subsingleton.elim x y⟩
  have hfresh : ∀ i, ownerToken ≠ block i := by
    intro i heq
    apply canonicalStableRawComponent_referenceSourceCollision_ne_ownerCollision
      ends m j k l zero hloop hjk hkl hk0 p hno component collision
    exact congrArg Subtype.val heq.symm
  simpa only [Nat.reduceAdd] using
    (finiteEmbedding_add_fresh 1 block ownerToken hfresh)




theorem
    canonicalStableRawComponent_tightCrossCollision_sourceNormalized_or_threeTokens
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (external : ↑sources)
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hself : external.1.1 = collision.1.1.1) :
    canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision =
        canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component external.1 ∨
      Nonempty (Fin 3 ↪
        ↑(canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)) := by
  classical
  let naturalToken := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources external
  let sourceToken :
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) :=
    ⟨canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component collision,
      canonicalStableRawComponent_referenceSourceCollision_mem_tightNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          external collision hself⟩
  let ownerToken :
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) :=
    ⟨canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component collision,
      canonicalStableRawComponent_referenceOwnerCollision_mem_tightNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          external collision hself⟩
  by_cases hnormalized : sourceToken = naturalToken
  · left
    exact congrArg Subtype.val hnormalized
  · right
    have hsourceOwner : sourceToken ≠ ownerToken := by
      intro heq
      apply canonicalStableRawComponent_referenceSourceCollision_ne_ownerCollision
        ends m j k l zero hloop hjk hkl hk0 p hno component collision
      exact congrArg Subtype.val heq
    have hnatural : naturalToken.1 =
        canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.1 := by
      apply Subtype.ext
      change canonicalStableRawStateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno external.1.1 =
        canonicalStableRawStateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1
      rw [hself]
    have hnaturalOwner : naturalToken ≠ ownerToken := by
      intro heq
      apply canonicalStableRawComponentReferenceOwnerCollisionEmbedding_ne_self
        ends m j k l zero hloop hjk hkl hk0 p hno component
          collision collision.1.1
      exact (congrArg Subtype.val heq).symm.trans hnatural
    exact finiteEmbedding_three_of_pairwise_ne sourceToken naturalToken ownerToken
      hnormalized hsourceOwner hnaturalOwner



theorem
    canonicalStableRawComponent_tightCrossCollision_terminal_or_advancing_or_threeTokens
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (external : ↑sources)
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hself : external.1.1 = collision.1.1.1) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      CanonicalStableRawOwnerAdvancingStep
          ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1 ∨
        Nonempty (Fin 3 ↪
          ↑(canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources)) := by
  rcases
      canonicalStableRawComponent_tightCrossCollision_sourceNormalized_or_threeTokens
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          external collision hself with
    hnormalized | hthree
  · rcases canonicalStableRawComponent_sourceNormalized_terminal_or_advancing
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          external collision hself hnormalized with
      hterminal | hadvancing
    · exact Or.inl hterminal
    · exact Or.inr (Or.inl hadvancing)
  · exact Or.inr (Or.inr hthree)




theorem
    canonicalStableRawComponent_tightCrossCollision_terminal_or_strictBlock_or_second
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (size : Nat)
    (directs : Fin size ↪ CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (tokens : Fin size ↪
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources))
    (hdirect : ∀ i,
      canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component (directs i) =
        (tokens i).1)
    (external : ↑sources)
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hself : external.1.1 = collision.1.1.1) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      Nonempty (Fin (size + 1) ↪
        ↑(canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨
      Nonempty (StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)) := by
  classical
  let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  let first := canonicalStableRawComponentReferenceOwnerCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component collision
  have hfirst : first ∈ canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources :=
    canonicalStableRawComponent_referenceOwnerCollision_mem_tightNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources external collision hself
  let tightFirst : TightToken := ⟨first, hfirst⟩
  by_cases hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p first.1
  · by_cases hfresh : ∀ i, tightFirst ≠ tokens i
    · exact Or.inr (Or.inl
        (finiteEmbedding_add_fresh size tokens tightFirst hfresh))
    · push_neg at hfresh
      obtain ⟨i, hi⟩ := hfresh
      let second : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component) :=
        ⟨(collision, directs i), by
          change first = canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component (directs i)
          exact (congrArg Subtype.val hi).trans (hdirect i).symm⟩
      exact Or.inr (Or.inr ⟨second⟩)
  · let terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨first, hexceptional⟩
    exact Or.inl ⟨terminal, hfirst⟩



theorem canonicalStableRawComponentTightHoleMoveAcross_classification
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (state : StatMech.FrontierA.RelationPartialMatching.HoleState
      (fun (tightState : ↑sources)
          (tightToken : ↑(canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources)) =>
        CanonicalStableRawComponentIncident
          ends m j k l zero hloop hjk hkl hk0 p hno component
            tightState.1 tightToken.1))
    (token : ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources))
    (hincident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        state.hole.1 token.1) :
    let moved := state.moveAcross token hincident
    state.hole.1 ≠ moved.hole.1 ∧
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p token.1 ∧
        (CanonicalStableRawOwnerStableOutput
            ends m j k l zero hloop hjk hkl hk0 p state.hole.1 u ∨
          CanonicalStableRawOwnerAdvancingOutput
            ends m j k l zero hloop hjk hkl hk0 p state.hole.1 u) ∧
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  classical
  dsimp only
  let moved := state.moveAcross token hincident
  have hne : state.hole ≠ moved.hole :=
    state.hole_ne_moveAcross_hole token hincident
  have hneRaw : state.hole.1 ≠ moved.hole.1 := by
    intro heq
    exact hne (Subtype.ext heq)
  have hnext : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        moved.hole.1 token.1 :=
    state.matching.related
      (state.matching_apply_moveAcross_hole token hincident)
  have hclassification :=
    canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
      ends m j k l zero hloop hjk hkl hk0 p hno
        token.1 state.hole.1 moved.hole.1 hincident hnext
  refine ⟨hneRaw, ?_⟩
  rcases hclassification with heq | hstable | hadvancing
  · exact False.elim (hneRaw (Subtype.ext heq))
  · exact ⟨hstable.choose, hstable.choose_spec.1,
      Or.inl hstable.choose_spec.2.1,
      hstable.choose_spec.2.2.1.trans state.hole.1.2⟩
  · exact ⟨hadvancing.choose, hadvancing.choose_spec.1,
      Or.inr hadvancing.choose_spec.2.1,
      hadvancing.choose_spec.2.2.1.trans state.hole.1.2⟩




theorem canonicalStableRawComponentTightHoleMove_classification
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (state : StatMech.FrontierA.RelationPartialMatching.HoleState
      (fun (tightState : ↑sources)
          (tightToken : ↑(canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources)) =>
        CanonicalStableRawComponentIncident
          ends m j k l zero hloop hjk hkl hk0 p hno component
            tightState.1 tightToken.1)) :
    let natural := canonicalStableRawComponentTightNaturalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
    let hnatural := canonicalStableRawComponentTightNaturalToken_incident
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
    let moved := state.move natural hnatural
    state.hole.1 ≠ moved.hole.1 ∧
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p
            (natural state.hole).1.1 ∧
        (CanonicalStableRawOwnerStableOutput
            ends m j k l zero hloop hjk hkl hk0 p state.hole.1.1 u ∨
          CanonicalStableRawOwnerAdvancingOutput
            ends m j k l zero hloop hjk hkl hk0 p state.hole.1.1 u) ∧
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  classical
  dsimp only
  let natural := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  let hnatural := canonicalStableRawComponentTightNaturalToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  let moved := state.move natural hnatural
  have hne : state.hole ≠ moved.hole :=
    state.hole_ne_move_hole natural hnatural
  have hneRaw : state.hole.1 ≠ moved.hole.1 := by
    intro heq
    exact hne (Subtype.ext heq)
  have hcurrent : CanonicalStableRawWitnessedStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        (natural state.hole).1.1 state.hole.1.1 :=
    hnatural state.hole
  have hnext : CanonicalStableRawWitnessedStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        (natural state.hole).1.1 moved.hole.1.1 := by
    exact state.matching.related
      (state.matching_apply_move_hole natural hnatural)
  have hclassification :=
    canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
      ends m j k l zero hloop hjk hkl hk0 p hno
        (natural state.hole).1.1 state.hole.1.1 moved.hole.1.1
          hcurrent hnext
  refine ⟨hneRaw, ?_⟩
  rcases hclassification with heq | hstable | hadvancing
  · exact False.elim (hneRaw (Subtype.ext heq))
  · exact ⟨hstable.choose, hstable.choose_spec.1,
      Or.inl hstable.choose_spec.2.1,
      hstable.choose_spec.2.2.1.trans state.hole.1.2⟩
  · exact ⟨hadvancing.choose, hadvancing.choose_spec.1,
      Or.inr hadvancing.choose_spec.2.1,
      hadvancing.choose_spec.2.2.1.trans state.hole.1.2⟩





theorem exists_canonicalStableRawTightComponentSuccessorCollision
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    let incident : ↑sources -> TightToken -> Prop := fun state token =>
      CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component
          state.1 token.1
    let successor := canonicalStableRawComponentTightSuccessorToken
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
    let hsuccessor := canonicalStableRawComponentTightSuccessorToken_incident
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
    ∃ state : StatMech.FrontierA.RelationPartialMatching.HoleState incident,
      state.hole.1 ≠ (state.move successor hsuccessor).hole.1 ∧
        successor state.hole =
          successor (state.move successor hsuccessor).hole := by
  classical
  dsimp only
  let TightState := ↑sources
  let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  let incident : TightState -> TightToken -> Prop := fun state token =>
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1
  let successor := canonicalStableRawComponentTightSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  let hsuccessor := canonicalStableRawComponentTightSuccessorToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  have hcard : Fintype.card TightToken < Fintype.card TightState := by
    simpa only [TightToken, TightState, Fintype.card_coe] using
      (show (canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources).card <
        sources.card by omega)
  obtain ⟨state, hne, heq⟩ :=
    StatMech.FrontierA.RelationPartialMatching.exists_maximalNatural_holeState_collision
      incident successor hsuccessor hcard
  refine ⟨state, ?_, heq⟩
  intro hraw
  exact hne (Subtype.ext hraw)



theorem canonicalStableRawComponentForestStep_eq_of_tightSuccessorToken_eq
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (x y : ↑sources)
    (hxy : canonicalStableRawComponentTightSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component sources x =
      canonicalStableRawComponentTightSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component sources y) :
    canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component x.1 =
      canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component y.1 := by
  let tokenEquiv := canonicalStableRawComponentDirectSumNonexceptionalEquivToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  apply tokenEquiv.injective
  have hx := canonicalStableRawComponentForestStep_token
    ends m j k l zero hloop hjk hkl hk0 p hno component x.1
  have hy := canonicalStableRawComponentForestStep_token
    ends m j k l zero hloop hjk hkl hk0 p hno component y.1
  have htoken : canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component x.1 =
      canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component y.1 :=
    congrArg Subtype.val hxy
  have hx' : tokenEquiv (canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component x.1) =
      canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component x.1 := by
    cases hstep : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component x.1 with
    | inl direct =>
        rw [hstep] at hx
        simpa [tokenEquiv,
          canonicalStableRawComponentDirectSumNonexceptionalEquivToken] using hx
    | inr terminal =>
        rw [hstep] at hx
        simpa [tokenEquiv,
          canonicalStableRawComponentDirectSumNonexceptionalEquivToken] using hx
  have hy' : tokenEquiv (canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component y.1) =
      canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component y.1 := by
    cases hstep : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component y.1 with
    | inl direct =>
        rw [hstep] at hy
        simpa [tokenEquiv,
          canonicalStableRawComponentDirectSumNonexceptionalEquivToken] using hy
    | inr terminal =>
        rw [hstep] at hy
        simpa [tokenEquiv,
          canonicalStableRawComponentDirectSumNonexceptionalEquivToken] using hy
  exact hx'.trans (htoken.trans hy'.symm)



theorem canonicalStableRawComponentForestStepMerger_of_alternatingPathRepeat
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (size : Nat) (path : Fin (size + 1) ↪ ↑sources)
    (tokens : Fin size ↪
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources))
    (htransition : ∀ i, tokens i =
      canonicalStableRawComponentTightSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          (path i.castSucc))
    (index : Fin size)
    (hrepeat :
      canonicalStableRawComponentTightSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component sources
            (path (Fin.last size)) =
        tokens index) :
    (path (Fin.last size)).1 ≠ (path index.castSucc).1 ∧
      canonicalStableRawComponentForestStep
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (path (Fin.last size)).1 =
        canonicalStableRawComponentForestStep
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (path index.castSucc).1 := by
  have hstatesNe : path (Fin.last size) ≠ path index.castSucc := by
    intro heq
    exact Fin.castSucc_ne_last index (path.injective heq).symm
  refine ⟨fun hraw => hstatesNe (Subtype.ext hraw), ?_⟩
  apply canonicalStableRawComponentForestStep_eq_of_tightSuccessorToken_eq
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  exact hrepeat.trans (htransition index)




theorem canonicalStableRawComponentForestStepMerger_localizedOutput
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (x y : ↑sources)
    (hmerge : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component x.1 =
      canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component y.1) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources ∧
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component x.1 =
          Sum.inr terminal ∧
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component y.1 =
          Sum.inr terminal) ∨
      ∃ direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component direct ∈
          canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources ∧
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component x.1 =
          Sum.inl direct ∧
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component y.1 =
          Sum.inl direct := by
  cases hx : canonicalStableRawComponentForestStep
      ends m j k l zero hloop hjk hkl hk0 p hno component x.1 with
  | inl direct =>
      have hy : canonicalStableRawComponentForestStep
          ends m j k l zero hloop hjk hkl hk0 p hno component y.1 =
          Sum.inl direct := hmerge.symm.trans hx
      right
      refine ⟨direct, ?_, rfl, hy⟩
      have htoken := canonicalStableRawComponentForestStep_token
        ends m j k l zero hloop hjk hkl hk0 p hno component x.1
      rw [hx] at htoken
      have htoken' : canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component direct =
          canonicalStableRawComponentSuccessorToken
            ends m j k l zero hloop hjk hkl hk0 p hno component x.1 := by
        simpa only using htoken
      rw [htoken']
      exact (canonicalStableRawComponentTightSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component sources x).2
  | inr terminal =>
      have hy : canonicalStableRawComponentForestStep
          ends m j k l zero hloop hjk hkl hk0 p hno component y.1 =
          Sum.inr terminal := hmerge.symm.trans hx
      left
      refine ⟨terminal, ?_, rfl, hy⟩
      have htoken := canonicalStableRawComponentForestStep_token
        ends m j k l zero hloop hjk hkl hk0 p hno component x.1
      rw [hx] at htoken
      have htoken' : terminal.1 =
          canonicalStableRawComponentSuccessorToken
            ends m j k l zero hloop hjk hkl hk0 p hno component x.1 := by
        simpa only using htoken
      rw [htoken']
      exact (canonicalStableRawComponentTightSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component sources x).2




theorem
    canonicalStableRawComponentForestStepMerger_threeTokens_of_distinctDirect
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (x y : ↑sources)
    (output first second : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hfirstNeSecond : first ≠ second)
    (hfirst : x.1.1 = first.1) (hsecond : y.1.1 = second.1)
    (hx : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component x.1 =
      Sum.inl output)
    (hy : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component y.1 =
      Sum.inl output) :
    Nonempty (Fin 3 ↪
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources)) := by
  let firstNatural := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources x
  let secondNatural := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources y
  let commonSuccessor := canonicalStableRawComponentTightSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources x
  have hfirstNatural : firstNatural.1 =
      canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component first := by
    apply Subtype.ext
    change canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno x.1.1 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno first.1
    rw [hfirst]
  have hsecondNatural : secondNatural.1 =
      canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component second := by
    apply Subtype.ext
    change canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno y.1.1 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno second.1
    rw [hsecond]
  have hcommonX : commonSuccessor.1 =
      canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component output := by
    have htoken := canonicalStableRawComponentForestStep_token
      ends m j k l zero hloop hjk hkl hk0 p hno component x.1
    rw [hx] at htoken
    exact htoken.symm
  have hcommonY : commonSuccessor.1 =
      canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component y.1 := by
    have hyToken := canonicalStableRawComponentForestStep_token
      ends m j k l zero hloop hjk hkl hk0 p hno component y.1
    rw [hy] at hyToken
    exact hcommonX.trans hyToken
  have hfirstSecond : firstNatural ≠ secondNatural := by
    intro heq
    apply hfirstNeSecond
    apply (canonicalStableRawComponentDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component).injective
    exact hfirstNatural.symm.trans
      ((congrArg Subtype.val heq).trans hsecondNatural)
  have hfirstCommon : firstNatural ≠ commonSuccessor := by
    intro heq
    apply canonicalStableRawComponentSuccessorToken_ne_natural
      ends m j k l zero hloop hjk hkl hk0 p hno component x.1
    exact (congrArg Subtype.val heq).symm
  have hsecondCommon : secondNatural ≠ commonSuccessor := by
    intro heq
    apply canonicalStableRawComponentSuccessorToken_ne_natural
      ends m j k l zero hloop hjk hkl hk0 p hno component y.1
    exact hcommonY.symm.trans (congrArg Subtype.val heq).symm
  exact finiteEmbedding_three_of_pairwise_ne
    firstNatural secondNatural commonSuccessor
      hfirstSecond hfirstCommon hsecondCommon




theorem canonicalStableRawComponentForestStepMerger_localDischarge
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (x y : ↑sources) (hne : x ≠ y)
    (hmerge : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component x.1 =
      canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component y.1) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      Nonempty (Fin 3 ↪
        ↑(canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨
      ∃ second : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component second.1.2 ∈
          canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
  rcases canonicalStableRawComponentForestStepMerger_localizedOutput
      ends m j k l zero hloop hjk hkl hk0 p hno component sources x y hmerge with
    ⟨terminal, hterminal, _hx, _hy⟩ |
      ⟨output, _houtput, hx, hy⟩
  · exact Or.inl ⟨terminal, hterminal⟩
  · rcases canonicalStableRawComponent_distinctTightStates_localDischarge
        ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
          x y hne with hterminal | hthree | hsecond |
            ⟨first, second, hfirstNeSecond, hfirst, hsecond⟩
    · exact Or.inl hterminal
    · exact Or.inr (Or.inl hthree)
    · exact Or.inr (Or.inr hsecond)
    · exact Or.inr (Or.inl
        (canonicalStableRawComponentForestStepMerger_threeTokens_of_distinctDirect
          ends m j k l zero hloop hjk hkl hk0 p hno component sources
            x y output first second hfirstNeSecond hfirst hsecond hx hy))




theorem exists_canonicalStableRawTightComponentForestStepMerger
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    ∃ x y : ↑sources,
      x.1 ≠ y.1 ∧
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component x.1 =
          canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component y.1 := by
  classical
  let successor := canonicalStableRawComponentTightSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  let hsuccessor := canonicalStableRawComponentTightSuccessorToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  obtain ⟨state, hne, htoken⟩ :=
    exists_canonicalStableRawTightComponentSuccessorCollision
      ends m j k l zero hloop hjk hkl hk0 p hno component sources htight
  refine ⟨state.hole, (state.move successor hsuccessor).hole, hne, ?_⟩
  exact canonicalStableRawComponentForestStep_eq_of_tightSuccessorToken_eq
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
      state.hole (state.move successor hsuccessor).hole htoken



theorem exists_canonicalStableRawTightComponent_localDischarge
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      Nonempty (Fin 3 ↪
        ↑(canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨
      ∃ second : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component second.1.2 ∈
          canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
  obtain ⟨x, y, hne, hmerge⟩ :=
    exists_canonicalStableRawTightComponentForestStepMerger
      ends m j k l zero hloop hjk hkl hk0 p hno component sources htight
  apply canonicalStableRawComponentForestStepMerger_localDischarge
    ends m j k l zero hloop hjk hkl hk0 p hno component sources herase x y
  · intro hxy
    exact hne (congrArg Subtype.val hxy)
  · exact hmerge



theorem exists_canonicalStableRawComponent_localDischarge_of_deficit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) <
      Fintype.card (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ sources : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      sources.Nonempty ∧
      (canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources).card +
          1 = sources.card ∧
      (∀ source ∈ sources,
        canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (sources.erase source) =
          canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∧
      (∀ smaller : Finset (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component),
        smaller ⊂ sources ->
          smaller.card ≤
            (canonicalStableRawComponentIncidentNeighborhood
              ends m j k l zero hloop hjk hkl hk0 p hno component
                smaller).card) ∧
      ((∃ terminal : CanonicalStableRawComponentNonexceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
        Nonempty (Fin 3 ↪
          ↑(canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨
        ∃ second : StatMech.FrontierA.crossCollision
            (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component)
            (canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component),
          canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component second.1.2 ∈
            canonicalStableRawComponentIncidentNeighborhood
              ends m j k l zero hloop hjk hkl hk0 p hno component sources) := by
  classical
  obtain ⟨sources, hnonempty, htight, herase, hproper⟩ :=
    exists_canonicalStableRawComponent_minimalIncidentObstruction_of_deficit
      ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit
  refine ⟨sources, hnonempty, htight, herase, hproper, ?_⟩
  exact exists_canonicalStableRawTightComponent_localDischarge
    ends m j k l zero hloop hjk hkl hk0 p hno component sources herase htight




theorem exists_canonicalStableRawComponent_strictBlock_or_fourTightSources_of_deficit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) <
      Fintype.card (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    (∃ size : Nat, 0 < size ∧
      Nonempty (Fin size ↪ CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
      Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component)) ∨
      ∃ sources : Finset (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component),
        Nonempty (Fin 4 ↪ ↑sources) := by
  classical
  obtain ⟨sources, hnonempty, htight, herase, hproper, hdischarge⟩ :=
    exists_canonicalStableRawComponent_localDischarge_of_deficit
      ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit
  have strictOfTerminal
      (terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) :
      ∃ size : Nat, 0 < size ∧
        Nonempty (Fin size ↪ CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
        Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) := by
    have hdirectGt := canonicalStableRawComponent_direct_card_gt_self_of_deficit
      ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit
    have hdirectPos : 0 < Nat.card (CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
      omega
    let start : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      (Nat.card_pos_iff.mp hdirectPos).1.some
    exact exists_canonicalStableRawComponentDirect_strictTokenBlock_of_available
      ends m j k l zero hloop hjk hkl hk0 p hno component start terminal
  rcases hdischarge with ⟨terminal, _hterminalMem⟩ | hthree |
      ⟨second, _hsecondMem⟩
  · exact Or.inl (strictOfTerminal terminal)
  · right
    let source := hnonempty.choose
    have hsource : source ∈ sources := hnonempty.choose_spec
    exact ⟨sources,
      exists_canonicalStableRawComponent_fourSourceEmbedding_of_threeTightTokens
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          source hsource htight hproper hthree⟩
  · exact Or.inl
      (exists_canonicalStableRawComponentSecondCollision_strictTokenBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component second)



theorem exists_canonicalStableRawTightComponentCrossCollision
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    let incident : ↑sources -> TightToken -> Prop := fun state token =>
      CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component
          state.1 token.1
    let natural := canonicalStableRawComponentTightNaturalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
    let hnatural := canonicalStableRawComponentTightNaturalToken_incident
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
    ∃ state : StatMech.FrontierA.RelationPartialMatching.HoleState incident,
      ∃ collision : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        state.hole.1.1 = collision.1.1.1 ∧
          (state.move natural hnatural).hole.1.1 = collision.1.2.1 := by
  classical
  dsimp only
  let TightState := ↑sources
  let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  let incident : TightState -> TightToken -> Prop := fun state token =>
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1
  let natural := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  let hnatural := canonicalStableRawComponentTightNaturalToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  have hcard : Fintype.card TightToken < Fintype.card TightState := by
    simpa only [TightToken, TightState, Fintype.card_coe] using
      (show (canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources).card <
        sources.card by omega)
  obtain ⟨state, hholes, htoken⟩ :=
    StatMech.FrontierA.RelationPartialMatching.exists_maximalNatural_holeState_collision
      incident natural hnatural hcard
  have hrawToken : canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno state.hole.1.1 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno
          (state.move natural hnatural).hole.1.1 := by
    exact congrArg (fun token : TightToken => token.1.1) htoken
  rcases canonicalStableRawStateLeftToken_eq_imp
      ends m j k l zero hloop hjk hkl hk0 p hno
        state.hole.1.1 (state.move natural hnatural).hole.1.1 hrawToken with
    heq | hforward | hreverse
  · exact False.elim (hholes (Subtype.ext (Subtype.ext heq)))
  · let self : CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
        ⟨state.hole.1.1, state.hole.1.2, hforward.1⟩
    let direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
        ⟨(state.move natural hnatural).hole.1.1,
          (state.move natural hnatural).hole.1.2, hforward.2.1⟩
    let collision : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component) :=
      ⟨(self, direct), by
        apply Subtype.ext
        exact hrawToken⟩
    exact ⟨state, collision, rfl, rfl⟩
  · let self : CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
        ⟨(state.move natural hnatural).hole.1.1,
          (state.move natural hnatural).hole.1.2, hreverse.1⟩
    let direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
        ⟨state.hole.1.1, state.hole.1.2, hreverse.2.1⟩
    let collision : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component) :=
      ⟨(self, direct), by
        apply Subtype.ext
        exact hrawToken.symm⟩
    have hback := state.move_move_hole_eq_of_natural_eq
      natural hnatural htoken
    refine ⟨state.move natural hnatural, collision, rfl, ?_⟩
    exact congrArg (fun tightState : TightState => tightState.1.1) hback




theorem exists_canonicalStableRawTightComponent_twoAlternateTokenEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    Nonempty (Fin 2 ↪
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources)) := by
  classical
  obtain ⟨state, collision, hself, _hdirect⟩ :=
    exists_canonicalStableRawTightComponentCrossCollision
      ends m j k l zero hloop hjk hkl hk0 p hno component sources htight
  exact canonicalStableRawComponent_tightCrossCollision_twoAlternateTokenEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
      state.hole collision hself




theorem
    exists_canonicalStableRawTightComponent_sourceNormalized_or_four_le_card
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    (∃ state : ↑sources,
      ∃ collision : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        state.1.1 = collision.1.1.1 ∧
          canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component collision =
            canonicalStableRawComponentNaturalToken
              ends m j k l zero hloop hjk hkl hk0 p hno component state.1) ∨
      4 ≤ sources.card := by
  classical
  obtain ⟨state, collision, hself, _hdirect⟩ :=
    exists_canonicalStableRawTightComponentCrossCollision
      ends m j k l zero hloop hjk hkl hk0 p hno component sources htight
  rcases
      canonicalStableRawComponent_tightCrossCollision_sourceNormalized_or_threeTokens
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          state.hole collision hself with
    hnormalized | htokens
  · exact Or.inl ⟨state.hole, collision, hself, hnormalized⟩
  · right
    obtain ⟨tokens⟩ := htokens
    have hcard : 3 ≤
        (canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources).card := by
      simpa only [Fintype.card_fin, Fintype.card_coe] using
        Fintype.card_le_of_injective tokens tokens.injective
    omega




theorem exists_canonicalStableRawTightComponentFirstChargeOccupant
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    let incident : ↑sources -> TightToken -> Prop := fun state token =>
      CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component
          state.1 token.1
    let natural := canonicalStableRawComponentTightNaturalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
    let hnatural := canonicalStableRawComponentTightNaturalToken_incident
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
    ∃ state : StatMech.FrontierA.RelationPartialMatching.HoleState incident,
      ∃ collision : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
      ∃ third : ↑sources,
        state.hole.1.1 = collision.1.1.1 ∧
        (state.move natural hnatural).hole.1.1 = collision.1.2.1 ∧
        third ≠ state.hole ∧
        third ≠ (state.move natural hnatural).hole ∧
        CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component third.1
              (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
                ends m j k l zero hloop hjk hkl hk0 p hno component
                  collision) ∧
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          u.target = canonicalStableRawLeftTokenTarget
              ends m j k l zero hloop hjk hkl hk0 p
                (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    collision).1 ∧
          (CanonicalStableRawOwnerStableOutput
              ends m j k l zero hloop hjk hkl hk0 p state.hole.1.1 u ∨
            CanonicalStableRawOwnerAdvancingOutput
              ends m j k l zero hloop hjk hkl hk0 p state.hole.1.1 u) ∧
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  classical
  dsimp only
  let TightState := ↑sources
  let neighborhood := canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  let TightToken := ↑neighborhood
  let incident : TightState -> TightToken -> Prop := fun state token =>
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1
  let natural := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  let hnatural := canonicalStableRawComponentTightNaturalToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  let first := canonicalStableRawComponentReferenceOwnerCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  obtain ⟨state, collision, hself, hdirect⟩ :=
    exists_canonicalStableRawTightComponentCrossCollision
      ends m j k l zero hloop hjk hkl hk0 p hno component sources htight
  have hfirstIncident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        state.hole.1 (first collision) := by
    apply (canonicalStableRawWitnessedStateTokenIncidence_iff
      ends m j k l zero hloop hjk hkl hk0 p
        (first collision).1 state.hole.1.1).2
    rw [hself]
    exact canonicalStableRawReferenceOwnerLeftToken_stateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        collision.1.1.1 collision.1.1.2.2
  let firstTight : TightToken :=
    ⟨first collision, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, state.hole.1, state.hole.2, hfirstIncident⟩⟩
  obtain ⟨third, hthird⟩ :=
    state.maximum.saturates_target_of_unmatched
      state.hole state.hole_unmatched firstTight hfirstIncident
  have hthirdNeHole : third ≠ state.hole := by
    intro heq
    subst third
    exact state.hole_unmatched
      ((StatMech.FrontierA.RelationPartialMatching.mem_support_iff
        state.matching state.hole).2 ⟨firstTight, hthird⟩)
  have hthirdNeDirect : third ≠ (state.move natural hnatural).hole := by
    intro heq
    have hfirstNaturalTight : firstTight = natural state.hole := by
      apply Option.some.inj
      exact hthird.symm.trans
        (heq ▸ state.matching_apply_move_hole natural hnatural)
    have hfirstNatural : first collision =
        canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component
            state.hole.1 := by
      exact congrArg (fun token : TightToken => token.1) hfirstNaturalTight
    apply canonicalStableRawComponentReferenceOwnerCollisionEmbedding_ne_self
      ends m j k l zero hloop hjk hkl hk0 p hno component
        collision collision.1.1
    calc
      first collision = canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component
            state.hole.1 := hfirstNatural
      _ = canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component
            collision.1.1 := by
        apply Subtype.ext
        change canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno state.hole.1.1 =
          canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1
        rw [hself]
  have hthirdIncident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        third.1 (first collision) := state.matching.related hthird
  have hclassification :=
    canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
      ends m j k l zero hloop hjk hkl hk0 p hno
        (first collision).1 state.hole.1.1 third.1.1
          hfirstIncident hthirdIncident
  have houtput : ∃ u : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p,
      u.target = canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p (first collision).1 ∧
      (CanonicalStableRawOwnerStableOutput
          ends m j k l zero hloop hjk hkl hk0 p state.hole.1.1 u ∨
        CanonicalStableRawOwnerAdvancingOutput
          ends m j k l zero hloop hjk hkl hk0 p state.hole.1.1 u) ∧
      canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
    rcases hclassification with heq | hstable | hadvancing
    · exact False.elim (hthirdNeHole
        (Subtype.ext (Subtype.ext heq)).symm)
    · exact ⟨hstable.choose, hstable.choose_spec.1,
        Or.inl hstable.choose_spec.2.1,
        hstable.choose_spec.2.2.1.trans state.hole.1.2⟩
    · exact ⟨hadvancing.choose, hadvancing.choose_spec.1,
        Or.inr hadvancing.choose_spec.2.1,
        hadvancing.choose_spec.2.2.1.trans state.hole.1.2⟩
  exact ⟨state, collision, third, hself, hdirect,
    hthirdNeHole, hthirdNeDirect, hthirdIncident, houtput⟩





theorem exists_canonicalStableRawTightComponentFirstChargeCollisionSplit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    (∃ collision : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        ∃ direct : CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component collision =
            canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component direct ∧
          canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component
                collision.1.2 ∈
            canonicalStableRawComponentIncidentNeighborhood
              ends m j k l zero hloop hjk hkl hk0 p hno component sources ∧
          canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component direct ∈
            canonicalStableRawComponentIncidentNeighborhood
              ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      ∃ collision : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        ∃ direct : CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          canonicalStableRawComponentReferenceOwnerCollisionEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component collision =
            canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component direct ∧
          canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component
                collision.1.2 ∈
            canonicalStableRawComponentIncidentNeighborhood
              ends m j k l zero hloop hjk hkl hk0 p hno component sources ∧
          canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component direct ∈
            canonicalStableRawComponentIncidentNeighborhood
              ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
  classical
  obtain ⟨state, collision, _third, hself, _hdirect,
      _hthirdNeHole, _hthirdNeDirect, _hthirdIncident,
      u, huTarget, hkind, huComponent⟩ :=
    exists_canonicalStableRawTightComponentFirstChargeOccupant
      ends m j k l zero hloop hjk hkl hk0 p hno component sources htight
  have hnaturalMem : canonicalStableRawComponentNaturalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component state.hole.1 ∈
      canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, state.hole.1, state.hole.2,
      canonicalStableRawComponentNaturalToken_incident
        ends m j k l zero hloop hjk hkl hk0 p hno component state.hole.1⟩
  have hcollisionNatural :
      canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.2 =
        canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component state.hole.1 := by
    calc
      canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.2 =
        canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.1 :=
            collision.2.symm
      _ = canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component state.hole.1 := by
        apply Subtype.ext
        change canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1 =
          canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno state.hole.1.1
        rw [hself]
  have hcollisionTokenMem :
      canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.2 ∈
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
    rw [hcollisionNatural]
    exact hnaturalMem
  have huTargetRaw : u.target.1 =
      (canonicalStableRawReferenceOwnerAlternateData
        ends m j k l zero hloop hjk hkl hk0 p
          collision.1.1.1 collision.1.1.2.2).target :=
    calc
      u.target.1 = (canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p
            (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component
                collision).1).1 := congrArg Subtype.val huTarget
      _ = (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component
            collision).1.2.1 := rfl
      _ = (canonicalStableRawReferenceOwnerAlternateData
          ends m j k l zero hloop hjk hkl hk0 p
            collision.1.1.1 collision.1.1.2.2).target :=
        canonicalStableRawReferenceOwnerLeftToken_target
          ends m j k l zero hloop hjk hkl hk0 p
            collision.1.1.1 collision.1.1.2.2
  rw [hself] at hkind
  rcases hkind with hstable | hadvancing
  · obtain ⟨huDirect, hkey⟩ :=
      canonicalStableRawOwnerStableOutput_directKey_eq_referenceSource
        ends m j k l zero hloop hjk hkl hk0 p
          collision.1.1.1 u collision.1.1.2.2 huTargetRaw hstable
    let direct : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨u, huComponent, huDirect⟩
    have htoken :
        canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component collision =
          canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component direct := by
      apply (canonicalStableRawComponentTokenKeyEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component).injective
      change canonicalStableRawLeftTokenKey
          ends m j k l zero hloop hjk hkl hk0 p
            (canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component
                collision).1 =
        canonicalStableRawLeftTokenKey
          ends m j k l zero hloop hjk hkl hk0 p
            (canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component direct).1
      change canonicalStableRawLeftTokenKey
          ends m j k l zero hloop hjk hkl hk0 p
            (canonicalStableRawReferenceSourceLeftToken
              ends m j k l zero hloop hjk hkl hk0 p
                collision.1.1.1 collision.1.1.2.2) =
        canonicalStableRawLeftTokenKey
          ends m j k l zero hloop hjk hkl hk0 p
            (canonicalStableRawStateLeftToken
              ends m j k l zero hloop hjk hkl hk0 p hno u)
      unfold canonicalStableRawStateLeftToken
      rw [dif_neg huDirect]
      change (collision.1.1.1.source,
          (canonicalStableRawReferenceOwnerAlternateData
            ends m j k l zero hloop hjk hkl hk0 p
              collision.1.1.1 collision.1.1.2.2).target) =
        (u.source, u.target.1)
      exact hkey
    have hsourceIncident : CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component state.hole.1
          (canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component collision) := by
      apply (canonicalStableRawWitnessedStateTokenIncidence_iff
        ends m j k l zero hloop hjk hkl hk0 p _ _).2
      rw [hself]
      exact canonicalStableRawReferenceSourceLeftToken_stateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p
          collision.1.1.1 collision.1.1.2.2
    refine Or.inl ⟨collision, direct, htoken, hcollisionTokenMem, ?_⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, state.hole.1, state.hole.2,
      htoken ▸ hsourceIncident⟩
  · obtain ⟨huDirect, hkey⟩ :=
      canonicalStableRawOwnerAdvancingOutput_directKey_eq_referenceOwner
        ends m j k l zero hloop hjk hkl hk0 p
          collision.1.1.1 u collision.1.1.2.2 huTargetRaw hadvancing
    let direct : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨u, huComponent, huDirect⟩
    have htoken :
        canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component collision =
          canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component direct := by
      apply (canonicalStableRawComponentTokenKeyEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component).injective
      change canonicalStableRawLeftTokenKey
          ends m j k l zero hloop hjk hkl hk0 p
            (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component
                collision).1 =
        canonicalStableRawLeftTokenKey
          ends m j k l zero hloop hjk hkl hk0 p
            (canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component direct).1
      change canonicalStableRawLeftTokenKey
          ends m j k l zero hloop hjk hkl hk0 p
            (canonicalStableRawReferenceOwnerLeftToken
              ends m j k l zero hloop hjk hkl hk0 p
                collision.1.1.1 collision.1.1.2.2) =
        canonicalStableRawLeftTokenKey
          ends m j k l zero hloop hjk hkl hk0 p
            (canonicalStableRawStateLeftToken
              ends m j k l zero hloop hjk hkl hk0 p hno u)
      unfold canonicalStableRawStateLeftToken
      rw [dif_neg huDirect]
      change (canonicalStableRawReferenceOwner
            ends m j k l zero hloop hjk hkl hk0 p collision.1.1.1,
          (canonicalStableRawReferenceOwnerAlternateData
            ends m j k l zero hloop hjk hkl hk0 p
              collision.1.1.1 collision.1.1.2.2).target) =
        (u.source, u.target.1)
      exact hkey
    have hownerIncident : CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component state.hole.1
          (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component collision) := by
      apply (canonicalStableRawWitnessedStateTokenIncidence_iff
        ends m j k l zero hloop hjk hkl hk0 p _ _).2
      rw [hself]
      exact canonicalStableRawReferenceOwnerLeftToken_stateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p
          collision.1.1.1 collision.1.1.2.2
    refine Or.inr ⟨collision, direct, htoken, hcollisionTokenMem, ?_⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, state.hole.1, state.hole.2,
      htoken ▸ hownerIncident⟩




theorem
    exists_canonicalStableRawTightComponent_distinctDirectTokens_or_sourceNormalized
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    (∃ collision : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        ∃ direct : CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          direct ≠ collision.1.2 ∧
          canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component
                collision.1.2 ∈
            canonicalStableRawComponentIncidentNeighborhood
              ends m j k l zero hloop hjk hkl hk0 p hno component sources ∧
          canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component direct ∈
            canonicalStableRawComponentIncidentNeighborhood
              ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      ∃ collision : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component collision =
          canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.1 ∧
        canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.1 ∈
          canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
  rcases exists_canonicalStableRawTightComponentFirstChargeCollisionSplit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources htight with
    ⟨collision, direct, htoken, holdMem, hnewMem⟩ |
      ⟨collision, direct, htoken, holdMem, hnewMem⟩
  · by_cases hdistinct : direct ≠ collision.1.2
    · exact Or.inl ⟨collision, direct, hdistinct, holdMem, hnewMem⟩
    · have heq : direct = collision.1.2 := Classical.not_not.mp hdistinct
      right
      refine ⟨collision, ?_, ?_⟩
      · exact htoken.trans ((congrArg
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          heq).trans collision.2.symm)
      · rw [collision.2]
        exact holdMem
  · have hdistinct : direct ≠ collision.1.2 := by
      intro heq
      apply canonicalStableRawComponentReferenceOwnerCollisionEmbedding_ne_self
        ends m j k l zero hloop hjk hkl hk0 p hno component
          collision collision.1.1
      exact htoken.trans ((congrArg
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        heq).trans collision.2.symm)
    exact Or.inl ⟨collision, direct, hdistinct, holdMem, hnewMem⟩




theorem exists_canonicalStableRawTightComponent_threeStateTwoTokenPeelData
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    let incident : ↑sources -> TightToken -> Prop := fun state token =>
      CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1
    let natural := canonicalStableRawComponentTightNaturalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
    let hnatural := canonicalStableRawComponentTightNaturalToken_incident
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
    ∃ state : StatMech.FrontierA.RelationPartialMatching.HoleState incident,
      ∃ collision : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        ∃ third : ↑sources, ∃ first : TightToken,
          state.hole.1.1 = collision.1.1.1 ∧
          (state.move natural hnatural).hole.1.1 = collision.1.2.1 ∧
          third ≠ state.hole ∧
          third ≠ (state.move natural hnatural).hole ∧
          state.hole ≠ (state.move natural hnatural).hole ∧
          first.1 = canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component collision ∧
          natural state.hole ≠ first ∧
          incident state.hole (natural state.hole) ∧
          incident (state.move natural hnatural).hole (natural state.hole) ∧
          incident state.hole first ∧ incident third first := by
  classical
  dsimp only
  let TightState := ↑sources
  let neighborhood := canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  let TightToken := ↑neighborhood
  let incident : TightState -> TightToken -> Prop := fun state token =>
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1
  let natural := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  let hnatural := canonicalStableRawComponentTightNaturalToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  obtain ⟨state, collision, third, hself, hdirect,
      hthirdNeHole, hthirdNeDirect, hthirdIncident, _u, _huTarget,
      _hkind, _huComponent⟩ :=
    exists_canonicalStableRawTightComponentFirstChargeOccupant
      ends m j k l zero hloop hjk hkl hk0 p hno component sources htight
  have hfirstIncident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.hole.1
        (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision) := by
    apply (canonicalStableRawWitnessedStateTokenIncidence_iff
      ends m j k l zero hloop hjk hkl hk0 p _ state.hole.1.1).2
    rw [hself]
    exact canonicalStableRawReferenceOwnerLeftToken_stateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        collision.1.1.1 collision.1.1.2.2
  let first : TightToken :=
    ⟨canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component collision,
      Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, state.hole.1, state.hole.2, hfirstIncident⟩⟩
  have hnaturalSelf : (natural state.hole).1 =
      canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.1 := by
    apply Subtype.ext
    change canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno state.hole.1.1 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1
    rw [hself]
  have hnaturalDirect :
      (natural (state.move natural hnatural).hole).1 =
        canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component
            collision.1.2 := by
    apply Subtype.ext
    change canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno
          (state.move natural hnatural).hole.1.1 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno collision.1.2.1
    rw [hdirect]
  have hnaturalEq : natural state.hole =
      natural (state.move natural hnatural).hole := by
    apply Subtype.ext
    exact hnaturalSelf.trans (collision.2.trans hnaturalDirect.symm)
  have hfirstNe : natural state.hole ≠ first := by
    intro heq
    apply canonicalStableRawComponentReferenceOwnerCollisionEmbedding_ne_self
      ends m j k l zero hloop hjk hkl hk0 p hno component
        collision collision.1.1
    calc
      canonicalStableRawComponentReferenceOwnerCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision =
        first.1 := rfl
      _ = (natural state.hole).1 := congrArg Subtype.val heq.symm
      _ = canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component
            collision.1.1 := hnaturalSelf
  refine ⟨state, collision, third, first, hself, hdirect,
    hthirdNeHole, hthirdNeDirect,
    state.hole_ne_move_hole natural hnatural, rfl, hfirstNe,
    hnatural state.hole, ?_, hfirstIncident, ?_⟩
  · change incident (state.move natural hnatural).hole (natural state.hole)
    rw [hnaturalEq]
    exact hnatural (state.move natural hnatural).hole
  · exact hthirdIncident




structure CanonicalStableRawTightChargeOrbit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)) where
  size : Nat
  states : Fin (size + 1) ↪ ↑sources
  tokens : Fin size ↪
    ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  paired : ∀ i, CanonicalStableRawComponentIncident
    ends m j k l zero hloop hjk hkl hk0 p hno component
      (states i.succ).1 (tokens i).1
  coreSelf : Fin (size + 1)
  coreDirect : Fin (size + 1)
  coreThird : Fin (size + 1)
  coreNatural : Fin size
  coreFirst : Fin size
  origin : ∀ i,
    tokens i = canonicalStableRawComponentTightNaturalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          (states i.succ) ∨
      tokens i = canonicalStableRawComponentTightSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          (states i.succ) ∨
      i = coreFirst
  coreSelf_ne_direct : coreSelf ≠ coreDirect
  coreSelf_ne_third : coreSelf ≠ coreThird
  coreDirect_ne_third : coreDirect ≠ coreThird
  coreNatural_ne_first : coreNatural ≠ coreFirst
  self_natural : CanonicalStableRawComponentIncident
    ends m j k l zero hloop hjk hkl hk0 p hno component
      (states coreSelf).1 (tokens coreNatural).1
  direct_natural : CanonicalStableRawComponentIncident
    ends m j k l zero hloop hjk hkl hk0 p hno component
      (states coreDirect).1 (tokens coreNatural).1
  self_first : CanonicalStableRawComponentIncident
    ends m j k l zero hloop hjk hkl hk0 p hno component
      (states coreSelf).1 (tokens coreFirst).1
  third_first : CanonicalStableRawComponentIncident
    ends m j k l zero hloop hjk hkl hk0 p hno component
      (states coreThird).1 (tokens coreFirst).1




theorem CanonicalStableRawTightChargeOrbit.extendPair
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (source : ↑sources)
    (token : ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources))
    (hsource : ∀ i, source ≠ orbit.states i)
    (htoken : ∀ i, token ≠ orbit.tokens i)
    (hincident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component source.1 token.1)
    (horigin : token = canonicalStableRawComponentTightNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component sources source ∨
        token = canonicalStableRawComponentTightSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component sources source) :
    ∃ extended : CanonicalStableRawTightChargeOrbit
        ends m j k l zero hloop hjk hkl hk0 p hno component sources,
      extended.size = orbit.size + 1 := by
  obtain ⟨extendedStates, hstatePrefix, hstateLast⟩ :=
    finiteEmbedding_snoc (orbit.size + 1) orbit.states source hsource
  obtain ⟨extendedTokens, htokenPrefix, htokenLast⟩ :=
    finiteEmbedding_snoc orbit.size orbit.tokens token htoken
  refine ⟨⟨orbit.size + 1, extendedStates, extendedTokens, ?_,
    orbit.coreSelf.castSucc, orbit.coreDirect.castSucc,
    orbit.coreThird.castSucc, orbit.coreNatural.castSucc,
    orbit.coreFirst.castSucc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · intro i
    refine Fin.lastCases ?_ (fun q => ?_) i
    · have hsucc : (Fin.last orbit.size).succ =
          Fin.last (orbit.size + 1) := by
        apply Fin.ext
        rfl
      rw [hsucc, hstateLast, htokenLast]
      exact hincident
    · have hsucc : q.castSucc.succ = q.succ.castSucc := by
        apply Fin.ext
        rfl
      rw [hsucc, hstatePrefix, htokenPrefix]
      exact orbit.paired q
  · intro i
    refine Fin.lastCases ?_ (fun q => ?_) i
    · have hsucc : (Fin.last orbit.size).succ =
          Fin.last (orbit.size + 1) := by
        apply Fin.ext
        rfl
      rw [hsucc, hstateLast, htokenLast]
      rcases horigin with hnatural | hsuccessor
      · exact Or.inl hnatural
      · exact Or.inr (Or.inl hsuccessor)
    · have hsucc : q.castSucc.succ = q.succ.castSucc := by
        apply Fin.ext
        rfl
      rw [hsucc, hstatePrefix, htokenPrefix]
      rcases orbit.origin q with hnatural | hsuccessor | hcore
      · exact Or.inl hnatural
      · exact Or.inr (Or.inl hsuccessor)
      · exact Or.inr (Or.inr (congrArg Fin.castSucc hcore))
  · intro heq
    exact orbit.coreSelf_ne_direct (Fin.castSucc_inj.mp heq)
  · intro heq
    exact orbit.coreSelf_ne_third (Fin.castSucc_inj.mp heq)
  · intro heq
    exact orbit.coreDirect_ne_third (Fin.castSucc_inj.mp heq)
  · intro heq
    exact orbit.coreNatural_ne_first (Fin.castSucc_inj.mp heq)
  · rw [hstatePrefix, htokenPrefix]
    exact orbit.self_natural
  · rw [hstatePrefix, htokenPrefix]
    exact orbit.direct_natural
  · rw [hstatePrefix, htokenPrefix]
    exact orbit.self_first
  · rw [hstatePrefix, htokenPrefix]
    exact orbit.third_first


def CanonicalStableRawTightChargeOrbit.TokenSaturated
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources) : Prop :=
  ∀ source token,
    CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component source.1 token.1 ->
      (∃ i, token = orbit.tokens i) -> ∃ i, source = orbit.states i


def CanonicalStableRawTightChargeOrbit.SourceSaturated
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources) : Prop :=
  ∀ source token,
    CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component source.1 token.1 ->
      (∃ i, source = orbit.states i) -> ∃ i, token = orbit.tokens i



theorem CanonicalStableRawTightChargeOrbit.sourceSaturated_or_crossing
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.SourceSaturated ∨
      ∃ source token,
        CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component
              source.1 token.1 ∧
          (∃ i, source = orbit.states i) ∧
          ∀ i, token ≠ orbit.tokens i := by
  classical
  by_cases hsaturated : orbit.SourceSaturated
  · exact Or.inl hsaturated
  · right
    unfold CanonicalStableRawTightChargeOrbit.SourceSaturated at hsaturated
    push Not at hsaturated
    obtain ⟨source, token, hincident, hsource, htoken⟩ := hsaturated
    exact ⟨source, token, hincident, hsource, htoken⟩




theorem CanonicalStableRawTightChargeOrbit.sourceSaturated_or_external_or_chord
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.SourceSaturated ∨
      (∃ external token,
        CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component
              external.1 token.1 ∧
          (∀ i, external ≠ orbit.states i) ∧
          ∀ i, token ≠ orbit.tokens i) ∨
      ∃ q r : Fin (orbit.size + 1), q ≠ r ∧
        ∃ token,
          CanonicalStableRawComponentIncident
              ends m j k l zero hloop hjk hkl hk0 p hno component
                (orbit.states q).1 token.1 ∧
          CanonicalStableRawComponentIncident
              ends m j k l zero hloop hjk hkl hk0 p hno component
                (orbit.states r).1 token.1 ∧
          ∀ s, token ≠ orbit.tokens s := by
  classical
  rcases orbit.sourceSaturated_or_crossing with hsaturated |
      ⟨source, token, hincident, ⟨q, hsource⟩, htoken⟩
  · exact Or.inl hsaturated
  · obtain ⟨other, hotherMem, hotherNe, hotherIncident⟩ :=
      exists_other_mem_of_incident_of_delete_invariant
        ends m j k l zero hloop hjk hkl hk0 p hno component sources source.1
          source.2 (herase source.1 source.2) token.1 hincident
    let external : ↑sources := ⟨other, hotherMem⟩
    by_cases hother : ∃ r, external = orbit.states r
    · obtain ⟨r, hr⟩ := hother
      right
      right
      refine ⟨q, r, ?_, token, ?_, ?_, htoken⟩
      · intro hqr
        apply hotherNe
        have heq : source = external := hsource.trans (hqr ▸ hr.symm)
        exact congrArg Subtype.val heq.symm
      · rw [← hsource]
        exact hincident
      · rw [← hr]
        exact hotherIncident
    · right
      left
      refine ⟨external, token, hotherIncident, ?_, htoken⟩
      push Not at hother
      exact hother



theorem CanonicalStableRawTightChargeOrbit.internalChordClassification
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (q r : Fin (orbit.size + 1)) (hqr : q ≠ r)
    (token : ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources))
    (hq : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (orbit.states q).1 token.1)
    (hr : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (orbit.states r).1 token.1) :
    (∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
            ends m j k l zero hloop hjk hkl hk0 p token.1.1 ∧
        CanonicalStableRawOwnerStableOutput
            ends m j k l zero hloop hjk hkl hk0 p (orbit.states q).1.1 u ∧
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
            ends m j k l zero hloop hjk hkl hk0 p token.1.1 ∧
        CanonicalStableRawOwnerAdvancingOutput
            ends m j k l zero hloop hjk hkl hk0 p (orbit.states q).1.1 u ∧
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  rcases canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
      ends m j k l zero hloop hjk hkl hk0 p hno token.1
        (orbit.states q).1.1 (orbit.states r).1.1 hq hr with
    heq | ⟨u, htarget, hstable, hcomponent, _⟩ |
      ⟨u, htarget, hadvancing, hcomponent, _⟩
  · apply False.elim
    apply hqr
    apply orbit.states.injective
    apply Subtype.ext
    apply Subtype.ext
    exact heq
  · exact Or.inl
      ⟨u, htarget, hstable, hcomponent.trans (orbit.states q).1.2⟩
  · exact Or.inr
      ⟨u, htarget, hadvancing, hcomponent.trans (orbit.states q).1.2⟩





theorem CanonicalStableRawTightChargeOrbit.SourceSaturated.exhaustive_of_properHall
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (hsaturated : orbit.SourceSaturated)
    (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      smaller ⊂ sources ->
        smaller.card ≤
          (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              smaller).card) :
    ∀ source : ↑sources, ∃ i, source = orbit.states i := by
  classical
  let stateVal : ↑sources ↪ CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let tokenVal :
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) ↪
        CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let stateBlock : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :=
    Finset.univ.map (orbit.states.trans stateVal)
  let tokenBlock : Finset (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) :=
    Finset.univ.map (orbit.tokens.trans tokenVal)
  have hstateSubset : stateBlock ⊆ sources := by
    intro state hstate
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp hstate
    exact (orbit.states i).2
  by_contra hexhaustive
  push Not at hexhaustive
  obtain ⟨missing, hmissing⟩ := hexhaustive
  have hmissingBlock : missing.1 ∉ stateBlock := by
    intro hmem
    obtain ⟨i, _hi, heq⟩ := Finset.mem_map.mp hmem
    apply hmissing i
    apply Subtype.ext
    exact heq.symm
  have hstateProper : stateBlock ⊂ sources := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hstateSubset, ?_⟩
    intro heq
    apply hmissingBlock
    rw [heq]
    exact missing.2
  have hneighborhoodSubset :
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component stateBlock ⊆
        tokenBlock := by
    intro token htoken
    obtain ⟨_huniv, state, hstateBlock, hincident⟩ :=
      Finset.mem_filter.mp htoken
    have hstateSources := hstateSubset hstateBlock
    let tightState : ↑sources := ⟨state, hstateSources⟩
    obtain ⟨i, _hi, hstateEq⟩ := Finset.mem_map.mp hstateBlock
    have htightState : tightState = orbit.states i := by
      apply Subtype.ext
      exact hstateEq.symm
    have htokenSources : token ∈
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ token, state, hstateSources, hincident⟩
    let tightToken : ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) :=
      ⟨token, htokenSources⟩
    obtain ⟨q, htokenEq⟩ :=
      hsaturated tightState tightToken hincident ⟨i, htightState⟩
    apply Finset.mem_map.mpr
    exact ⟨q, Finset.mem_univ q, congrArg Subtype.val htokenEq.symm⟩
  have hhall := hproper stateBlock hstateProper
  have hstateCard : stateBlock.card = orbit.size + 1 := by
    simp [stateBlock]
  have htokenCard : tokenBlock.card = orbit.size := by
    simp [tokenBlock]
  have hneighborhoodCard :
      (canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component stateBlock).card ≤
        tokenBlock.card := Finset.card_le_card hneighborhoodSubset
  omega



theorem CanonicalStableRawTightChargeOrbit.SourceSaturated.tokens_exhaustive
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (hsaturated : orbit.SourceSaturated)
    (hstates : ∀ source : ↑sources, ∃ i, source = orbit.states i) :
    ∀ token : ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources),
      ∃ i, token = orbit.tokens i := by
  classical
  intro token
  obtain ⟨_huniv, source, hsource, hincident⟩ :=
    Finset.mem_filter.mp token.2
  let tightSource : ↑sources := ⟨source, hsource⟩
  obtain ⟨i, hi⟩ := hstates tightSource
  exact hsaturated tightSource token hincident ⟨i, hi⟩



theorem CanonicalStableRawTightChargeOrbit.SourceSaturated.exhaustive
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (hsaturated : orbit.SourceSaturated)
    (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      smaller ⊂ sources ->
        smaller.card ≤
          (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              smaller).card) :
    (∀ source : ↑sources, ∃ i, source = orbit.states i) ∧
      ∀ token : ↑(canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources),
        ∃ i, token = orbit.tokens i := by
  have hstates :=
    CanonicalStableRawTightChargeOrbit.SourceSaturated.exhaustive_of_properHall
      orbit hsaturated hproper
  exact ⟨hstates,
    CanonicalStableRawTightChargeOrbit.SourceSaturated.tokens_exhaustive
      orbit hsaturated hstates⟩





theorem CanonicalStableRawTightChargeOrbit.SourceSaturated.surplusNaturalDischarge
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (hsaturated : orbit.SourceSaturated) :
    ∃ q, canonicalStableRawComponentTightNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component sources
            (orbit.states 0) = orbit.tokens q ∧
      ((∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          u.target = canonicalStableRawLeftTokenTarget
              ends m j k l zero hloop hjk hkl hk0 p
                (canonicalStableRawComponentTightNaturalToken
                  ends m j k l zero hloop hjk hkl hk0 p hno component sources
                    (orbit.states 0)).1.1 ∧
          CanonicalStableRawOwnerStableOutput
              ends m j k l zero hloop hjk hkl hk0 p
                (orbit.states 0).1.1 u ∧
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          u.target = canonicalStableRawLeftTokenTarget
              ends m j k l zero hloop hjk hkl hk0 p
                (canonicalStableRawComponentTightNaturalToken
                  ends m j k l zero hloop hjk hkl hk0 p hno component sources
                    (orbit.states 0)).1.1 ∧
          CanonicalStableRawOwnerAdvancingOutput
              ends m j k l zero hloop hjk hkl hk0 p
                (orbit.states 0).1.1 u ∧
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component) := by
  let surplus : Fin (orbit.size + 1) := 0
  let natural := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
      (orbit.states surplus)
  have hnatural := canonicalStableRawComponentTightNaturalToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
      (orbit.states surplus)
  obtain ⟨q, hrepeat⟩ := hsaturated (orbit.states surplus) natural hnatural
    ⟨surplus, rfl⟩
  have hold : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (orbit.states q.succ).1 natural.1 := by
    have hpaired := orbit.paired q
    rw [← hrepeat] at hpaired
    exact hpaired
  have hindexNe : surplus ≠ q.succ := by
    intro heq
    have hval := congrArg Fin.val heq
    simp [surplus] at hval
  rcases canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
      ends m j k l zero hloop hjk hkl hk0 p hno natural.1
        (orbit.states surplus).1.1 (orbit.states q.succ).1.1
          hnatural hold with
    heq | ⟨u, htarget, hstable, hcomponent, _⟩ |
      ⟨u, htarget, hadvancing, hcomponent, _⟩
  · exfalso
    apply hindexNe
    apply orbit.states.injective
    apply Subtype.ext
    apply Subtype.ext
    exact heq
  · exact ⟨q, hrepeat, Or.inl
      ⟨u, htarget, hstable, hcomponent.trans (orbit.states surplus).1.2⟩⟩
  · exact ⟨q, hrepeat, Or.inr
      ⟨u, htarget, hadvancing, hcomponent.trans (orbit.states surplus).1.2⟩⟩






theorem
    CanonicalStableRawTightChargeOrbit.SourceSaturated.surplusNatural_rankSplit
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (hsaturated : orbit.SourceSaturated) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      (∃ q, ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          canonicalStableRawComponentTightNaturalToken
              ends m j k l zero hloop hjk hkl hk0 p hno component sources
                (orbit.states 0) = orbit.tokens q ∧
          u.target = canonicalStableRawLeftTokenTarget
              ends m j k l zero hloop hjk hkl hk0 p
                (canonicalStableRawComponentTightNaturalToken
                  ends m j k l zero hloop hjk hkl hk0 p hno component sources
                    (orbit.states 0)).1.1 ∧
          CanonicalStableRawOwnerStableOutput
              ends m j k l zero hloop hjk hkl hk0 p
                (orbit.states 0).1.1 u ∧
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨
      ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
        canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
          canonicalStableRawSourceRank ends m j k l zero p u.source <
            canonicalStableRawSourceRank ends m j k l zero p
              (orbit.states 0).1.1.source := by
  classical
  obtain ⟨q, hrepeat, hstable | hadvancing⟩ :=
    hsaturated.surplusNaturalDischarge orbit
  · obtain ⟨u, htarget, hstable, hcomponent⟩ := hstable
    exact Or.inr (Or.inl
      ⟨q, u, hrepeat, htarget, hstable, hcomponent⟩)
  · obtain ⟨u, htarget, hadvancing, hcomponent⟩ := hadvancing
    rcases canonicalStableRawComponent_tightState_terminal_or_crossCollision_or_direct
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          (orbit.states 0) with
      hterminal | ⟨collision, hself, _htoken⟩ | ⟨direct, hdirect⟩
    · exact Or.inl hterminal
    · have hsourceSelf : (orbit.states 0).1.1.target.1 =
          canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
            (orbit.states 0).1.1.source := by
        rw [hself]
        exact collision.1.1.2.2
      let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
        ⟨canonicalStableRawPreferredRightBase
            ends m j k l zero hloop hjk hkl hk0 p
              (orbit.states 0).1.1.target,
          canonicalStableRawPreferredRightBase_mem
            ends m j k l zero hloop hjk hkl hk0 p
              (orbit.states 0).1.1.target⟩
      have hownerRank : canonicalStableRawSourceRank
            ends m j k l zero p owner <
          canonicalStableRawSourceRank ends m j k l zero p
            (orbit.states 0).1.1.source :=
        canonicalStableRawPreferredRightBase_rank_lt_of_self
          ends m j k l zero hloop hjk hkl hk0 p
            (orbit.states 0).1.1.target (orbit.states 0).1.1.source
              hsourceSelf.symm (orbit.states 0).1.1.exceptional
      have huSource : u.source = owner := by
        apply Subtype.ext
        exact hadvancing
      exact Or.inr (Or.inr
        ⟨u, hcomponent, huSource ▸ hownerRank⟩)
    · have hsourceDirect : (orbit.states 0).1.1.target.1 ≠
          canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
            (orbit.states 0).1.1.source := by
        rw [hdirect]
        exact direct.2.2
      exact False.elim
        (canonicalStableRawOwnerAdvancingOutput_false_of_directNaturalTarget
          (orbit.states 0).1 hsourceDirect u htarget hadvancing)



theorem CanonicalStableRawTightChargeOrbit.tokenSaturated_or_crossing
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.TokenSaturated ∨
      ∃ source token,
        CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component
              source.1 token.1 ∧
          (∀ i, source ≠ orbit.states i) ∧ ∃ i, token = orbit.tokens i := by
  classical
  by_cases hsaturated : orbit.TokenSaturated
  · exact Or.inl hsaturated
  · right
    unfold CanonicalStableRawTightChargeOrbit.TokenSaturated at hsaturated
    push Not at hsaturated
    obtain ⟨source, token, hincident, hold, hfresh⟩ := hsaturated
    exact ⟨source, token, hincident, hfresh, hold⟩




theorem CanonicalStableRawTightChargeOrbit.extendByNatural_or_repeat
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (source : ↑sources) (hsource : ∀ i, source ≠ orbit.states i) :
    (∃ extended : CanonicalStableRawTightChargeOrbit
          ends m j k l zero hloop hjk hkl hk0 p hno component sources,
        extended.size = orbit.size + 1) ∨
      ∃ i, canonicalStableRawComponentTightNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component sources source =
        orbit.tokens i := by
  classical
  let charge := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources source
  by_cases hfresh : ∀ i, charge ≠ orbit.tokens i
  · left
    exact orbit.extendPair source charge hsource hfresh
      (canonicalStableRawComponentTightNaturalToken_incident
        ends m j k l zero hloop hjk hkl hk0 p hno component sources source)
      (Or.inl rfl)
  · right
    push Not at hfresh
    exact hfresh



theorem CanonicalStableRawTightChargeOrbit.extendBySuccessor_or_repeat
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (source : ↑sources) (hsource : ∀ i, source ≠ orbit.states i) :
    (∃ extended : CanonicalStableRawTightChargeOrbit
          ends m j k l zero hloop hjk hkl hk0 p hno component sources,
        extended.size = orbit.size + 1) ∨
      ∃ i, canonicalStableRawComponentTightSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component sources source =
        orbit.tokens i := by
  classical
  let charge := canonicalStableRawComponentTightSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources source
  by_cases hfresh : ∀ i, charge ≠ orbit.tokens i
  · left
    exact orbit.extendPair source charge hsource hfresh
      (canonicalStableRawComponentTightSuccessorToken_incident
        ends m j k l zero hloop hjk hkl hk0 p hno component sources source)
      (Or.inr rfl)
  · right
    push Not at hfresh
    exact hfresh



theorem CanonicalStableRawTightChargeOrbit.repeatedSuccessorDischarge
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (source : ↑sources) (hsource : ∀ i, source ≠ orbit.states i)
    (q : Fin orbit.size)
    (hrepeat : canonicalStableRawComponentTightSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component sources source =
      orbit.tokens q) :
    (∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
            ends m j k l zero hloop hjk hkl hk0 p
              (canonicalStableRawComponentTightSuccessorToken
                ends m j k l zero hloop hjk hkl hk0 p hno component sources
                  source).1.1 ∧
        CanonicalStableRawOwnerStableOutput
            ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
            ends m j k l zero hloop hjk hkl hk0 p
              (canonicalStableRawComponentTightSuccessorToken
                ends m j k l zero hloop hjk hkl hk0 p hno component sources
                  source).1.1 ∧
        CanonicalStableRawOwnerAdvancingOutput
            ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  let successor := canonicalStableRawComponentTightSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources source
  have hnew : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component source.1 successor.1 :=
    canonicalStableRawComponentTightSuccessorToken_incident
      ends m j k l zero hloop hjk hkl hk0 p hno component sources source
  have hold : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (orbit.states q.succ).1 successor.1 := by
    have hpaired := orbit.paired q
    rw [← hrepeat] at hpaired
    exact hpaired
  rcases canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
      ends m j k l zero hloop hjk hkl hk0 p hno successor.1
        source.1.1 (orbit.states q.succ).1.1 hnew hold with
    heq | ⟨u, htarget, hstable, hcomponent, _⟩ |
      ⟨u, htarget, hadvancing, hcomponent, _⟩
  · exact False.elim (hsource q.succ (Subtype.ext (Subtype.ext heq)))
  · exact Or.inl ⟨u, htarget, hstable, hcomponent.trans source.1.2⟩
  · exact Or.inr ⟨u, htarget, hadvancing, hcomponent.trans source.1.2⟩




theorem CanonicalStableRawTightChargeOrbit.repeatedNaturalDischarge
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (source : ↑sources) (hsource : ∀ i, source ≠ orbit.states i)
    (q : Fin orbit.size)
    (hrepeat : canonicalStableRawComponentTightNaturalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component sources source =
      orbit.tokens q) :
    (∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
            ends m j k l zero hloop hjk hkl hk0 p
              (canonicalStableRawComponentTightNaturalToken
                ends m j k l zero hloop hjk hkl hk0 p hno component sources
                  source).1.1 ∧
        CanonicalStableRawOwnerStableOutput
            ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
            ends m j k l zero hloop hjk hkl hk0 p
              (canonicalStableRawComponentTightNaturalToken
                ends m j k l zero hloop hjk hkl hk0 p hno component sources
                  source).1.1 ∧
        CanonicalStableRawOwnerAdvancingOutput
            ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  let natural := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources source
  have hnew : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component source.1 natural.1 :=
    canonicalStableRawComponentTightNaturalToken_incident
      ends m j k l zero hloop hjk hkl hk0 p hno component sources source
  have hold : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (orbit.states q.succ).1 natural.1 := by
    have hpaired := orbit.paired q
    rw [← hrepeat] at hpaired
    exact hpaired
  rcases canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
      ends m j k l zero hloop hjk hkl hk0 p hno natural.1
        source.1.1 (orbit.states q.succ).1.1 hnew hold with
    heq | ⟨u, htarget, hstable, hcomponent, _⟩ |
      ⟨u, htarget, hadvancing, hcomponent, _⟩
  · exact False.elim (hsource q.succ (Subtype.ext (Subtype.ext heq)))
  · exact Or.inl ⟨u, htarget, hstable, hcomponent.trans source.1.2⟩
  · exact Or.inr ⟨u, htarget, hadvancing, hcomponent.trans source.1.2⟩





theorem CanonicalStableRawTightChargeOrbit.saturationStep
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.TokenSaturated ∨
      (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      (∃ extended : CanonicalStableRawTightChargeOrbit
            ends m j k l zero hloop hjk hkl hk0 p hno component sources,
          extended.size = orbit.size + 1) ∨
      ∃ source : ↑sources, (∀ i, source ≠ orbit.states i) ∧
        ∃ q, canonicalStableRawComponentTightNaturalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component sources source =
          orbit.tokens q := by
  classical
  rcases orbit.tokenSaturated_or_crossing with hsaturated |
      ⟨source, _oldToken, _hcrossing, hsource, _hold⟩
  · exact Or.inl hsaturated
  · rcases canonicalStableRawComponent_tightState_terminal_or_crossCollision_or_direct
        ends m j k l zero hloop hjk hkl hk0 p hno component sources source with
      hterminal | _hcollision | _hdirect
    · exact Or.inr (Or.inl hterminal)
    · rcases orbit.extendByNatural_or_repeat source hsource with hextend | hrepeat
      · exact Or.inr (Or.inr (Or.inl hextend))
      · exact Or.inr (Or.inr (Or.inr ⟨source, hsource, hrepeat⟩))
    · rcases orbit.extendByNatural_or_repeat source hsource with hextend | hrepeat
      · exact Or.inr (Or.inr (Or.inl hextend))
      · exact Or.inr (Or.inr (Or.inr ⟨source, hsource, hrepeat⟩))



theorem CanonicalStableRawTightChargeOrbit.saturationStep_classified
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.TokenSaturated ∨
      (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      (∃ extended : CanonicalStableRawTightChargeOrbit
            ends m j k l zero hloop hjk hkl hk0 p hno component sources,
          extended.size = orbit.size + 1) ∨
      (∃ source : ↑sources,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          CanonicalStableRawOwnerStableOutput
              ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨
      ∃ source : ↑sources,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          CanonicalStableRawOwnerAdvancingOutput
              ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  rcases orbit.saturationStep with hsaturated | hterminal | hextended |
      ⟨source, hsource, q, hrepeat⟩
  · exact Or.inl hsaturated
  · exact Or.inr (Or.inl hterminal)
  · exact Or.inr (Or.inr (Or.inl hextended))
  · rcases orbit.repeatedNaturalDischarge source hsource q hrepeat with
      ⟨u, _htarget, hstable, hcomponent⟩ |
        ⟨u, _htarget, hadvancing, hcomponent⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨source, u, hstable, hcomponent⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨source, u, hadvancing, hcomponent⟩)))





theorem CanonicalStableRawTightChargeOrbit.saturationStep_rankSplit
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.TokenSaturated ∨
      (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      (∃ extended : CanonicalStableRawTightChargeOrbit
            ends m j k l zero hloop hjk hkl hk0 p hno component sources,
          extended.size = orbit.size + 1) ∨
      (∃ source : ↑sources,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          (∀ i, source ≠ orbit.states i) ∧
          (∃ r, canonicalStableRawComponentTightNaturalToken
              ends m j k l zero hloop hjk hkl hk0 p hno component sources source =
            orbit.tokens r) ∧
          u.target = canonicalStableRawLeftTokenTarget
              ends m j k l zero hloop hjk hkl hk0 p
                (canonicalStableRawComponentTightNaturalToken
                  ends m j k l zero hloop hjk hkl hk0 p hno component sources
                    source).1.1 ∧
          CanonicalStableRawOwnerStableOutput
              ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨
      ∃ source : ↑sources,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          canonicalStableRawTokenComponent
                ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
            canonicalStableRawSourceRank ends m j k l zero p u.source <
              canonicalStableRawSourceRank ends m j k l zero p
                source.1.1.source := by
  classical
  rcases orbit.saturationStep with hsaturated | hterminal | hextended |
      ⟨source, hsource, q, hrepeat⟩
  · exact Or.inl hsaturated
  · exact Or.inr (Or.inl hterminal)
  · exact Or.inr (Or.inr (Or.inl hextended))
  · rcases orbit.repeatedNaturalDischarge source hsource q hrepeat with
      ⟨u, htarget, hstable, hcomponent⟩ |
        ⟨u, htarget, hadvancing, hcomponent⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨source, u, hsource, ⟨q, hrepeat⟩,
          htarget, hstable, hcomponent⟩)))
    · rcases canonicalStableRawComponent_tightState_terminal_or_crossCollision_or_direct
          ends m j k l zero hloop hjk hkl hk0 p hno component sources source with
        hterminal | ⟨collision, hself, _htoken⟩ | ⟨direct, hdirect⟩
      · exact Or.inr (Or.inl hterminal)
      · have hsourceSelf : source.1.1.target.1 =
            canonicalStableRawSelfBase
              ends m j k l zero hloop hjk hkl hk0 p source.1.1.source := by
          rw [hself]
          exact collision.1.1.2.2
        let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
          ⟨canonicalStableRawPreferredRightBase
              ends m j k l zero hloop hjk hkl hk0 p source.1.1.target,
            canonicalStableRawPreferredRightBase_mem
              ends m j k l zero hloop hjk hkl hk0 p source.1.1.target⟩
        have hownerRank : canonicalStableRawSourceRank
              ends m j k l zero p owner <
            canonicalStableRawSourceRank
              ends m j k l zero p source.1.1.source :=
          canonicalStableRawPreferredRightBase_rank_lt_of_self
            ends m j k l zero hloop hjk hkl hk0 p source.1.1.target
              source.1.1.source hsourceSelf.symm source.1.1.exceptional
        have huSource : u.source = owner := by
          apply Subtype.ext
          exact hadvancing
        exact Or.inr (Or.inr (Or.inr (Or.inr
          ⟨source, u, hcomponent, huSource ▸ hownerRank⟩)))
      · have hsourceDirect : source.1.1.target.1 ≠
            canonicalStableRawSelfBase
              ends m j k l zero hloop hjk hkl hk0 p source.1.1.source := by
          rw [hdirect]
          exact direct.2.2
        exact False.elim
          (canonicalStableRawOwnerAdvancingOutput_false_of_directNaturalTarget
            source.1 hsourceDirect u htarget hadvancing)




def CanonicalStableRawTightChargeOrbit.HasStableSuccessorRepeat
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources) : Prop :=
  ∃ source : ↑sources,
    ∃ u : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p,
      (∀ i, source ≠ orbit.states i) ∧
      (∃ r, canonicalStableRawComponentTightNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component sources source =
        orbit.tokens r) ∧
      u.target = canonicalStableRawLeftTokenTarget
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawComponentTightNaturalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component sources
              source).1.1 ∧
      CanonicalStableRawOwnerStableOutput
        ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧
      canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
      ∃ q, canonicalStableRawComponentTightSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component sources source =
        orbit.tokens q




theorem CanonicalStableRawTightChargeOrbit.saturationStep_grow_or_rankDrop_or_repeat
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.TokenSaturated ∨
      (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      (∃ extended : CanonicalStableRawTightChargeOrbit
            ends m j k l zero hloop hjk hkl hk0 p hno component sources,
          extended.size = orbit.size + 1) ∨
      (∃ source : ↑sources,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          canonicalStableRawTokenComponent
                ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
            canonicalStableRawSourceRank ends m j k l zero p u.source <
              canonicalStableRawSourceRank ends m j k l zero p
                source.1.1.source) ∨
      orbit.HasStableSuccessorRepeat := by
  rcases orbit.saturationStep_rankSplit with hsaturated | hterminal |
      hextended | ⟨source, u, hsource, hnaturalRepeat,
        htarget, hstable, hcomponent⟩ | hrank
  · exact Or.inl hsaturated
  · exact Or.inr (Or.inl hterminal)
  · exact Or.inr (Or.inr (Or.inl hextended))
  · rcases orbit.extendBySuccessor_or_repeat source hsource with
      hextended | hrepeat
    · exact Or.inr (Or.inr (Or.inl hextended))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨source, u, hsource, hnaturalRepeat,
          htarget, hstable, hcomponent, hrepeat⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hrank)))




theorem CanonicalStableRawTightChargeOrbit.HasStableSuccessorRepeat.originSplit
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (hobstruction : orbit.HasStableSuccessorRepeat) :
    (∃ source : ↑sources, ∃ q : Fin orbit.size,
        (∀ i, source ≠ orbit.states i) ∧
        canonicalStableRawComponentTightSuccessorToken
            ends m j k l zero hloop hjk hkl hk0 p hno component sources source =
          canonicalStableRawComponentTightNaturalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component sources
              (orbit.states q.succ)) ∨
      (∃ source : ↑sources, ∃ q : Fin orbit.size,
        source.1 ≠ (orbit.states q.succ).1 ∧
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component source.1 =
          canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (orbit.states q.succ).1) ∨
      ∃ source : ↑sources,
        (∀ i, source ≠ orbit.states i) ∧
        canonicalStableRawComponentTightSuccessorToken
            ends m j k l zero hloop hjk hkl hk0 p hno component sources source =
          orbit.tokens orbit.coreFirst := by
  obtain ⟨source, _u, hsource, _hnaturalRepeat, _htarget, _hstable,
      _hcomponent, q, hsuccessorRepeat⟩ := hobstruction
  rcases orbit.origin q with hnatural | hsuccessor | hcore
  · exact Or.inl ⟨source, q, hsource, hsuccessorRepeat.trans hnatural⟩
  · right
    left
    refine ⟨source, q, ?_, ?_⟩
    · intro heq
      exact hsource q.succ (Subtype.ext heq)
    · apply canonicalStableRawComponentForestStep_eq_of_tightSuccessorToken_eq
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
      exact hsuccessorRepeat.trans hsuccessor
  · exact Or.inr (Or.inr
      ⟨source, hsource, hsuccessorRepeat.trans (congrArg orbit.tokens hcore)⟩)




theorem CanonicalStableRawTightChargeOrbit.saturationStep_grow_or_rankDrop_or_merger
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    orbit.TokenSaturated ∨
      (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      (∃ extended : CanonicalStableRawTightChargeOrbit
            ends m j k l zero hloop hjk hkl hk0 p hno component sources,
          extended.size = orbit.size + 1) ∨
      (∃ source : ↑sources,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          canonicalStableRawTokenComponent
                ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
            canonicalStableRawSourceRank ends m j k l zero p u.source <
              canonicalStableRawSourceRank ends m j k l zero p
                source.1.1.source) ∨
      ∃ x y : ↑sources,
        x.1 ≠ y.1 ∧
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component x.1 =
          canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component y.1 := by
  rcases orbit.saturationStep_grow_or_rankDrop_or_repeat with
    hsaturated | hterminal | hextended | hrank | _hrepeat
  · exact Or.inl hsaturated
  · exact Or.inr (Or.inl hterminal)
  · exact Or.inr (Or.inr (Or.inl hextended))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hrank)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (exists_canonicalStableRawTightComponentForestStepMerger
        ends m j k l zero hloop hjk hkl hk0 p hno component sources htight))))



def CanonicalStableRawTightChargeOrbit.LocalMergerDischarge
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (_orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources) : Prop :=
  (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
    Nonempty (Fin 3 ↪
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨
    ∃ second : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component),
      canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component second.1.2 ∈
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources




theorem CanonicalStableRawTightChargeOrbit.saturationStep_localDischarge
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    orbit.TokenSaturated ∨
      (∃ extended : CanonicalStableRawTightChargeOrbit
            ends m j k l zero hloop hjk hkl hk0 p hno component sources,
          extended.size = orbit.size + 1) ∨
      (∃ source : ↑sources,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          canonicalStableRawTokenComponent
                ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
            canonicalStableRawSourceRank ends m j k l zero p u.source <
              canonicalStableRawSourceRank ends m j k l zero p
                source.1.1.source) ∨
      orbit.LocalMergerDischarge := by
  rcases orbit.saturationStep_grow_or_rankDrop_or_merger htight with
    hsaturated | hterminal | hextended | hrank | ⟨x, y, hne, hmerge⟩
  · exact Or.inl hsaturated
  · exact Or.inr (Or.inr (Or.inr (Or.inl hterminal)))
  · exact Or.inr (Or.inl hextended)
  · exact Or.inr (Or.inr (Or.inl hrank))
  · exact Or.inr (Or.inr (Or.inr
      (canonicalStableRawComponentForestStepMerger_localDischarge
        ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
          x y (fun hxy => hne (congrArg Subtype.val hxy)) hmerge)))







theorem CanonicalStableRawTightChargeOrbit.sourceSaturationStep
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      (∃ extended : CanonicalStableRawTightChargeOrbit
            ends m j k l zero hloop hjk hkl hk0 p hno component sources,
          extended.size = orbit.size + 1) ∨
      (∃ source : ↑sources,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          CanonicalStableRawOwnerStableOutput
              ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨
      (∃ source : ↑sources,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          CanonicalStableRawOwnerAdvancingOutput
              ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨
      ∃ source : ↑sources,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          canonicalStableRawTokenComponent
                ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
            canonicalStableRawSourceRank ends m j k l zero p u.source <
              canonicalStableRawSourceRank ends m j k l zero p
                source.1.1.source := by
  rcases orbit.sourceSaturated_or_external_or_chord herase with
    hsaturated | ⟨external, _token, _hincident, hfresh, _htokenFresh⟩ |
      ⟨q, r, hqr, token, hq, hr, _htokenFresh⟩
  · rcases hsaturated.surplusNatural_rankSplit orbit with
      hterminal | ⟨_index, u, _hrepeat, _htarget, hstable, hcomponent⟩ |
        ⟨u, hcomponent, hrank⟩
    · exact Or.inl hterminal
    · exact Or.inr (Or.inr (Or.inl
        ⟨orbit.states 0, u, hstable, hcomponent⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨orbit.states 0, u, hcomponent, hrank⟩)))
  · rcases orbit.extendByNatural_or_repeat external hfresh with
      hextended | ⟨index, hrepeat⟩
    · exact Or.inr (Or.inl hextended)
    · rcases orbit.repeatedNaturalDischarge external hfresh index hrepeat with
        ⟨u, _htarget, hstable, hcomponent⟩ |
          ⟨u, _htarget, hadvancing, hcomponent⟩
      · exact Or.inr (Or.inr (Or.inl
          ⟨external, u, hstable, hcomponent⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨external, u, hadvancing, hcomponent⟩)))
  · rcases orbit.internalChordClassification q r hqr token hq hr with
      ⟨u, _htarget, hstable, hcomponent⟩ |
        ⟨u, _htarget, hadvancing, hcomponent⟩
    · exact Or.inr (Or.inr (Or.inl
        ⟨orbit.states q, u, hstable, hcomponent⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨orbit.states q, u, hadvancing, hcomponent⟩)))





theorem
    CanonicalStableRawTightChargeOrbit.bidirectionalSaturationStep_localDischarge
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    (∃ extended : CanonicalStableRawTightChargeOrbit
          ends m j k l zero hloop hjk hkl hk0 p hno component sources,
        extended.size = orbit.size + 1) ∨
      (∃ source : ↑sources,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          CanonicalStableRawOwnerStableOutput
              ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨
      (∃ source : ↑sources,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          CanonicalStableRawOwnerAdvancingOutput
              ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨
      (∃ source : ↑sources,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          canonicalStableRawTokenComponent
                ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
            canonicalStableRawSourceRank ends m j k l zero p u.source <
              canonicalStableRawSourceRank ends m j k l zero p
                source.1.1.source) ∨
      orbit.LocalMergerDischarge := by
  rcases orbit.saturationStep_localDischarge herase htight with
    htokenSaturated | hextended | hrank | hlocal
  · rcases orbit.sourceSaturationStep herase with
      hterminal | hextended | hstable | hadvancing | hrank
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hterminal))))
    · exact Or.inl hextended
    · exact Or.inr (Or.inl hstable)
    · exact Or.inr (Or.inr (Or.inl hadvancing))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hrank)))
  · exact Or.inl hextended
  · exact Or.inr (Or.inr (Or.inr (Or.inl hrank)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hlocal)))



theorem exists_canonicalStableRawTightComponent_initialChargeFamily
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    let TightState := ↑sources
    let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    let incident : TightState -> TightToken -> Prop := fun state token =>
      CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1
    let natural := canonicalStableRawComponentTightNaturalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
    let hnatural := canonicalStableRawComponentTightNaturalToken_incident
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
    ∃ family : FiniteRelationDeficiencyOneFamily TightState TightToken,
      ∃ state : StatMech.FrontierA.RelationPartialMatching.HoleState incident,
        ∃ third : TightState, ∃ first : TightToken,
          family.states =
              {state.hole, (state.move natural hnatural).hole, third} ∧
          family.tokens = {natural state.hole, first} ∧
          incident state.hole (natural state.hole) ∧
          incident (state.move natural hnatural).hole (natural state.hole) ∧
          incident state.hole first ∧ incident third first := by
  classical
  dsimp only
  let TightState := ↑sources
  let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  let incident : TightState -> TightToken -> Prop := fun state token =>
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1
  let natural := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  let hnatural := canonicalStableRawComponentTightNaturalToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  obtain ⟨state, _collision, third, first, _hself, _hdirect,
      hthirdNeHole, hthirdNeDirect, hholeNeDirect, _hfirst,
      hnaturalNeFirst, hselfNatural, hdirectNatural,
      hselfFirst, hthirdFirst⟩ :=
    exists_canonicalStableRawTightComponent_threeStateTwoTokenPeelData
      ends m j k l zero hloop hjk hkl hk0 p hno component sources htight
  let family : FiniteRelationDeficiencyOneFamily TightState TightToken :=
    FiniteRelationDeficiencyOneFamily.threeTwo
      state.hole (state.move natural hnatural).hole third
      hholeNeDirect hthirdNeHole.symm hthirdNeDirect.symm
      (natural state.hole) first hnaturalNeFirst
  exact ⟨family, state, third, first, rfl, rfl,
    hselfNatural, hdirectNatural, hselfFirst, hthirdFirst⟩




theorem exists_canonicalStableRawTightComponent_initialChargeOrbit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    ∃ orbit : CanonicalStableRawTightChargeOrbit
        ends m j k l zero hloop hjk hkl hk0 p hno component sources,
      orbit.size = 2 := by
  classical
  let natural := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  let hnatural := canonicalStableRawComponentTightNaturalToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  obtain ⟨state, collision, third, first, hself, hdirect,
      hthirdNeHole, hthirdNeDirect, hholeNeDirect, _hfirst,
      hnaturalNeFirst, hselfNatural, hdirectNatural,
      hselfFirst, hthirdFirst⟩ :=
    exists_canonicalStableRawTightComponent_threeStateTwoTokenPeelData
      ends m j k l zero hloop hjk hkl hk0 p hno component sources htight
  let direct := (state.move natural hnatural).hole
  let stateMap : Fin 3 -> ↑sources := fun i =>
    Fin.cases state.hole (fun q => Fin.cases direct (fun _ => third) q) i
  have hstateInjective : Function.Injective stateMap := by
    intro x y hxy
    fin_cases x <;> fin_cases y
    · rfl
    · exact False.elim (hholeNeDirect hxy)
    · exact False.elim (hthirdNeHole hxy.symm)
    · exact False.elim (hholeNeDirect hxy.symm)
    · rfl
    · exact False.elim (hthirdNeDirect hxy.symm)
    · exact False.elim (hthirdNeHole hxy)
    · exact False.elim (hthirdNeDirect hxy)
    · rfl
  let states : Fin 3 ↪ ↑sources := ⟨stateMap, hstateInjective⟩
  let tokenMap : Fin 2 ->
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) :=
    fun i => Fin.cases (natural state.hole) (fun _ => first) i
  have htokenInjective : Function.Injective tokenMap := by
    intro x y hxy
    fin_cases x <;> fin_cases y
    · rfl
    · exact False.elim (hnaturalNeFirst hxy)
    · exact False.elim (hnaturalNeFirst hxy.symm)
    · rfl
  let tokens : Fin 2 ↪
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) :=
    ⟨tokenMap, htokenInjective⟩
  let coreSelf : Fin 3 := ⟨0, by omega⟩
  let coreDirect : Fin 3 := ⟨1, by omega⟩
  let coreThird : Fin 3 := ⟨2, by omega⟩
  let coreNatural : Fin 2 := ⟨0, by omega⟩
  let coreFirst : Fin 2 := ⟨1, by omega⟩
  have hnaturalEq : natural state.hole = natural direct := by
    apply Subtype.ext
    apply Subtype.ext
    change canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno state.hole.1.1 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno direct.1.1
    rw [hself, hdirect]
    exact congrArg Subtype.val collision.2
  refine ⟨⟨2, states, tokens, ?_, coreSelf, coreDirect, coreThird,
    coreNatural, coreFirst, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · intro i
    fin_cases i
    · simpa [states, stateMap, tokens, tokenMap, direct] using hdirectNatural
    · simpa [states, stateMap, tokens, tokenMap] using hthirdFirst
  · intro i
    fin_cases i
    · exact Or.inl (by
        simpa [states, stateMap, tokens, tokenMap, direct] using hnaturalEq)
    · exact Or.inr (Or.inr (by simp [coreFirst]))
  · simp [coreSelf, coreDirect]
  · simp [coreSelf, coreThird]
  · simp [coreDirect, coreThird]
  · simp [coreNatural, coreFirst]
  · simpa [states, stateMap, tokens, tokenMap, coreSelf, coreNatural] using
      hselfNatural
  · simpa [states, stateMap, tokens, tokenMap, coreDirect, coreNatural,
      direct] using hdirectNatural
  · simpa [states, stateMap, tokens, tokenMap, coreSelf, coreFirst] using
      hselfFirst
  · simpa [states, stateMap, tokens, tokenMap, coreThird, coreFirst] using
      hthirdFirst




def CanonicalStableRawTightChargeOrbit.HasRetainedSharedTokenOutput
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources) : Prop :=
  ∃ source : ↑sources,
    ∃ q : Fin orbit.size,
      ∃ token : ↑(canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources),
        ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
          source ≠ orbit.states q.succ ∧
          source = orbit.states 0 ∧
          token = canonicalStableRawComponentTightNaturalToken
              ends m j k l zero hloop hjk hkl hk0 p hno component sources
                source ∧
          token = orbit.tokens q ∧
          CanonicalStableRawComponentIncident
              ends m j k l zero hloop hjk hkl hk0 p hno component
                source.1 token.1 ∧
          CanonicalStableRawComponentIncident
              ends m j k l zero hloop hjk hkl hk0 p hno component
                (orbit.states q.succ).1 token.1 ∧
          u.target = canonicalStableRawLeftTokenTarget
              ends m j k l zero hloop hjk hkl hk0 p token.1.1 ∧
          (CanonicalStableRawOwnerStableOutput
                ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∨
            CanonicalStableRawOwnerAdvancingOutput
                ends m j k l zero hloop hjk hkl hk0 p source.1.1 u) ∧
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component



def CanonicalStableRawTightChargeOrbit.HasFreshInternalChordOutput
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources) : Prop :=
  ∃ q r : Fin (orbit.size + 1),
    ∃ token : ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources),
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        q ≠ r ∧
        (∀ s, token ≠ orbit.tokens s) ∧
        CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (orbit.states q).1 token.1 ∧
        CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (orbit.states r).1 token.1 ∧
        u.target = canonicalStableRawLeftTokenTarget
            ends m j k l zero hloop hjk hkl hk0 p token.1.1 ∧
        (CanonicalStableRawOwnerStableOutput
              ends m j k l zero hloop hjk hkl hk0 p (orbit.states q).1.1 u ∨
          CanonicalStableRawOwnerAdvancingOutput
              ends m j k l zero hloop hjk hkl hk0 p (orbit.states q).1.1 u) ∧
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u = component




theorem exists_canonicalStableRawTightComponent_sizeMaximalChargeOrbit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    ∃ orbit : CanonicalStableRawTightChargeOrbit
        ends m j k l zero hloop hjk hkl hk0 p hno component sources,
      2 ≤ orbit.size ∧
      ∀ other : CanonicalStableRawTightChargeOrbit
          ends m j k l zero hloop hjk hkl hk0 p hno component sources,
        other.size ≤ orbit.size := by
  classical
  obtain ⟨start, hstart⟩ :=
    exists_canonicalStableRawTightComponent_initialChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources htight
  have hbound : ∀ orbit : CanonicalStableRawTightChargeOrbit
        ends m j k l zero hloop hjk hkl hk0 p hno component sources,
      orbit.size ≤ sources.card := by
    intro orbit
    have hcard := Fintype.card_le_of_injective
      orbit.states orbit.states.injective
    simp only [Fintype.card_fin, Fintype.card_coe] at hcard
    omega
  obtain ⟨orbit, hmax⟩ := exists_sizeMaximalBlock sources.card
    (fun orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources => orbit.size)
    hbound start
  refine ⟨orbit, ?_, hmax⟩
  have hstartMax := hmax start
  rw [hstart] at hstartMax
  exact hstartMax






theorem
    CanonicalStableRawTightChargeOrbit.TokenSaturated.exhaustive_of_sizeMaximal
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (hsaturated : orbit.TokenSaturated)
    (hmax : ∀ other : CanonicalStableRawTightChargeOrbit
        ends m j k l zero hloop hjk hkl hk0 p hno component sources,
      other.size ≤ orbit.size)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    (∀ source : ↑sources, ∃ i, source = orbit.states i) ∧
      (∀ token : ↑(canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources),
        ∃ i, token = orbit.tokens i) ∧
      orbit.SourceSaturated := by
  classical
  have hstates : ∀ source : ↑sources, ∃ i, source = orbit.states i := by
    intro source
    by_contra hmissing
    push Not at hmissing
    rcases orbit.extendByNatural_or_repeat source hmissing with
      ⟨extended, hextended⟩ | ⟨q, hrepeat⟩
    · have hle := hmax extended
      omega
    · let token := canonicalStableRawComponentTightNaturalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component sources source
      have hincident : CanonicalStableRawComponentIncident
          ends m j k l zero hloop hjk hkl hk0 p hno component
            source.1 token.1 :=
        canonicalStableRawComponentTightNaturalToken_incident
          ends m j k l zero hloop hjk hkl hk0 p hno component sources source
      obtain ⟨i, hi⟩ := hsaturated source token hincident ⟨q, hrepeat⟩
      exact hmissing i hi
  have hstateSurjective : Function.Surjective orbit.states := by
    intro source
    obtain ⟨i, hi⟩ := hstates source
    exact ⟨i, hi.symm⟩
  have hstateCard : orbit.size + 1 = sources.card := by
    have hcard := Fintype.card_congr
      (Equiv.ofBijective orbit.states
        ⟨orbit.states.injective, hstateSurjective⟩)
    simpa only [Fintype.card_fin, Fintype.card_coe] using hcard
  have htokenCard : Fintype.card (Fin orbit.size) =
      Fintype.card ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) := by
    simp only [Fintype.card_fin, Fintype.card_coe]
    omega
  have htokenBijective : Function.Bijective orbit.tokens :=
    (Fintype.bijective_iff_injective_and_card orbit.tokens).2
      ⟨orbit.tokens.injective, htokenCard⟩
  have htokens : ∀ token : ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources),
      ∃ i, token = orbit.tokens i := by
    intro token
    obtain ⟨i, hi⟩ := htokenBijective.2 token
    exact ⟨i, hi.symm⟩
  have hsourceSaturated : orbit.SourceSaturated := by
    intro _source token _hincident _hsource
    exact htokens token
  exact ⟨hstates, htokens, hsourceSaturated⟩





theorem
    CanonicalStableRawTightChargeOrbit.maximalSaturationStep_localDischarge
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (hmax : ∀ other : CanonicalStableRawTightChargeOrbit
        ends m j k l zero hloop hjk hkl hk0 p hno component sources,
      other.size ≤ orbit.size)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    orbit.HasRetainedSharedTokenOutput ∨
      orbit.HasFreshInternalChordOutput ∨
      (∃ source : ↑sources,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          canonicalStableRawTokenComponent
                ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
            canonicalStableRawSourceRank ends m j k l zero p u.source <
              canonicalStableRawSourceRank ends m j k l zero p
                source.1.1.source) ∨
      orbit.LocalMergerDischarge := by
  have hnoGrowth : ¬ ∃ extended : CanonicalStableRawTightChargeOrbit
        ends m j k l zero hloop hjk hkl hk0 p hno component sources,
      extended.size = orbit.size + 1 := by
    rintro ⟨extended, hextended⟩
    have := hmax extended
    omega
  rcases orbit.saturationStep_localDischarge herase htight with
    htokenSaturated | hextended | hrank | hlocal
  · rcases orbit.sourceSaturated_or_external_or_chord herase with
      hsaturated | ⟨external, _fresh, _hincident, hfresh, _hfreshToken⟩ |
        ⟨q, r, hqr, token, hq, hr, hfreshToken⟩
    · rcases hsaturated.surplusNatural_rankSplit orbit with
        hterminal | ⟨q, u, hrepeat, htarget, hstable, hcomponent⟩ |
          ⟨u, hcomponent, hrank⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl hterminal)))
      · let source := orbit.states (0 : Fin (orbit.size + 1))
        let token := canonicalStableRawComponentTightNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component sources source
        have hsourceIncident : CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component
              source.1 token.1 :=
          canonicalStableRawComponentTightNaturalToken_incident
            ends m j k l zero hloop hjk hkl hk0 p hno component sources source
        have hpairedIncident : CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (orbit.states q.succ).1 token.1 := by
          have hpaired := orbit.paired q
          rw [← hrepeat] at hpaired
          exact hpaired
        have hsourceNe : source ≠ orbit.states q.succ := by
          intro heq
          have hindex := orbit.states.injective heq
          have hval := congrArg Fin.val hindex
          simp [source] at hval
        exact Or.inl
          ⟨source, q, token, u, hsourceNe, rfl, rfl, hrepeat,
            hsourceIncident, hpairedIncident, htarget, Or.inl hstable,
            hcomponent⟩
      · exact Or.inr (Or.inr (Or.inl
          ⟨orbit.states 0, u, hcomponent, hrank⟩))
    · rcases orbit.extendByNatural_or_repeat external hfresh with
        hextended | ⟨q, hrepeat⟩
      · exact False.elim (hnoGrowth hextended)
      · let token := canonicalStableRawComponentTightNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component sources external
        have hexternalIncident : CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component
              external.1 token.1 :=
          canonicalStableRawComponentTightNaturalToken_incident
            ends m j k l zero hloop hjk hkl hk0 p hno component sources external
        obtain ⟨i, hi⟩ := htokenSaturated external token hexternalIncident
          ⟨q, hrepeat⟩
        exact False.elim (hfresh i hi)
    · rcases orbit.internalChordClassification q r hqr token hq hr with
        ⟨u, htarget, hstable, hcomponent⟩ |
          ⟨u, htarget, hadvancing, hcomponent⟩
      · exact Or.inr (Or.inl
          ⟨q, r, token, u, hqr, hfreshToken, hq, hr, htarget,
            Or.inl hstable, hcomponent⟩)
      · exact Or.inr (Or.inl
          ⟨q, r, token, u, hqr, hfreshToken, hq, hr, htarget,
            Or.inr hadvancing, hcomponent⟩)
  · exact False.elim (hnoGrowth hextended)
  · exact Or.inr (Or.inr (Or.inl hrank))
  · exact Or.inr (Or.inr (Or.inr hlocal))




theorem
    CanonicalStableRawTightChargeOrbit.maximalSaturationStep_sharp
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (hmax : ∀ other : CanonicalStableRawTightChargeOrbit
        ends m j k l zero hloop hjk hkl hk0 p hno component sources,
      other.size ≤ orbit.size)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    orbit.HasRetainedSharedTokenOutput ∨
      (∃ source : ↑sources,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          canonicalStableRawTokenComponent
                ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
            canonicalStableRawSourceRank ends m j k l zero p u.source <
              canonicalStableRawSourceRank ends m j k l zero p
                source.1.1.source) ∨
      orbit.LocalMergerDischarge := by
  have hnoGrowth : ¬ ∃ extended : CanonicalStableRawTightChargeOrbit
        ends m j k l zero hloop hjk hkl hk0 p hno component sources,
      extended.size = orbit.size + 1 := by
    rintro ⟨extended, hextended⟩
    have hle := hmax extended
    omega
  rcases orbit.saturationStep_localDischarge herase htight with
    htokenSaturated | hextended | hrank | hlocal
  · obtain ⟨_hstates, _htokens, hsourceSaturated⟩ :=
      htokenSaturated.exhaustive_of_sizeMaximal orbit hmax htight
    rcases hsourceSaturated.surplusNatural_rankSplit orbit with
      hterminal | ⟨q, u, hrepeat, htarget, hstable, hcomponent⟩ |
        ⟨u, hcomponent, hrank⟩
    · exact Or.inr (Or.inr (Or.inl hterminal))
    · let source := orbit.states (0 : Fin (orbit.size + 1))
      let token := canonicalStableRawComponentTightNaturalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component sources source
      have hsourceIncident : CanonicalStableRawComponentIncident
          ends m j k l zero hloop hjk hkl hk0 p hno component
            source.1 token.1 :=
        canonicalStableRawComponentTightNaturalToken_incident
          ends m j k l zero hloop hjk hkl hk0 p hno component sources source
      have hpairedIncident : CanonicalStableRawComponentIncident
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (orbit.states q.succ).1 token.1 := by
        have hpaired := orbit.paired q
        rw [← hrepeat] at hpaired
        exact hpaired
      have hsourceNe : source ≠ orbit.states q.succ := by
        intro heq
        have hindex := orbit.states.injective heq
        have hval := congrArg Fin.val hindex
        simp [source] at hval
      exact Or.inl
        ⟨source, q, token, u, hsourceNe, rfl, rfl, hrepeat,
          hsourceIncident, hpairedIncident, htarget, Or.inl hstable,
          hcomponent⟩
    · exact Or.inr (Or.inl ⟨orbit.states 0, u, hcomponent, hrank⟩)
  · exact False.elim (hnoGrowth hextended)
  · exact Or.inr (Or.inl hrank)
  · exact Or.inr (Or.inr hlocal)




theorem canonicalStableRawComponent_squareOutput_tightDirect_or_self
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (state : ↑sources)
    (token : ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources))
    (hincident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1)
    (u : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (htarget : u.target = canonicalStableRawLeftTokenTarget
      ends m j k l zero hloop hjk hkl hk0 p token.1.1)
    (hkind : CanonicalStableRawOwnerStableOutput
        ends m j k l zero hloop hjk hkl hk0 p state.1.1 u ∨
      CanonicalStableRawOwnerAdvancingOutput
        ends m j k l zero hloop hjk hkl hk0 p state.1.1 u)
    (hcomponent : canonicalStableRawTokenComponent
      ends m j k l zero hloop hjk hkl hk0 p hno u = component) :
    Nonempty (CanonicalStableRawComponentTightDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      Nonempty (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  by_cases huDirect : u.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p u.source
  · let direct : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨u, hcomponent, huDirect⟩
    have hmem := canonicalStableRawComponent_directOutput_mem_tightNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
        state token hincident u htarget hkind hcomponent huDirect
    exact Or.inl ⟨⟨direct, hmem⟩⟩
  · have huSelf : u.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p u.source :=
      Classical.not_not.mp huDirect
    exact Or.inr ⟨⟨u, hcomponent, huSelf⟩⟩



theorem
    CanonicalStableRawTightChargeOrbit.HasRetainedSharedTokenOutput.direct_or_self
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (houtput : orbit.HasRetainedSharedTokenOutput) :
    Nonempty (CanonicalStableRawComponentTightDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      Nonempty (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  obtain ⟨source, _q, token, u, _hne, _horigin, _hnatural, _hrepeat,
      hsourceIncident, _hpairedIncident, htarget, hkind, hcomponent⟩ := houtput
  exact canonicalStableRawComponent_squareOutput_tightDirect_or_self
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
      source token hsourceIncident u htarget hkind hcomponent



theorem
    CanonicalStableRawTightChargeOrbit.HasFreshInternalChordOutput.direct_or_self
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (houtput : orbit.HasFreshInternalChordOutput) :
    Nonempty (CanonicalStableRawComponentTightDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      Nonempty (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  obtain ⟨q, _r, token, u, _hqr, _hfresh, hq, _hr,
      htarget, hkind, hcomponent⟩ := houtput
  exact canonicalStableRawComponent_squareOutput_tightDirect_or_self
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
      (orbit.states q) token hq u htarget hkind hcomponent




theorem canonicalStableRawComponent_directNaturalSquareOutput_eq
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (source : ↑sources)
    (token : ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources))
    (hnatural : token = canonicalStableRawComponentTightNaturalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component sources source)
    (u : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (htarget : u.target = canonicalStableRawLeftTokenTarget
      ends m j k l zero hloop hjk hkl hk0 p token.1.1)
    (hkind : CanonicalStableRawOwnerStableOutput
        ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∨
      CanonicalStableRawOwnerAdvancingOutput
        ends m j k l zero hloop hjk hkl hk0 p source.1.1 u)
    (hdirect : source.1.1.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p source.1.1.source) :
    CanonicalStableRawOwnerStableOutput
        ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧
      u = source.1.1 := by
  rw [hnatural] at htarget
  rcases hkind with hstable | hadvancing
  · exact ⟨hstable,
      canonicalStableRawOwnerStableOutput_eq_of_directNaturalTarget
        source.1 hdirect u htarget hstable⟩
  · exact False.elim
      (canonicalStableRawOwnerAdvancingOutput_false_of_directNaturalTarget
        source.1 hdirect u htarget hadvancing)




theorem canonicalStableRawComponent_directNaturalIncidence_endpointSplit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (firstState secondState : ↑sources)
    (first second : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hfirst : firstState.1.1 = first.1)
    (hsecond : secondState.1.1 = second.1)
    (token : ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources))
    (hnatural : token = canonicalStableRawComponentTightNaturalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component sources firstState)
    (hsecondIncident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        secondState.1 token.1) :
    first.1.source = second.1.source ∨
      first.1.source =
        ⟨canonicalStableRawPreferredRightBase
            ends m j k l zero hloop hjk hkl hk0 p second.1.target,
          canonicalStableRawPreferredRightBase_mem
            ends m j k l zero hloop hjk hkl hk0 p second.1.target⟩ := by
  have htokenSource : token.1.1.1 = first.1.source := by
    rw [hnatural]
    change (canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno firstState.1.1).1 =
      first.1.source
    rw [hfirst]
    unfold canonicalStableRawStateLeftToken
    rw [dif_neg first.2.2]
    rfl
  have hraw := (canonicalStableRawWitnessedStateTokenIncidence_iff
    ends m j k l zero hloop hjk hkl hk0 p token.1.1 secondState.1.1).1
      hsecondIncident
  rcases hraw.1 with hsource | howner
  · left
    calc
      first.1.source = token.1.1.1 := htokenSource.symm
      _ = secondState.1.1.source := hsource
      _ = second.1.source := congrArg
        (fun state : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p => state.source) hsecond
  · right
    calc
      first.1.source = token.1.1.1 := htokenSource.symm
      _ = ⟨canonicalStableRawPreferredRightBase
            ends m j k l zero hloop hjk hkl hk0 p secondState.1.1.target,
          canonicalStableRawPreferredRightBase_mem
            ends m j k l zero hloop hjk hkl hk0 p
              secondState.1.1.target⟩ := howner
      _ = ⟨canonicalStableRawPreferredRightBase
            ends m j k l zero hloop hjk hkl hk0 p second.1.target,
          canonicalStableRawPreferredRightBase_mem
            ends m j k l zero hloop hjk hkl hk0 p second.1.target⟩ := by
        rw [hsecond]





theorem canonicalStableRawComponent_directPair_threeTokens_or_firstStep
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (firstState secondState : ↑sources)
    (first second : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hne : first ≠ second)
    (hfirst : firstState.1.1 = first.1)
    (hsecond : secondState.1.1 = second.1) :
    Nonempty (Fin 3 ↪
        ↑(canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨
      canonicalStableRawComponentForestStep
          ends m j k l zero hloop hjk hkl hk0 p hno component firstState.1 =
        Sum.inl second := by
  let firstNatural := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources firstState
  let secondNatural := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources secondState
  let firstSuccessor := canonicalStableRawComponentTightSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources firstState
  have hfirstNatural : firstNatural.1 =
      canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component first := by
    apply Subtype.ext
    change canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno firstState.1.1 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno first.1
    rw [hfirst]
  have hsecondNatural : secondNatural.1 =
      canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component second := by
    apply Subtype.ext
    change canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno secondState.1.1 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno second.1
    rw [hsecond]
  have hnaturalsNe : firstNatural ≠ secondNatural := by
    intro heq
    apply hne
    apply (canonicalStableRawComponentDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component).injective
    exact hfirstNatural.symm.trans
      ((congrArg Subtype.val heq).trans hsecondNatural)
  have hsuccessorNeFirst : firstSuccessor ≠ firstNatural := by
    intro heq
    apply canonicalStableRawComponentSuccessorToken_ne_natural
      ends m j k l zero hloop hjk hkl hk0 p hno component firstState.1
    exact congrArg Subtype.val heq
  by_cases hsuccessorSecond : firstSuccessor = secondNatural
  · right
    have hsuccessorToken :
        canonicalStableRawComponentSuccessorToken
            ends m j k l zero hloop hjk hkl hk0 p hno component firstState.1 =
          canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component second :=
      (congrArg Subtype.val hsuccessorSecond).trans hsecondNatural
    have hsuccessorExceptional : CanonicalStableRawLeftTokenIsExceptional
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawComponentSuccessorToken
            ends m j k l zero hloop hjk hkl hk0 p hno component
              firstState.1).1 := by
      rw [congrArg Subtype.val hsuccessorToken]
      change CanonicalStableRawLeftTokenIsExceptional
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno second.1)
      unfold canonicalStableRawStateLeftToken
      rw [dif_neg second.2.2]
      exact canonicalStableRawDirectLeftToken_isExceptional
        ends m j k l zero hloop hjk hkl hk0 p second.1 second.2.2
    unfold canonicalStableRawComponentForestStep
    rw [dif_pos hsuccessorExceptional]
    congr 1
    apply (canonicalStableRawComponentDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component).injective
    exact (canonicalStableRawComponentExceptionalSuccessorDirect_natural
      ends m j k l zero hloop hjk hkl hk0 p hno component firstState.1
        hsuccessorExceptional).trans hsuccessorToken
  · left
    exact finiteEmbedding_three_of_pairwise_ne
      firstNatural secondNatural firstSuccessor hnaturalsNe
        hsuccessorNeFirst.symm (fun heq => hsuccessorSecond heq.symm)



theorem canonicalStableRawComponent_directPair_threeTokens_or_twoCycle
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (firstState secondState : ↑sources)
    (first second : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hne : first ≠ second)
    (hfirst : firstState.1.1 = first.1)
    (hsecond : secondState.1.1 = second.1) :
    Nonempty (Fin 3 ↪
        ↑(canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨
      (canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component firstState.1 =
          Sum.inl second ∧
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component secondState.1 =
          Sum.inl first) := by
  rcases canonicalStableRawComponent_directPair_threeTokens_or_firstStep
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
        firstState secondState first second hne hfirst hsecond with
    hthree | hfirstStep
  · exact Or.inl hthree
  · rcases canonicalStableRawComponent_directPair_threeTokens_or_firstStep
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          secondState firstState second first hne.symm hsecond hfirst with
      hthree | hsecondStep
    · exact Or.inl hthree
    · exact Or.inr ⟨hfirstStep, hsecondStep⟩



theorem canonicalStableRawComponent_directPair_threeTokens_or_token_eq_natural
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (firstState secondState : ↑sources)
    (first second : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hne : first ≠ second)
    (hfirst : firstState.1.1 = first.1)
    (hsecond : secondState.1.1 = second.1)
    (token : ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)) :
    Nonempty (Fin 3 ↪
        ↑(canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨
      token = canonicalStableRawComponentTightNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component
            sources firstState ∨
      token = canonicalStableRawComponentTightNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component
            sources secondState := by
  let firstNatural := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources firstState
  let secondNatural := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources secondState
  have hfirstNatural : firstNatural.1 =
      canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component first := by
    apply Subtype.ext
    change canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno firstState.1.1 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno first.1
    rw [hfirst]
  have hsecondNatural : secondNatural.1 =
      canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component second := by
    apply Subtype.ext
    change canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno secondState.1.1 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno second.1
    rw [hsecond]
  have hnaturalsNe : firstNatural ≠ secondNatural := by
    intro heq
    apply hne
    apply (canonicalStableRawComponentDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component).injective
    exact hfirstNatural.symm.trans
      ((congrArg Subtype.val heq).trans hsecondNatural)
  by_cases hfirstToken : token = firstNatural
  · exact Or.inr (Or.inl hfirstToken)
  · by_cases hsecondToken : token = secondNatural
    · exact Or.inr (Or.inr hsecondToken)
    · exact Or.inl (finiteEmbedding_three_of_pairwise_ne
        firstNatural secondNatural token hnaturalsNe
          (fun heq => hfirstToken heq.symm) (fun heq => hsecondToken heq.symm))




theorem
    CanonicalStableRawTightChargeOrbit.HasRetainedSharedTokenOutput.local_or_directPair
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (houtput : orbit.HasRetainedSharedTokenOutput)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.LocalMergerDischarge ∨
      (orbit.HasRetainedSharedTokenOutput ∧
        ∃ source : ↑sources, ∃ q : Fin orbit.size,
          ∃ first second : CanonicalStableRawComponentDirectState
              ends m j k l zero hloop hjk hkl hk0 p hno component,
            source ≠ orbit.states q.succ ∧ first ≠ second ∧
            source.1.1 = first.1 ∧
            (orbit.states q.succ).1.1 = second.1 ∧
            ∃ token : ↑(canonicalStableRawComponentIncidentNeighborhood
                ends m j k l zero hloop hjk hkl hk0 p hno component sources),
              ∃ u : CanonicalStableRawExceptionalEdge
                  ends m j k l zero hloop hjk hkl hk0 p,
                token = canonicalStableRawComponentTightNaturalToken
                    ends m j k l zero hloop hjk hkl hk0 p hno component
                      sources source ∧
                token = orbit.tokens q ∧
                u.target = canonicalStableRawLeftTokenTarget
                    ends m j k l zero hloop hjk hkl hk0 p token.1.1 ∧
                CanonicalStableRawOwnerStableOutput
                    ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧
                u = source.1.1 ∧
                (first.1.source = second.1.source ∨
                  first.1.source =
                    ⟨canonicalStableRawPreferredRightBase
                        ends m j k l zero hloop hjk hkl hk0 p second.1.target,
                      canonicalStableRawPreferredRightBase_mem
                        ends m j k l zero hloop hjk hkl hk0 p
                          second.1.target⟩)) := by
  have houtput' := houtput
  obtain ⟨source, q, token, u, hne, _horigin, hnatural, hrepeat,
      _hsourceIncident, hpairedIncident, htarget, hkind, _hcomponent⟩ :=
    houtput
  rcases canonicalStableRawComponent_distinctTightStates_localDischarge
      ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
        source (orbit.states q.succ) hne with
    hterminal | hthree | hsecond |
      ⟨first, second, hfirstSecond, hfirst, hsecond⟩
  · exact Or.inl (Or.inl hterminal)
  · exact Or.inl (Or.inr (Or.inl hthree))
  · exact Or.inl (Or.inr (Or.inr hsecond))
  · have hsourceDirect : source.1.1.target.1 ≠
        canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
          source.1.1.source := by
      rw [hfirst]
      exact first.2.2
    obtain ⟨hstable, hu⟩ :=
      canonicalStableRawComponent_directNaturalSquareOutput_eq
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          source token hnatural u htarget hkind hsourceDirect
    have hendpoint :=
      canonicalStableRawComponent_directNaturalIncidence_endpointSplit
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          source (orbit.states q.succ) first second hfirst hsecond token
            hnatural hpairedIncident
    exact Or.inr
      ⟨houtput', source, q, first, second, hne, hfirstSecond, hfirst, hsecond,
        token, u, hnatural, hrepeat, htarget, hstable, hu, hendpoint⟩



theorem
    CanonicalStableRawTightChargeOrbit.HasFreshInternalChordOutput.local_or_directPair
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (houtput : orbit.HasFreshInternalChordOutput)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.LocalMergerDischarge ∨
      (orbit.HasFreshInternalChordOutput ∧
        ∃ q r : Fin (orbit.size + 1),
          ∃ first second : CanonicalStableRawComponentDirectState
              ends m j k l zero hloop hjk hkl hk0 p hno component,
            q ≠ r ∧ first ≠ second ∧
            (orbit.states q).1.1 = first.1 ∧
            (orbit.states r).1.1 = second.1) := by
  have houtput' := houtput
  obtain ⟨q, r, _token, _u, hqr, _hfresh, _hq, _hr,
      _htarget, _hkind, _hcomponent⟩ := houtput
  have hne : orbit.states q ≠ orbit.states r := by
    intro heq
    exact hqr (orbit.states.injective heq)
  rcases canonicalStableRawComponent_distinctTightStates_localDischarge
      ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
        (orbit.states q) (orbit.states r) hne with
    hterminal | hthree | hsecond |
      ⟨first, second, hfirstSecond, hfirst, hsecond⟩
  · exact Or.inl (Or.inl hterminal)
  · exact Or.inl (Or.inr (Or.inl hthree))
  · exact Or.inl (Or.inr (Or.inr hsecond))
  · exact Or.inr
      ⟨houtput', q, r, first, second, hqr, hfirstSecond, hfirst, hsecond⟩




theorem
    CanonicalStableRawTightChargeOrbit.HasRetainedSharedTokenOutput.local_or_firstDirectStep
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (houtput : orbit.HasRetainedSharedTokenOutput)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.LocalMergerDischarge ∨
      (orbit.HasRetainedSharedTokenOutput ∧
        ∃ source : ↑sources, ∃ q : Fin orbit.size,
          ∃ first second : CanonicalStableRawComponentDirectState
              ends m j k l zero hloop hjk hkl hk0 p hno component,
            source ≠ orbit.states q.succ ∧ first ≠ second ∧
            source.1.1 = first.1 ∧
            (orbit.states q.succ).1.1 = second.1 ∧
            canonicalStableRawComponentForestStep
                ends m j k l zero hloop hjk hkl hk0 p hno component source.1 =
              Sum.inl second) := by
  rcases houtput.local_or_directPair herase with hlocal |
      ⟨houtput', source, q, first, second, hsourceNe, hfirstSecond,
        hfirst, hsecond, _hsquare⟩
  · exact Or.inl hlocal
  · rcases canonicalStableRawComponent_directPair_threeTokens_or_firstStep
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          source (orbit.states q.succ) first second hfirstSecond hfirst hsecond with
      hthree | hstep
    · exact Or.inl (Or.inr (Or.inl hthree))
    · exact Or.inr
        ⟨houtput', source, q, first, second, hsourceNe, hfirstSecond,
          hfirst, hsecond, hstep⟩


theorem
    CanonicalStableRawTightChargeOrbit.HasFreshInternalChordOutput.local_or_firstDirectStep
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (houtput : orbit.HasFreshInternalChordOutput)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.LocalMergerDischarge ∨
      (orbit.HasFreshInternalChordOutput ∧
        ∃ q r : Fin (orbit.size + 1),
          ∃ first second : CanonicalStableRawComponentDirectState
              ends m j k l zero hloop hjk hkl hk0 p hno component,
            q ≠ r ∧ first ≠ second ∧
            (orbit.states q).1.1 = first.1 ∧
            (orbit.states r).1.1 = second.1 ∧
            canonicalStableRawComponentForestStep
                ends m j k l zero hloop hjk hkl hk0 p hno component
                  (orbit.states q).1 = Sum.inl second) := by
  rcases houtput.local_or_directPair herase with hlocal |
      ⟨houtput', q, r, first, second, hqr, hfirstSecond, hfirst, hsecond⟩
  · exact Or.inl hlocal
  · rcases canonicalStableRawComponent_directPair_threeTokens_or_firstStep
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          (orbit.states q) (orbit.states r) first second hfirstSecond
            hfirst hsecond with
      hthree | hstep
    · exact Or.inl (Or.inr (Or.inl hthree))
    · exact Or.inr
        ⟨houtput', q, r, first, second, hqr, hfirstSecond,
          hfirst, hsecond, hstep⟩



theorem
    CanonicalStableRawTightChargeOrbit.HasRetainedSharedTokenOutput.local_or_directTwoCycle
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (houtput : orbit.HasRetainedSharedTokenOutput)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.LocalMergerDischarge ∨
      (orbit.HasRetainedSharedTokenOutput ∧
        ∃ source : ↑sources, ∃ q : Fin orbit.size,
          ∃ first second : CanonicalStableRawComponentDirectState
              ends m j k l zero hloop hjk hkl hk0 p hno component,
            source ≠ orbit.states q.succ ∧ first ≠ second ∧
            source.1.1 = first.1 ∧
            (orbit.states q.succ).1.1 = second.1 ∧
            canonicalStableRawComponentForestStep
                ends m j k l zero hloop hjk hkl hk0 p hno component source.1 =
              Sum.inl second ∧
            canonicalStableRawComponentForestStep
                ends m j k l zero hloop hjk hkl hk0 p hno component
                  (orbit.states q.succ).1 = Sum.inl first) := by
  rcases houtput.local_or_directPair herase with hlocal |
      ⟨houtput', source, q, first, second, hsourceNe, hfirstSecond,
        hfirst, hsecond, _hsquare⟩
  · exact Or.inl hlocal
  · rcases canonicalStableRawComponent_directPair_threeTokens_or_twoCycle
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          source (orbit.states q.succ) first second hfirstSecond hfirst hsecond with
      hthree | ⟨hfirstStep, hsecondStep⟩
    · exact Or.inl (Or.inr (Or.inl hthree))
    · exact Or.inr
        ⟨houtput', source, q, first, second, hsourceNe, hfirstSecond,
          hfirst, hsecond, hfirstStep, hsecondStep⟩



theorem
    CanonicalStableRawTightChargeOrbit.HasFreshInternalChordOutput.local_or_directTwoCycle
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (houtput : orbit.HasFreshInternalChordOutput)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.LocalMergerDischarge ∨
      (orbit.HasFreshInternalChordOutput ∧
        ∃ q r : Fin (orbit.size + 1),
          ∃ first second : CanonicalStableRawComponentDirectState
              ends m j k l zero hloop hjk hkl hk0 p hno component,
            q ≠ r ∧ first ≠ second ∧
            (orbit.states q).1.1 = first.1 ∧
            (orbit.states r).1.1 = second.1 ∧
            canonicalStableRawComponentForestStep
                ends m j k l zero hloop hjk hkl hk0 p hno component
                  (orbit.states q).1 = Sum.inl second ∧
            canonicalStableRawComponentForestStep
                ends m j k l zero hloop hjk hkl hk0 p hno component
                  (orbit.states r).1 = Sum.inl first) := by
  rcases houtput.local_or_directPair herase with hlocal |
      ⟨houtput', q, r, first, second, hqr, hfirstSecond, hfirst, hsecond⟩
  · exact Or.inl hlocal
  · rcases canonicalStableRawComponent_directPair_threeTokens_or_twoCycle
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          (orbit.states q) (orbit.states r) first second hfirstSecond
            hfirst hsecond with
      hthree | ⟨hfirstStep, hsecondStep⟩
    · exact Or.inl (Or.inr (Or.inl hthree))
    · exact Or.inr
        ⟨houtput', q, r, first, second, hqr, hfirstSecond,
          hfirst, hsecond, hfirstStep, hsecondStep⟩




theorem
    CanonicalStableRawTightChargeOrbit.HasFreshInternalChordOutput.local_or_naturalTwoCycle
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (houtput : orbit.HasFreshInternalChordOutput)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.LocalMergerDischarge ∨
      ∃ q r : Fin (orbit.size + 1),
        ∃ token : ↑(canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources),
          ∃ u : CanonicalStableRawExceptionalEdge
              ends m j k l zero hloop hjk hkl hk0 p,
            ∃ first second : CanonicalStableRawComponentDirectState
                ends m j k l zero hloop hjk hkl hk0 p hno component,
              q ≠ r ∧ first ≠ second ∧
              (orbit.states q).1.1 = first.1 ∧
              (orbit.states r).1.1 = second.1 ∧
              (∀ s, token ≠ orbit.tokens s) ∧
              CanonicalStableRawComponentIncident
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    (orbit.states q).1 token.1 ∧
              CanonicalStableRawComponentIncident
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    (orbit.states r).1 token.1 ∧
              u.target = canonicalStableRawLeftTokenTarget
                  ends m j k l zero hloop hjk hkl hk0 p token.1.1 ∧
              (CanonicalStableRawOwnerStableOutput
                    ends m j k l zero hloop hjk hkl hk0 p
                      (orbit.states q).1.1 u ∨
                CanonicalStableRawOwnerAdvancingOutput
                    ends m j k l zero hloop hjk hkl hk0 p
                      (orbit.states q).1.1 u) ∧
              canonicalStableRawTokenComponent
                  ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
              (token = canonicalStableRawComponentTightNaturalToken
                    ends m j k l zero hloop hjk hkl hk0 p hno component
                      sources (orbit.states q) ∨
                token = canonicalStableRawComponentTightNaturalToken
                    ends m j k l zero hloop hjk hkl hk0 p hno component
                      sources (orbit.states r)) ∧
              canonicalStableRawComponentForestStep
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    (orbit.states q).1 = Sum.inl second ∧
              canonicalStableRawComponentForestStep
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    (orbit.states r).1 = Sum.inl first := by
  obtain ⟨q, r, token, u, hqr, hfresh, hq, hr,
      htarget, hkind, hcomponent⟩ := houtput
  have hstatesNe : orbit.states q ≠ orbit.states r := by
    intro heq
    exact hqr (orbit.states.injective heq)
  rcases canonicalStableRawComponent_distinctTightStates_localDischarge
      ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
        (orbit.states q) (orbit.states r) hstatesNe with
    hterminal | hthree | hsecondCharge |
      ⟨first, second, hfirstSecond, hfirst, hsecond⟩
  · exact Or.inl (Or.inl hterminal)
  · exact Or.inl (Or.inr (Or.inl hthree))
  · exact Or.inl (Or.inr (Or.inr hsecondCharge))
  · rcases canonicalStableRawComponent_directPair_threeTokens_or_token_eq_natural
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          (orbit.states q) (orbit.states r) first second hfirstSecond
            hfirst hsecond token with
      hthree | hnatural
    · exact Or.inl (Or.inr (Or.inl hthree))
    · rcases canonicalStableRawComponent_directPair_threeTokens_or_twoCycle
          ends m j k l zero hloop hjk hkl hk0 p hno component sources
            (orbit.states q) (orbit.states r) first second hfirstSecond
              hfirst hsecond with
        hthree | ⟨hfirstStep, hsecondStep⟩
      · exact Or.inl (Or.inr (Or.inl hthree))
      · exact Or.inr
          ⟨q, r, token, u, first, second, hqr, hfirstSecond,
            hfirst, hsecond, hfresh, hq, hr, htarget, hkind, hcomponent,
            hnatural, hfirstStep, hsecondStep⟩




def CanonicalStableRawTightChargeOrbit.HasDirectOrbitDischarge
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (_orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources) : Prop :=
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Token := CanonicalStableRawComponentToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let advance := canonicalStableRawComponentDirectForestAdvance
    ends m j k l zero hloop hjk hkl hk0 p hno component
  ∃ entry : ↑sources, ∃ start : Direct,
    canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component entry.1 =
      Sum.inl start ∧
    ((∃ n ≤ Nat.card Direct,
        ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          canonicalStableRawComponentForestStep
              ends m j k l zero hloop hjk hkl hk0 p hno component
                ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ =
            Sum.inr terminal) ∨
      ∃ size : Nat, 0 < size ∧
        Nonempty (Fin size ↪ Direct) ∧ Nonempty (Fin size ↪ Token))





def CanonicalStableRawTightChargeOrbit.HasBalancedResidualDeficit
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (_orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources) : Prop :=
  let Self := CanonicalStableRawComponentSelfState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Token := CanonicalStableRawComponentToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  ∃ size : Nat, 0 < size ∧ Nonempty (Fin size ↪ Direct) ∧
    Nonempty (Fin size ↪ Token) ∧
    Nat.card Token - size < Nat.card Self + (Nat.card Direct - size)




structure CanonicalStableRawComponentBalancedDirectBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) where
  size : Nat
  positive : 0 < size
  directs : Fin size ↪ CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  witnessTokens : Fin size ↪ CanonicalStableRawComponentToken
    ends m j k l zero hloop hjk hkl hk0 p hno component

def CanonicalStableRawComponentBalancedDirectBlock.sourceBlock
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Fin block.size ↪ CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
  block.directs.trans
    (canonicalStableRawComponentDirectStateEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component)

noncomputable def CanonicalStableRawComponentBalancedDirectBlock.tokenBlock
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Fin block.size ↪ CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
  block.directs.trans
    (canonicalStableRawComponentDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component)



theorem
    CanonicalStableRawComponentBalancedDirectBlock.sourceBlock_tokenBlock_incident
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (index : Fin block.size) :
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (block.sourceBlock index) (block.tokenBlock index) := by
  apply (canonicalStableRawWitnessedStateTokenIncidence_iff
    ends m j k l zero hloop hjk hkl hk0 p
      (block.tokenBlock index).1 (block.sourceBlock index).1).2
  change CanonicalStableRawStateTokenIncidence
    ends m j k l zero hloop hjk hkl hk0 p
      (canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno
          (block.directs index).1) (block.directs index).1
  exact canonicalStableRawStateLeftToken_stateTokenIncidence
    ends m j k l zero hloop hjk hkl hk0 p hno (block.directs index).1




theorem
    CanonicalStableRawComponentBalancedDirectBlock.successorToken_fresh_or_retainedOther
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (index : Fin block.size) :
    let successor := canonicalStableRawComponentSuccessorToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (block.sourceBlock index)
    successor ∉ finiteEmbeddingBlock block.size block.tokenBlock ∨
      ∃ next, next ≠ index ∧ successor = block.tokenBlock next := by
  dsimp only
  let successor := canonicalStableRawComponentSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
      (block.sourceBlock index)
  by_cases hmem : successor ∈
      finiteEmbeddingBlock block.size block.tokenBlock
  · right
    obtain ⟨next, _hnext, hnext⟩ := Finset.mem_map.mp hmem
    refine ⟨next, ?_, hnext.symm⟩
    intro hnextIndex
    subst next
    apply canonicalStableRawComponentSuccessorToken_ne_natural
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (block.sourceBlock index)
    change successor = block.tokenBlock index
    exact hnext.symm
  · exact Or.inl hmem



def CanonicalStableRawComponentBalancedDirectBlock.IsClosed
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) : Prop :=
  FiniteRelationTokenClosed
    (CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    block.size block.sourceBlock block.tokenBlock


abbrev CanonicalStableRawComponentBalancedDirectBlock.StateComplement
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :=
  FiniteEmbeddingComplement block.size block.sourceBlock



abbrev CanonicalStableRawComponentBalancedDirectBlock.TokenComplement
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :=
  FiniteEmbeddingComplement block.size block.tokenBlock



def CanonicalStableRawComponentBalancedDirectBlock.complementIncident
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    block.StateComplement -> block.TokenComplement -> Prop :=
  finiteRelationComplement
    (CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    block.size block.sourceBlock block.tokenBlock


noncomputable def
    CanonicalStableRawComponentBalancedDirectBlock.complementNeighborhood
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (sources : Finset block.StateComplement) :
    Finset block.TokenComplement := by
  classical
  exact Finset.univ.filter fun token => ∃ source ∈ sources,
    block.complementIncident source token

theorem CanonicalStableRawComponentBalancedDirectBlock.complementNeighborhood_mono
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Monotone block.complementNeighborhood := by
  classical
  intro smaller larger hsubset token htoken
  obtain ⟨source, hsource, hincident⟩ :=
    (Finset.mem_filter.mp htoken).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ token,
    source, hsubset hsource, hincident⟩





theorem
    CanonicalStableRawTightChargeOrbit.HasDirectOrbitDischarge.richStrictBlock_or_balancedBlock
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (hdischarge : orbit.HasDirectOrbitDischarge) :
    Nonempty (CanonicalStableRawComponentRichStrictBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      ∃ size : Nat, 0 < size ∧
        Nonempty (Fin size ↪ CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
        Nonempty (Fin size ↪ CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  dsimp only [CanonicalStableRawTightChargeOrbit.HasDirectOrbitDischarge]
    at hdischarge
  obtain ⟨_entry, start, _hentry, hterminal | hbalanced⟩ := hdischarge
  · left
    obtain ⟨_n, _hn, terminal, _hterminal⟩ := hterminal
    exact exists_canonicalStableRawComponentDirect_richStrictBlock_of_available
      ends m j k l zero hloop hjk hkl hk0 p hno component start terminal
  · exact Or.inr hbalanced





theorem
    CanonicalStableRawTightChargeOrbit.HasDirectOrbitDischarge.richStrict_or_balancedResidual
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hdischarge : orbit.HasDirectOrbitDischarge) :
    Nonempty (CanonicalStableRawComponentRichStrictBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      orbit.HasBalancedResidualDeficit := by
  rcases hdischarge.richStrictBlock_or_balancedBlock with hrich |
      ⟨size, hsize, hdirect, htoken⟩
  · exact Or.inl hrich
  · right
    dsimp only [CanonicalStableRawTightChargeOrbit.HasBalancedResidualDeficit]
    refine ⟨size, hsize, hdirect, htoken, ?_⟩
    have hstate := Nat.card_congr
      (canonicalStableRawComponentStateEquivSelfSumDirect
        ends m j k l zero hloop hjk hkl hk0 p hno component)
    simp only [Nat.card_sum] at hstate
    apply strictDeficit_sub_balancedEmbeddings size
      (directBlock := hdirect) (tokenBlock := htoken)
    rw [← hstate]
    simpa only [Nat.card_eq_fintype_card] using hdeficit




theorem
    CanonicalStableRawTightChargeOrbit.HasBalancedResidualDeficit.exists_block
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (hresidual : orbit.HasBalancedResidualDeficit) :
    ∃ block : CanonicalStableRawComponentBalancedDirectBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      Nat.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) - block.size <
        Nat.card (CanonicalStableRawComponentSelfState
            ends m j k l zero hloop hjk hkl hk0 p hno component) +
          (Nat.card (CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component) -
              block.size) := by
  dsimp only [CanonicalStableRawTightChargeOrbit.HasBalancedResidualDeficit]
    at hresidual
  obtain ⟨size, hsize, ⟨directs⟩, ⟨tokens⟩, hstrict⟩ := hresidual
  exact ⟨⟨size, hsize, directs, tokens⟩, hstrict⟩



theorem CanonicalStableRawComponentBalancedDirectBlock.closed_or_crossing
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    block.IsClosed ∨
      ∃ source token,
        CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component source token ∧
          (∀ i, source ≠ block.sourceBlock i) ∧
          ∃ i, token = block.tokenBlock i := by
  exact finiteRelationTokenClosed_or_crossing
    (CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    block.size block.sourceBlock block.tokenBlock



theorem
    CanonicalStableRawComponentBalancedDirectBlock.complement_strictDeficit
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    Fintype.card block.TokenComplement <
      Fintype.card block.StateComplement := by
  exact finiteEmbeddingComplement_strictDeficit
    block.size block.sourceBlock block.tokenBlock hdeficit




theorem
    CanonicalStableRawComponentBalancedDirectBlock.stateComplement_card_lt
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Fintype.card block.StateComplement <
      Fintype.card (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  rw [finiteEmbeddingComplement_card]
  have hsize : block.size ≤ Fintype.card
      (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective block.sourceBlock block.sourceBlock.injective
  have hpositive := block.positive
  omega




def CanonicalStableRawComponentBalancedDirectBlock.HasComponentFiberRealization
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) : Prop :=
  ∃ component' : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p),
    ∀ state : CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno state.1 = component' ↔
        state ∉ finiteEmbeddingBlock block.size block.sourceBlock







theorem
    CanonicalStableRawComponentBalancedDirectBlock.no_componentFiberRealization_of_deficit
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ¬ block.HasComponentFiberRealization := by
  intro hrealization
  obtain ⟨component', hcomponent'⟩ := hrealization
  have hcomplementPos : 0 < Fintype.card block.StateComplement := by
    have hstrict := block.complement_strictDeficit hdeficit
    omega
  let remaining : block.StateComplement :=
    Classical.choice (Fintype.card_pos_iff.mp hcomplementPos)
  have hremainingComponent : canonicalStableRawTokenComponent
      ends m j k l zero hloop hjk hkl hk0 p hno remaining.1.1 = component' :=
    (hcomponent' remaining.1).2 remaining.2
  have hcomponentEq : component' = component :=
    hremainingComponent.symm.trans remaining.1.2
  let index : Fin block.size := ⟨0, block.positive⟩
  let removed := block.sourceBlock index
  have hremovedMem : removed ∈
      finiteEmbeddingBlock block.size block.sourceBlock := by
    apply Finset.mem_map.mpr
    exact ⟨index, Finset.mem_univ _, rfl⟩
  have hremovedComponent : canonicalStableRawTokenComponent
      ends m j k l zero hloop hjk hkl hk0 p hno removed.1 = component' := by
    rw [hcomponentEq]
    exact removed.2
  exact ((hcomponent' removed).1 hremovedComponent) hremovedMem




theorem
    CanonicalStableRawComponentBalancedDirectBlock.IsClosed.restricts_incidence
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    (hclosed : block.IsClosed) (source : block.StateComplement)
    (token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hincident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component source.1 token) :
    token ∉ finiteEmbeddingBlock block.size block.tokenBlock := by
  exact finiteRelationComplement_tokenClosed
    (CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    block.size block.sourceBlock block.tokenBlock hclosed source token hincident



theorem
    CanonicalStableRawComponentBalancedDirectBlock.exists_minimalComplementTightFamily
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ family : Finset block.StateComplement,
      family.Nonempty ∧
      (block.complementNeighborhood family).card + 1 = family.card ∧
      (∀ source ∈ family,
        block.complementNeighborhood (family.erase source) =
          block.complementNeighborhood family) ∧
      ∀ smaller : Finset block.StateComplement, smaller ⊂ family ->
        smaller.card ≤ (block.complementNeighborhood smaller).card := by
  apply exists_minimal_deficiency_one_family
    block.complementNeighborhood block.complementNeighborhood_mono
  refine ⟨Finset.univ, ?_⟩
  have hle := Finset.card_le_univ
    (block.complementNeighborhood (Finset.univ :
      Finset block.StateComplement))
  calc
    (block.complementNeighborhood
        (Finset.univ : Finset block.StateComplement)).card ≤
        Fintype.card block.TokenComplement := by
      simpa only [Finset.card_univ] using hle
    _ < Fintype.card block.StateComplement :=
      block.complement_strictDeficit hdeficit
    _ = (Finset.univ : Finset block.StateComplement).card := by simp






theorem
    CanonicalStableRawComponentBalancedDirectBlock.exists_smallerComplementMinimalTightProblem
    {I : Type uI} {W : Type uW} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W]
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hclosed : block.IsClosed)
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ problem : FiniteRelationMinimalTightProblem.{uI, uI},
      problem.rank < Fintype.card (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
      ∀ source : block.StateComplement,
        ∀ token : CanonicalStableRawComponentToken
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          CanonicalStableRawComponentIncident
              ends m j k l zero hloop hjk hkl hk0 p hno component
                source.1 token ->
            token ∉ finiteEmbeddingBlock block.size block.tokenBlock := by
  obtain ⟨family, hnonempty, htight, herase, hproper⟩ :=
    block.exists_minimalComplementTightFamily hdeficit
  let problem : FiniteRelationMinimalTightProblem :=
    { State := block.StateComplement
      Token := block.TokenComplement
      incident := block.complementIncident
      carrier := family
      nonempty := hnonempty
      deficiency_one := by
        simpa only [finiteBipartiteRelationNeighborhood,
          CanonicalStableRawComponentBalancedDirectBlock.complementNeighborhood]
          using htight
      erase_invariant := by
        intro source hsource
        simpa only [finiteBipartiteRelationNeighborhood,
          CanonicalStableRawComponentBalancedDirectBlock.complementNeighborhood]
          using herase source hsource
      proper_hall := by
        intro smaller hsmaller
        simpa only [finiteBipartiteRelationNeighborhood,
          CanonicalStableRawComponentBalancedDirectBlock.complementNeighborhood]
          using hproper smaller hsmaller }
  refine ⟨problem, ?_, fun source token hincident =>
    hclosed.restricts_incidence source token hincident⟩
  rw [problem.rank_eq_carrier_card]
  exact (Finset.card_le_univ family).trans_lt block.stateComplement_card_lt




def CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) : Prop :=
  ∃ source token, ∃ index : Fin block.size,
    CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component source token ∧
      (∀ i, source ≠ block.sourceBlock i) ∧
      token = block.tokenBlock index ∧
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p token.1 ∧
        (CanonicalStableRawOwnerStableOutput
              ends m j k l zero hloop hjk hkl hk0 p source.1 u ∨
          CanonicalStableRawOwnerAdvancingOutput
              ends m j k l zero hloop hjk hkl hk0 p source.1 u) ∧
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno u = component




theorem
    CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.exists_crossingContinuation
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    (hcross : block.HasGeometricCrossing) :
    ∃ continuation : FiniteRelationCrossingContinuation
        (CanonicalStableRawComponentIncident
          ends m j k l zero hloop hjk hkl hk0 p hno component),
      continuation.size = block.size ∧
      let move := StatMech.FrontierA.RelationPartialMatching.HoleState.move
        continuation.natural continuation.natural_incident
      ∃ start stop : Nat, start < stop ∧ stop ≤ block.size + 1 ∧
        (move^[start] continuation.initialHoleState).hole =
          (move^[stop] continuation.initialHoleState).hole ∧
        ∀ a b : Nat, a < b -> b < stop ->
          (move^[a] continuation.initialHoleState).hole ≠
            (move^[b] continuation.initialHoleState).hole := by
  obtain ⟨source, token, index, hincident, hsource, htoken,
      _u, _htarget, _hkind, _hcomponent⟩ := hcross
  let continuation : FiniteRelationCrossingContinuation
      (CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component) :=
    { size := block.size
      sources := block.sourceBlock
      tokens := block.tokenBlock
      extra := source
      index := index
      extra_fresh := hsource
      aligned := block.sourceBlock_tokenBlock_incident
      crossing := by
        rw [← htoken]
        exact hincident }
  refine ⟨continuation, rfl, ?_⟩
  simpa only [continuation] using continuation.exists_minimal_hole_repeat



def CanonicalStableRawComponentBalancedDirectBlock.HasOldOutputCrossing
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) : Prop :=
  ∃ source token, ∃ index oldIndex : Fin block.size,
    CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component source token ∧
      (∀ i, source ≠ block.sourceBlock i) ∧
      token = block.tokenBlock index ∧
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u = (block.directs oldIndex).1 ∧
        u.target = canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p token.1 ∧
        (CanonicalStableRawOwnerStableOutput
              ends m j k l zero hloop hjk hkl hk0 p source.1 u ∨
          CanonicalStableRawOwnerAdvancingOutput
              ends m j k l zero hloop hjk hkl hk0 p source.1 u)




def CanonicalStableRawComponentBalancedDirectBlock.HasNaturalTokenEscape
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) : Prop :=
  ∃ source, ∃ index : Fin block.size,
    (∀ i, source ≠ block.sourceBlock i) ∧
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        source (block.tokenBlock index) ∧
    let natural := canonicalStableRawComponentNaturalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component source
    natural ∉ finiteEmbeddingBlock block.size block.tokenBlock ∨
      ∃ q, q ≠ index ∧ natural = block.tokenBlock q


def CanonicalStableRawComponentBalancedDirectBlock.HasAugmentedIncidentBlock
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) : Prop :=
  ∃ sources : Fin (block.size + 1) ↪
      CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component,
    ∃ tokens : Fin (block.size + 1) ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      ∀ i, CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component
          (sources i) (tokens i)





theorem
    CanonicalStableRawComponentBalancedDirectBlock.HasNaturalTokenEscape.augmentedBlock_or_alternate
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    (hescape : block.HasNaturalTokenEscape) :
    block.HasAugmentedIncidentBlock ∨
      ∃ source, ∃ index q : Fin block.size,
        (∀ i, source ≠ block.sourceBlock i) ∧
        CanonicalStableRawComponentIncident
          ends m j k l zero hloop hjk hkl hk0 p hno component
            source (block.tokenBlock index) ∧
        q ≠ index ∧
        canonicalStableRawComponentNaturalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component source =
          block.tokenBlock q := by
  obtain ⟨source, index, hsource, hcrossing, hnatural⟩ := hescape
  rcases hnatural with hfresh | ⟨q, hq, hnatural⟩
  · left
    let natural := canonicalStableRawComponentNaturalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component source
    have htokenFresh : ∀ i, natural ≠ block.tokenBlock i := by
      intro i hi
      apply hfresh
      apply Finset.mem_map.mpr
      exact ⟨i, Finset.mem_univ _, hi.symm⟩
    obtain ⟨extendedSources, hsourcePrefix, hsourceLast⟩ :=
      finiteEmbedding_snoc block.size block.sourceBlock source hsource
    obtain ⟨extendedTokens, htokenPrefix, htokenLast⟩ :=
      finiteEmbedding_snoc block.size block.tokenBlock natural htokenFresh
    refine ⟨extendedSources, extendedTokens, ?_⟩
    intro i
    refine Fin.lastCases ?_ (fun q => ?_) i
    · rw [hsourceLast, htokenLast]
      exact canonicalStableRawComponentNaturalToken_incident
        ends m j k l zero hloop hjk hkl hk0 p hno component source
    · rw [hsourcePrefix, htokenPrefix]
      exact block.sourceBlock_tokenBlock_incident q
  · right
    exact ⟨source, index, q, hsource, hcrossing, hq, hnatural⟩





theorem
    CanonicalStableRawComponentBalancedDirectBlock.HasNaturalTokenEscape.augmentedBlock_or_nonreversingContinuation
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    (hescape : block.HasNaturalTokenEscape) :
    block.HasAugmentedIncidentBlock ∨
      ∃ continuation : FiniteRelationCrossingContinuation
          (CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        continuation.size = block.size ∧
        ∃ alternate : continuation.Token,
          alternate ≠ continuation.index ∧
          continuation.incident (Sum.inr ()) alternate ∧
          let moved := continuation.initialHoleState.move
            continuation.natural continuation.natural_incident
          ∃ hincident' : continuation.incident moved.hole alternate,
            (moved.moveAcross alternate hincident').hole =
              Sum.inl alternate := by
  rcases hescape.augmentedBlock_or_alternate with haugmented |
      ⟨source, index, q, hsource, hcrossing, hq, hnatural⟩
  · exact Or.inl haugmented
  · right
    let continuation : FiniteRelationCrossingContinuation
        (CanonicalStableRawComponentIncident
          ends m j k l zero hloop hjk hkl hk0 p hno component) :=
      { size := block.size
        sources := block.sourceBlock
        tokens := block.tokenBlock
        extra := source
        index := index
        extra_fresh := hsource
        aligned := block.sourceBlock_tokenBlock_incident
        crossing := hcrossing }
    have halternate : continuation.incident (Sum.inr ()) q := by
      change CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component
          source (block.tokenBlock q)
      rw [← hnatural]
      exact canonicalStableRawComponentNaturalToken_incident
        ends m j k l zero hloop hjk hkl hk0 p hno component source
    refine ⟨continuation, rfl, q, hq, halternate, ?_⟩
    exact continuation.moveThenAlternate_hole q hq halternate




def CanonicalStableRawComponentBalancedDirectBlock.HasStableSelfOldOutput
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) : Prop :=
  ∃ source, ∃ index oldIndex : Fin block.size,
    (∀ i, source ≠ block.sourceBlock i) ∧
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        source (block.tokenBlock index) ∧
    canonicalStableRawComponentNaturalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component source =
      block.tokenBlock index ∧
    source.1.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p source.1.source ∧
    ∃ u : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p,
      u = (block.directs oldIndex).1 ∧
      u.target = canonicalStableRawLeftTokenTarget
        ends m j k l zero hloop hjk hkl hk0 p
          (block.tokenBlock index).1 ∧
      CanonicalStableRawOwnerStableOutput
        ends m j k l zero hloop hjk hkl hk0 p source.1 u



def
    CanonicalStableRawComponentBalancedDirectBlock.HasAdvancingOldOutputRankDrop
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) : Prop :=
  ∃ source, ∃ index oldIndex : Fin block.size,
    (∀ i, source ≠ block.sourceBlock i) ∧
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        source (block.tokenBlock index) ∧
    canonicalStableRawComponentNaturalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component source =
      block.tokenBlock index ∧
    ∃ u : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p,
      u = (block.directs oldIndex).1 ∧
      u.target = canonicalStableRawLeftTokenTarget
        ends m j k l zero hloop hjk hkl hk0 p
          (block.tokenBlock index).1 ∧
      CanonicalStableRawOwnerAdvancingOutput
        ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧
      canonicalStableRawSourceRank ends m j k l zero p u.source <
        canonicalStableRawSourceRank ends m j k l zero p source.1.source







theorem
    CanonicalStableRawComponentBalancedDirectBlock.HasOldOutputCrossing.naturalEscape_or_stableSelf_or_advancingRankDrop
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    (hcross : block.HasOldOutputCrossing) :
    block.HasNaturalTokenEscape ∨
      block.HasStableSelfOldOutput ∨
      block.HasAdvancingOldOutputRankDrop := by
  obtain ⟨source, token, index, oldIndex, hincident, hsource, htoken,
      u, hu, htarget, hkind⟩ := hcross
  let natural := canonicalStableRawComponentNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component source
  by_cases hnaturalMem : natural ∈
      finiteEmbeddingBlock block.size block.tokenBlock
  · obtain ⟨q, _hq, hq⟩ := Finset.mem_map.mp hnaturalMem
    by_cases hqIndex : q = index
    · subst q
      have hnatural : natural = block.tokenBlock index := hq.symm
      have htargetNatural : u.target = canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p natural.1 := by
        rw [hnatural]
        simpa only [htoken] using htarget
      have hself : source.1.target.1 = canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p source.1.source := by
        by_contra hdirect
        rcases hkind with hstable | hadvancing
        · have huSource :=
            canonicalStableRawOwnerStableOutput_eq_of_directNaturalTarget
              source hdirect u htargetNatural hstable
          apply hsource oldIndex
          apply Subtype.ext
          change source.1 = (block.directs oldIndex).1
          exact huSource.symm.trans hu
        · exact
            canonicalStableRawOwnerAdvancingOutput_false_of_directNaturalTarget
              source hdirect u htargetNatural hadvancing
      rcases hkind with hstable | hadvancing
      · right
        left
        exact ⟨source, index, oldIndex, hsource,
          by simpa only [htoken] using hincident, hnatural, hself,
          u, hu, by simpa only [htoken] using htarget, hstable⟩
      · right
        right
        let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
          ⟨canonicalStableRawPreferredRightBase
              ends m j k l zero hloop hjk hkl hk0 p source.1.target,
            canonicalStableRawPreferredRightBase_mem
              ends m j k l zero hloop hjk hkl hk0 p source.1.target⟩
        have hownerRank : canonicalStableRawSourceRank
              ends m j k l zero p owner <
            canonicalStableRawSourceRank ends m j k l zero p
              source.1.source :=
          canonicalStableRawPreferredRightBase_rank_lt_of_self
            ends m j k l zero hloop hjk hkl hk0 p source.1.target
              source.1.source hself.symm source.1.exceptional
        have huSource : u.source = owner := by
          apply Subtype.ext
          exact hadvancing
        exact ⟨source, index, oldIndex, hsource,
          by simpa only [htoken] using hincident, hnatural, u, hu,
          by simpa only [htoken] using htarget, hadvancing,
          huSource ▸ hownerRank⟩
    · left
      exact ⟨source, index, hsource,
        by simpa only [htoken] using hincident,
        Or.inr ⟨q, hqIndex, hq.symm⟩⟩
  · left
    exact ⟨source, index, hsource,
      by simpa only [htoken] using hincident, Or.inl hnaturalMem⟩






theorem
    CanonicalStableRawComponentBalancedDirectBlock.HasStableSelfOldOutput.terminal_or_rankDrop
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    (hstable : block.HasStableSelfOldOutput) :
    Nonempty (CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      ∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
          canonicalStableRawSourceRank ends m j k l zero p u.source <
            canonicalStableRawSourceRank ends m j k l zero p
              source.1.source := by
  obtain ⟨source, index, _oldIndex, _hsource, _hcrossing, hnatural,
      hself, _u, _hu, _htarget, _houtputStable⟩ := hstable
  let self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨source.1, source.2, hself⟩
  have hraw := congrArg Subtype.val hnatural
  change canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno source.1 =
    canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno
        (block.directs index).1 at hraw
  unfold canonicalStableRawStateLeftToken at hraw
  rw [dif_pos hself, dif_neg (block.directs index).2.2] at hraw
  rcases canonicalStableRawSelfReroute_eq_directToken_dichotomy
      ends m j k l zero hloop hjk hkl hk0 p hno
        source.1 (block.directs index).1 hself
          (block.directs index).2.2 hraw with
    ⟨_hdirectNext, hownerStable⟩ |
      ⟨hownerAdvancing, _hsourceEq, _htargetEq, _hne⟩
  · left
    let successor := canonicalStableRawComponentSuccessorToken
      ends m j k l zero hloop hjk hkl hk0 p hno component source
    have hnonexceptional : ¬ CanonicalStableRawLeftTokenIsExceptional
        ends m j k l zero hloop hjk hkl hk0 p successor.1 := by
      exact canonicalStableRawComponentSuccessorToken_not_exceptional_of_ownerStable
        ends m j k l zero hloop hjk hkl hk0 p hno component
          self hownerStable
    exact ⟨⟨successor, hnonexceptional⟩⟩
  · right
    let hexceptional :=
      canonicalStableRawComponentSuccessorToken_exceptional_of_advancing
        ends m j k l zero hloop hjk hkl hk0 p hno component
          self hownerAdvancing
    let direct := canonicalStableRawComponentExceptionalSuccessorDirect
      ends m j k l zero hloop hjk hkl hk0 p hno component
        source hexceptional
    refine ⟨source, direct.1, direct.2.1, ?_⟩
    exact
      canonicalStableRawComponentExceptionalSuccessorDirect_rank_lt_of_advancing
        ends m j k l zero hloop hjk hkl hk0 p hno component
          self hownerAdvancing




noncomputable def
    CanonicalStableRawComponentBalancedDirectBlock.crossingFamily
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : ∀ i, source ≠ block.sourceBlock i) :
    FiniteRelationDeficiencyOneFamily
      (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) where
  states := insert source (finiteEmbeddingBlock block.size block.sourceBlock)
  tokens := finiteEmbeddingBlock block.size block.tokenBlock
  deficiency_one := by
    have hsourceNotMem : source ∉
        finiteEmbeddingBlock block.size block.sourceBlock := by
      intro hmem
      obtain ⟨i, _hi, heq⟩ := Finset.mem_map.mp hmem
      exact hsource i heq.symm
    rw [Finset.card_insert_of_notMem hsourceNotMem]
    simp only [finiteEmbeddingBlock, Finset.card_map, Finset.card_univ,
      Fintype.card_fin]

theorem
    CanonicalStableRawComponentBalancedDirectBlock.geometricCrossing_of_crossing
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hincident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component source token)
    (hsource : ∀ i, source ≠ block.sourceBlock i)
    (index : Fin block.size) (htoken : token = block.tokenBlock index) :
    block.HasGeometricCrossing := by
  have hsourceIncident : CanonicalStableRawWitnessedStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token.1 source.1 := hincident
  have hdirectIncident : CanonicalStableRawWitnessedStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token.1
        (block.directs index).1 := by
    apply (canonicalStableRawWitnessedStateTokenIncidence_iff
      ends m j k l zero hloop hjk hkl hk0 p token.1
        (block.directs index).1).2
    rw [htoken]
    exact canonicalStableRawStateLeftToken_stateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p hno (block.directs index).1
  rcases canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
      ends m j k l zero hloop hjk hkl hk0 p hno token.1
        source.1 (block.directs index).1 hsourceIncident hdirectIncident with
    heq | ⟨u, htarget, hkind, hcomponent, _⟩ |
      ⟨u, htarget, hkind, hcomponent, _⟩
  · exact False.elim (hsource index (by
      apply Subtype.ext
      exact heq))
  · exact ⟨source, token, index, hincident, hsource, htoken,
      u, htarget, Or.inl hkind, hcomponent.trans source.2⟩
  · exact ⟨source, token, index, hincident, hsource, htoken,
      u, htarget, Or.inr hkind, hcomponent.trans source.2⟩



theorem
    CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.exists_crossingFamily
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    (hcross : block.HasGeometricCrossing) :
    ∃ source token,
      ∃ hsource : ∀ i, source ≠ block.sourceBlock i,
        let family := block.crossingFamily source hsource
        source ∈ family.states ∧ token ∈ family.tokens ∧
          CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component source token ∧
          ∃ u : CanonicalStableRawExceptionalEdge
              ends m j k l zero hloop hjk hkl hk0 p,
            u.target = canonicalStableRawLeftTokenTarget
              ends m j k l zero hloop hjk hkl hk0 p token.1 ∧
            (CanonicalStableRawOwnerStableOutput
                  ends m j k l zero hloop hjk hkl hk0 p source.1 u ∨
              CanonicalStableRawOwnerAdvancingOutput
                  ends m j k l zero hloop hjk hkl hk0 p source.1 u) ∧
            canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  obtain ⟨source, token, index, hincident, hsource, htoken,
      u, htarget, hkind, hcomponent⟩ := hcross
  refine ⟨source, token, hsource, ?_, ?_, hincident,
    u, htarget, hkind, hcomponent⟩
  · exact Finset.mem_insert_self _ _
  · apply Finset.mem_map.mpr
    exact ⟨index, Finset.mem_univ _, htoken.symm⟩






theorem
    CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.exists_reroutedSourceBlock
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    (hcross : block.HasGeometricCrossing) :
    ∃ source token, ∃ index : Fin block.size,
      ∃ hsource : ∀ i, source ≠ block.sourceBlock i,
        let rerouted := finiteEmbedding_replaceAt
          block.sourceBlock source hsource index
        token = block.tokenBlock index ∧
        rerouted index = source ∧
        (∀ q, q ≠ index -> rerouted q = block.sourceBlock q) ∧
        (∀ q, CanonicalStableRawComponentIncident
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (rerouted q) (block.tokenBlock q)) ∧
        block.sourceBlock index ∉ finiteEmbeddingBlock block.size rerouted := by
  obtain ⟨source, token, index, hincident, hsource, htoken,
      _u, _htarget, _hkind, _hcomponent⟩ := hcross
  refine ⟨source, token, index, hsource, htoken, ?_, ?_, ?_, ?_⟩
  · exact finiteEmbedding_replaceAt_same
      block.sourceBlock source hsource index
  · intro q hq
    exact finiteEmbedding_replaceAt_ne
      block.sourceBlock source hsource index q hq
  · intro q
    by_cases hq : q = index
    · subst q
      rw [finiteEmbedding_replaceAt_same, ← htoken]
      exact hincident
    · rw [finiteEmbedding_replaceAt_ne
        block.sourceBlock source hsource index q hq]
      apply (canonicalStableRawWitnessedStateTokenIncidence_iff
        ends m j k l zero hloop hjk hkl hk0 p
          (block.tokenBlock q).1 (block.sourceBlock q).1).2
      change CanonicalStableRawStateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno
              (block.directs q).1) (block.directs q).1
      exact canonicalStableRawStateLeftToken_stateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p hno (block.directs q).1
  · intro hmem
    obtain ⟨q, _hq, heq⟩ := Finset.mem_map.mp hmem
    exact finiteEmbedding_replaceAt_displaced_fresh
      block.sourceBlock source hsource index q heq.symm





theorem
    CanonicalStableRawComponentBalancedDirectBlock.HasOldOutputCrossing.output_displaced_or_retained
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    (hcross : block.HasOldOutputCrossing) :
    ∃ source token, ∃ index oldIndex : Fin block.size,
      ∃ hsource : ∀ i, source ≠ block.sourceBlock i,
        let rerouted := finiteEmbedding_replaceAt
          block.sourceBlock source hsource index
        CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component source token ∧
          token = block.tokenBlock index ∧
          block.sourceBlock index ∉
            finiteEmbeddingBlock block.size rerouted ∧
          (oldIndex = index ∨
            block.sourceBlock oldIndex ∈
              finiteEmbeddingBlock block.size rerouted) ∧
          ∃ u : CanonicalStableRawExceptionalEdge
              ends m j k l zero hloop hjk hkl hk0 p,
            u = (block.directs oldIndex).1 ∧
            u.target = canonicalStableRawLeftTokenTarget
              ends m j k l zero hloop hjk hkl hk0 p token.1 ∧
            (CanonicalStableRawOwnerStableOutput
                  ends m j k l zero hloop hjk hkl hk0 p source.1 u ∨
              CanonicalStableRawOwnerAdvancingOutput
                  ends m j k l zero hloop hjk hkl hk0 p source.1 u) := by
  obtain ⟨source, token, index, oldIndex, hincident, hsource, htoken,
      u, hu, htarget, hkind⟩ := hcross
  refine ⟨source, token, index, oldIndex, hsource,
    hincident, htoken, ?_, ?_, u, hu, htarget, hkind⟩
  · intro hmem
    obtain ⟨q, _hq, heq⟩ := Finset.mem_map.mp hmem
    exact finiteEmbedding_replaceAt_displaced_fresh
      block.sourceBlock source hsource index q heq.symm
  · by_cases hold : oldIndex = index
    · exact Or.inl hold
    · right
      apply Finset.mem_map.mpr
      refine ⟨oldIndex, Finset.mem_univ _, ?_⟩
      exact finiteEmbedding_replaceAt_ne
        block.sourceBlock source hsource index oldIndex hold




theorem
    CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.growth_or_self_or_oldOutput
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    (hcross : block.HasGeometricCrossing) :
    (∃ extended : CanonicalStableRawComponentBalancedDirectBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        extended.size = block.size + 1) ∨
      Nonempty (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      block.HasOldOutputCrossing := by
  obtain ⟨source, token, index, hincident, hsource, htoken,
      u, htarget, hkind, hcomponent⟩ := hcross
  by_cases huDirect : u.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p u.source
  · let direct : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨u, hcomponent, huDirect⟩
    by_cases hfresh : ∀ i, direct ≠ block.directs i
    · left
      obtain ⟨directs, _hprefix, _hlast⟩ :=
        finiteEmbedding_snoc block.size block.directs direct hfresh
      let tokens : Fin (block.size + 1) ↪
          CanonicalStableRawComponentToken
            ends m j k l zero hloop hjk hkl hk0 p hno component :=
        directs.trans (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
      exact ⟨⟨block.size + 1, by omega, directs, tokens⟩, rfl⟩
    · right
      right
      push Not at hfresh
      obtain ⟨oldIndex, hold⟩ := hfresh
      exact ⟨source, token, index, oldIndex, hincident, hsource, htoken,
        u, by simpa only [direct] using congrArg Subtype.val hold,
        htarget, hkind⟩
  · right
    left
    have huSelf : u.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p u.source :=
      Classical.not_not.mp huDirect
    exact ⟨⟨u, hcomponent, huSelf⟩⟩




theorem
    CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.growth_or_self_or_naturalEscape_or_stableSelf_or_rankDrop
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    (hcross : block.HasGeometricCrossing) :
    (∃ extended : CanonicalStableRawComponentBalancedDirectBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        extended.size = block.size + 1) ∨
      Nonempty (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      block.HasNaturalTokenEscape ∨
      block.HasStableSelfOldOutput ∨
      block.HasAdvancingOldOutputRankDrop := by
  rcases hcross.growth_or_self_or_oldOutput with hgrowth | hself | hold
  · exact Or.inl hgrowth
  · exact Or.inr (Or.inl hself)
  · rcases hold.naturalEscape_or_stableSelf_or_advancingRankDrop with
      hescape | hstable | hrank
    · exact Or.inr (Or.inr (Or.inl hescape))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hstable)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hrank)))





theorem
    CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.growth_or_self_or_naturalEscape_or_terminal_or_rankDrop
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    (hcross : block.HasGeometricCrossing) :
    (∃ extended : CanonicalStableRawComponentBalancedDirectBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        extended.size = block.size + 1) ∨
      Nonempty (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      block.HasNaturalTokenEscape ∨
      Nonempty (CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      ∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
          canonicalStableRawSourceRank ends m j k l zero p u.source <
            canonicalStableRawSourceRank ends m j k l zero p
              source.1.source := by
  rcases hcross.growth_or_self_or_naturalEscape_or_stableSelf_or_rankDrop with
    hgrowth | hself | hescape | hstable | hadvancing
  · exact Or.inl hgrowth
  · exact Or.inr (Or.inl hself)
  · exact Or.inr (Or.inr (Or.inl hescape))
  · rcases hstable.terminal_or_rankDrop with hterminal | hrank
    · exact Or.inr (Or.inr (Or.inr (Or.inl hterminal)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hrank)))
  · obtain ⟨source, _index, _oldIndex, _hsource, _hcrossing, _hnatural,
      u, _hu, _htarget, _hkind, hrank⟩ := hadvancing
    have huComponent : canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
      rw [_hu]
      exact (block.directs _oldIndex).2.1
    exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨source, u, huComponent, hrank⟩)))






theorem
    CanonicalStableRawTightChargeOrbit.HasBalancedResidualDeficit.complementTightFamily_or_geometricCrossing
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (hresidual : orbit.HasBalancedResidualDeficit)
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ block : CanonicalStableRawComponentBalancedDirectBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      (block.IsClosed ∧
        Fintype.card block.StateComplement <
          Fintype.card (CanonicalStableRawComponentState
            ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
        Fintype.card block.TokenComplement <
          Fintype.card block.StateComplement ∧
        (∃ family : Finset block.StateComplement,
          family.Nonempty ∧
          (block.complementNeighborhood family).card + 1 = family.card ∧
          (∀ source ∈ family,
            block.complementNeighborhood (family.erase source) =
              block.complementNeighborhood family) ∧
          ∀ smaller : Finset block.StateComplement, smaller ⊂ family ->
            smaller.card ≤ (block.complementNeighborhood smaller).card) ∧
        ∀ source : block.StateComplement, ∀ token,
          CanonicalStableRawComponentIncident
              ends m j k l zero hloop hjk hkl hk0 p hno component
                source.1 token ->
            token ∉ finiteEmbeddingBlock block.size block.tokenBlock) ∨
      block.HasGeometricCrossing := by
  obtain ⟨block, _hstrict⟩ := hresidual.exists_block
  refine ⟨block, ?_⟩
  rcases block.closed_or_crossing with hclosed |
      ⟨source, token, hincident, hsource, index, htoken⟩
  · left
    exact ⟨hclosed, block.stateComplement_card_lt,
      block.complement_strictDeficit hdeficit,
      block.exists_minimalComplementTightFamily hdeficit,
      fun source token hincident =>
        hclosed.restricts_incidence source token hincident⟩
  · right
    exact block.geometricCrossing_of_crossing
      source token hincident hsource index htoken





theorem
    CanonicalStableRawTightChargeOrbit.HasBalancedResidualDeficit.smallerRecursion_or_crossingContinuation
    {I : Type uI} {W : Type uW} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W]
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (hresidual : orbit.HasBalancedResidualDeficit)
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ block : CanonicalStableRawComponentBalancedDirectBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      (block.IsClosed ∧
        ∃ problem : FiniteRelationMinimalTightProblem.{uI, uI},
          problem.rank < Fintype.card (CanonicalStableRawComponentState
            ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
          ∀ source : block.StateComplement,
            ∀ token : CanonicalStableRawComponentToken
                ends m j k l zero hloop hjk hkl hk0 p hno component,
              CanonicalStableRawComponentIncident
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    source.1 token ->
                token ∉ finiteEmbeddingBlock block.size block.tokenBlock) ∨
      (block.HasGeometricCrossing ∧
        ∃ continuation : FiniteRelationCrossingContinuation
            (CanonicalStableRawComponentIncident
              ends m j k l zero hloop hjk hkl hk0 p hno component),
          continuation.size = block.size ∧
          let move :=
            StatMech.FrontierA.RelationPartialMatching.HoleState.move
              continuation.natural continuation.natural_incident
          ∃ start stop : Nat, start < stop ∧ stop ≤ block.size + 1 ∧
            (move^[start] continuation.initialHoleState).hole =
              (move^[stop] continuation.initialHoleState).hole ∧
            ∀ a b : Nat, a < b -> b < stop ->
              (move^[a] continuation.initialHoleState).hole ≠
                (move^[b] continuation.initialHoleState).hole) := by
  obtain ⟨block, _hstrict⟩ := hresidual.exists_block
  refine ⟨block, ?_⟩
  rcases block.closed_or_crossing with hclosed |
      ⟨source, token, hincident, hsource, index, htoken⟩
  · left
    exact ⟨hclosed,
      block.exists_smallerComplementMinimalTightProblem hclosed hdeficit⟩
  · right
    let hgeometric := block.geometricCrossing_of_crossing
      source token hincident hsource index htoken
    exact ⟨hgeometric, hgeometric.exists_crossingContinuation⟩



theorem
    CanonicalStableRawTightChargeOrbit.HasRetainedSharedTokenOutput.local_or_directOrbit
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (houtput : orbit.HasRetainedSharedTokenOutput)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.LocalMergerDischarge ∨ orbit.HasDirectOrbitDischarge := by
  rcases houtput.local_or_firstDirectStep herase with hlocal |
      ⟨_houtput, source, _q, _first, second, _hsourceNe, _hfirstSecond,
        _hfirst, _hsecond, hstep⟩
  · exact Or.inl hlocal
  · exact Or.inr ⟨source, second, hstep,
      exists_canonicalStableRawComponentDirect_terminal_or_balancedBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component second⟩


theorem
    CanonicalStableRawTightChargeOrbit.HasFreshInternalChordOutput.local_or_directOrbit
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (houtput : orbit.HasFreshInternalChordOutput)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.LocalMergerDischarge ∨ orbit.HasDirectOrbitDischarge := by
  rcases houtput.local_or_firstDirectStep herase with hlocal |
      ⟨_houtput, q, _r, _first, second, _hqr, _hfirstSecond,
        _hfirst, _hsecond, hstep⟩
  · exact Or.inl hlocal
  · exact Or.inr ⟨orbit.states q, second, hstep,
      exists_canonicalStableRawComponentDirect_terminal_or_balancedBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component second⟩





theorem
    exists_canonicalStableRawComponent_maximalOrbitDischarge_of_deficit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ sources : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      sources.Nonempty ∧
      (canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources).card +
          1 = sources.card ∧
      (∀ source ∈ sources,
        canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (sources.erase source) =
          canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∧
      (∀ smaller : Finset (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component),
        smaller ⊂ sources ->
          smaller.card ≤
            (canonicalStableRawComponentIncidentNeighborhood
              ends m j k l zero hloop hjk hkl hk0 p hno component
                smaller).card) ∧
      ∃ orbit : CanonicalStableRawTightChargeOrbit
          ends m j k l zero hloop hjk hkl hk0 p hno component sources,
        2 ≤ orbit.size ∧
        (orbit.HasRetainedSharedTokenOutput ∨
          orbit.HasFreshInternalChordOutput ∨
          (∃ source : ↑sources,
            ∃ u : CanonicalStableRawExceptionalEdge
                ends m j k l zero hloop hjk hkl hk0 p,
              canonicalStableRawTokenComponent
                    ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
                canonicalStableRawSourceRank ends m j k l zero p u.source <
                  canonicalStableRawSourceRank ends m j k l zero p
                    source.1.1.source) ∨
          orbit.LocalMergerDischarge) := by
  classical
  obtain ⟨sources, hnonempty, htight, herase, hproper⟩ :=
    exists_canonicalStableRawComponent_minimalIncidentObstruction_of_deficit
      ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit
  obtain ⟨orbit, hsize, hmax⟩ :=
    exists_canonicalStableRawTightComponent_sizeMaximalChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources htight
  exact ⟨sources, hnonempty, htight, herase, hproper, orbit, hsize,
    orbit.maximalSaturationStep_localDischarge hmax herase htight⟩






theorem
    exists_canonicalStableRawComponent_maximalOrbitSharpDischarge_of_deficit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ sources : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      sources.Nonempty ∧
      (canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources).card +
          1 = sources.card ∧
      (∀ source ∈ sources,
        canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (sources.erase source) =
          canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∧
      (∀ smaller : Finset (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component),
        smaller ⊂ sources ->
          smaller.card ≤
            (canonicalStableRawComponentIncidentNeighborhood
              ends m j k l zero hloop hjk hkl hk0 p hno component
                smaller).card) ∧
      ∃ orbit : CanonicalStableRawTightChargeOrbit
          ends m j k l zero hloop hjk hkl hk0 p hno component sources,
        2 ≤ orbit.size ∧
        ((∃ source : ↑sources,
            ∃ u : CanonicalStableRawExceptionalEdge
                ends m j k l zero hloop hjk hkl hk0 p,
              canonicalStableRawTokenComponent
                    ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
                canonicalStableRawSourceRank ends m j k l zero p u.source <
                  canonicalStableRawSourceRank ends m j k l zero p
                    source.1.1.source) ∨
          orbit.LocalMergerDischarge ∨ orbit.HasDirectOrbitDischarge) := by
  classical
  obtain ⟨sources, hnonempty, htight, herase, hproper⟩ :=
    exists_canonicalStableRawComponent_minimalIncidentObstruction_of_deficit
      ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit
  obtain ⟨orbit, hsize, hmax⟩ :=
    exists_canonicalStableRawTightComponent_sizeMaximalChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources htight
  rcases orbit.maximalSaturationStep_sharp hmax herase htight with
    hretained | hrank | hlocal
  · rcases hretained.local_or_directOrbit herase with hlocal | horbit
    · exact ⟨sources, hnonempty, htight, herase, hproper, orbit, hsize,
        Or.inr (Or.inl hlocal)⟩
    · exact ⟨sources, hnonempty, htight, herase, hproper, orbit, hsize,
        Or.inr (Or.inr horbit)⟩
  · exact ⟨sources, hnonempty, htight, herase, hproper, orbit, hsize,
      Or.inl hrank⟩
  · exact ⟨sources, hnonempty, htight, herase, hproper, orbit, hsize,
      Or.inr (Or.inl hlocal)⟩







theorem
    exists_canonicalStableRawComponent_maximalOrbitResidualDischarge_of_deficit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ sources : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      sources.Nonempty ∧
      (canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources).card +
          1 = sources.card ∧
      (∀ source ∈ sources,
        canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (sources.erase source) =
          canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∧
      (∀ smaller : Finset (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component),
        smaller ⊂ sources ->
          smaller.card ≤
            (canonicalStableRawComponentIncidentNeighborhood
              ends m j k l zero hloop hjk hkl hk0 p hno component
                smaller).card) ∧
      ∃ orbit : CanonicalStableRawTightChargeOrbit
          ends m j k l zero hloop hjk hkl hk0 p hno component sources,
        2 ≤ orbit.size ∧
        ((∃ source : ↑sources,
            ∃ u : CanonicalStableRawExceptionalEdge
                ends m j k l zero hloop hjk hkl hk0 p,
              canonicalStableRawTokenComponent
                    ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
                canonicalStableRawSourceRank ends m j k l zero p u.source <
                  canonicalStableRawSourceRank ends m j k l zero p
                    source.1.1.source) ∨
          orbit.LocalMergerDischarge ∨
          Nonempty (CanonicalStableRawComponentRichStrictBlock
            ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
          orbit.HasBalancedResidualDeficit) := by
  obtain ⟨sources, hnonempty, htight, herase, hproper, orbit, hsize,
      hrank | hlocal | hdischarge⟩ :=
    exists_canonicalStableRawComponent_maximalOrbitSharpDischarge_of_deficit
      ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit
  · exact ⟨sources, hnonempty, htight, herase, hproper, orbit, hsize,
      Or.inl hrank⟩
  · exact ⟨sources, hnonempty, htight, herase, hproper, orbit, hsize,
      Or.inr (Or.inl hlocal)⟩
  · rcases hdischarge.richStrict_or_balancedResidual
        hdeficit with hrich | hresidual
    · exact ⟨sources, hnonempty, htight, herase, hproper, orbit, hsize,
        Or.inr (Or.inr (Or.inl hrich))⟩
    · exact ⟨sources, hnonempty, htight, herase, hproper, orbit, hsize,
        Or.inr (Or.inr (Or.inr hresidual))⟩

noncomputable def CanonicalStableRawComponentBalancedDirectBlock.directSuccessorStep
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (index : Fin block.size) :
    Fin block.size ⊕ CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
  let successor := canonicalStableRawComponentSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
      (block.sourceBlock index)
  if hmem : successor ∈ finiteEmbeddingBlock block.size block.tokenBlock then
    Sum.inl (Classical.choose (Finset.mem_map.mp hmem))
  else Sum.inr successor

theorem CanonicalStableRawComponentBalancedDirectBlock.directSuccessorStep_eq_inl
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (index next : Fin block.size)
    (hstep : block.directSuccessorStep index = Sum.inl next) :
    next ≠ index ∧
      canonicalStableRawComponentSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (block.sourceBlock index) = block.tokenBlock next := by
  classical
  unfold CanonicalStableRawComponentBalancedDirectBlock.directSuccessorStep at hstep
  dsimp only at hstep
  split at hstep
  next hmem =>
    have hnext : Classical.choose (Finset.mem_map.mp hmem) = next :=
      Sum.inl.inj hstep
    have hchosen := (Classical.choose_spec (Finset.mem_map.mp hmem)).2
    have htoken := hchosen.symm.trans (congrArg block.tokenBlock hnext)
    refine ⟨?_, htoken⟩
    intro hnextIndex
    apply canonicalStableRawComponentSuccessorToken_ne_natural
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (block.sourceBlock index)
    exact htoken.trans (congrArg block.tokenBlock hnextIndex)
  next hnot => contradiction

theorem CanonicalStableRawComponentBalancedDirectBlock.directSuccessorStep_eq_inr
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (index : Fin block.size)
    (token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstep : block.directSuccessorStep index = Sum.inr token) :
    token = canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component
          (block.sourceBlock index) ∧
      token ∉ finiteEmbeddingBlock block.size block.tokenBlock := by
  classical
  unfold CanonicalStableRawComponentBalancedDirectBlock.directSuccessorStep at hstep
  dsimp only at hstep
  split at hstep
  next hmem => contradiction
  next hnot => exact ⟨Sum.inr.inj hstep.symm, by simpa only [Sum.inr.inj hstep.symm] using hnot⟩

abbrev CanonicalStableRawComponentBalancedDirectBlock.PostSecondState
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (_block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :=
  Unit ⊕ Fin _block.size

noncomputable def CanonicalStableRawComponentBalancedDirectBlock.postSecondStep
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (entrance : Fin block.size) :
    block.PostSecondState -> block.PostSecondState ⊕
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component
  | Sum.inl _ => Sum.inl (Sum.inr entrance)
  | Sum.inr index =>
      match block.directSuccessorStep index with
      | Sum.inl next => Sum.inl (Sum.inr next)
      | Sum.inr token => Sum.inr token

theorem CanonicalStableRawComponentBalancedDirectBlock.exists_postSecond_terminal_or_cycle
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (entrance : Fin block.size) :
    (∃ n ≤ block.size + 1, ∃ token,
      block.postSecondStep entrance
        ((partialForestAdvance (block.postSecondStep entrance))^[n]
          (Sum.inl ())) = Sum.inr token ∧
      token ∉ finiteEmbeddingBlock block.size block.tokenBlock) ∨
    ∃ i j : Nat, i < j ∧ j ≤ block.size + 1 ∧
      ((partialForestAdvance (block.postSecondStep entrance))^[i]
        (Sum.inl ())) =
      ((partialForestAdvance (block.postSecondStep entrance))^[j]
        (Sum.inl ())) ∧
      (∀ n < j, ∃ next,
        block.postSecondStep entrance
          ((partialForestAdvance (block.postSecondStep entrance))^[n]
            (Sum.inl ())) = Sum.inl next) := by
  rcases exists_partialForest_terminal_or_cycle
      (block.postSecondStep entrance) (Sum.inl ()) with
    hterminal | hcycle
  · left
    obtain ⟨n, hn, token, htoken⟩ := hterminal
    refine ⟨n, by simpa only [CanonicalStableRawComponentBalancedDirectBlock.PostSecondState,
      Fintype.card_sum, Fintype.card_unit, Fintype.card_fin,
      Nat.add_comm] using hn,
      token, htoken, ?_⟩
    let state :=
      (partialForestAdvance (block.postSecondStep entrance))^[n]
        (Sum.inl ())
    change block.postSecondStep entrance state = Sum.inr token at htoken
    obtain ⟨index, hstate⟩ : ∃ index,
        state = Sum.inr index := by
      cases hstate : state with
      | inl unit =>
          simp [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
            hstate] at htoken
      | inr index => exact ⟨index, rfl⟩
    rw [hstate] at htoken
    change (match block.directSuccessorStep index with
      | Sum.inl next => Sum.inl (Sum.inr next)
      | Sum.inr token => Sum.inr token) = Sum.inr token at htoken
    cases hdirect : block.directSuccessorStep index with
    | inl next => simp [hdirect] at htoken
    | inr fresh =>
        simp only [hdirect, Sum.inr.injEq] at htoken
        subst fresh
        exact (block.directSuccessorStep_eq_inr index token hdirect).2
  · right
    obtain ⟨i, j, hij, hj, hrepeat, hsteps⟩ := hcycle
    exact ⟨i, j, hij, by simpa only [CanonicalStableRawComponentBalancedDirectBlock.PostSecondState,
      Fintype.card_sum, Fintype.card_unit, Fintype.card_fin,
      Nat.add_comm] using hj,
      hrepeat, hsteps⟩



abbrev PartialForestNonbacktrackingState (A : Type*) :=
  { pair : A × A // pair.1 ≠ pair.2 }




noncomputable def partialForestNonbacktrackingStep
    {A B : Type*} (step : A → A ⊕ B)
    (hloopFree : ∀ current next, step current = Sum.inl next →
      next ≠ current) :
    PartialForestNonbacktrackingState A →
      PartialForestNonbacktrackingState A ⊕ (B ⊕ Unit) := by
  classical
  exact fun state =>
    match hstep : step state.1.2 with
    | Sum.inr terminal => Sum.inr (Sum.inl terminal)
    | Sum.inl next =>
        if hback : next = state.1.1 then Sum.inr (Sum.inr ())
        else Sum.inl ⟨(state.1.2, next),
          (hloopFree state.1.2 next hstep).symm⟩

theorem partialForestNonbacktrackingStep_eq_inl
    {A B : Type*} (step : A → A ⊕ B)
    (hloopFree : ∀ current next, step current = Sum.inl next →
      next ≠ current)
    (state next : PartialForestNonbacktrackingState A)
    (hstep : partialForestNonbacktrackingStep step hloopFree state =
      Sum.inl next) :
    next.1.1 = state.1.2 ∧ next.1.2 ≠ state.1.1 := by
  classical
  unfold partialForestNonbacktrackingStep at hstep
  split at hstep
  next terminal hterminal => contradiction
  next continued hcontinued =>
    split at hstep
    next hback => contradiction
    next hnotBack =>
      have hnext : (⟨(state.1.2, continued),
          (hloopFree state.1.2 continued hcontinued).symm⟩ :
            PartialForestNonbacktrackingState A) = next :=
        Sum.inl.inj hstep
      rw [← hnext]
      exact ⟨rfl, hnotBack⟩

theorem partialForestNonbacktrackingStep_eq_terminal
    {A B : Type*} (step : A → A ⊕ B)
    (hloopFree : ∀ current next, step current = Sum.inl next →
      next ≠ current)
    (state : PartialForestNonbacktrackingState A) (terminal : B)
    (hstep : partialForestNonbacktrackingStep step hloopFree state =
      Sum.inr (Sum.inl terminal)) :
    step state.1.2 = Sum.inr terminal := by
  classical
  unfold partialForestNonbacktrackingStep at hstep
  split at hstep
  next terminal' hterminal =>
    exact hterminal.trans (congrArg Sum.inr (Sum.inl.inj (Sum.inr.inj hstep)))
  next continued hcontinued =>
    split at hstep <;> simp at hstep

theorem partialForestNonbacktrackingStep_eq_backtrack
    {A B : Type*} (step : A → A ⊕ B)
    (hloopFree : ∀ current next, step current = Sum.inl next →
      next ≠ current)
    (state : PartialForestNonbacktrackingState A)
    (hstep : partialForestNonbacktrackingStep step hloopFree state =
      Sum.inr (Sum.inr ())) :
    step state.1.2 = Sum.inl state.1.1 := by
  classical
  unfold partialForestNonbacktrackingStep at hstep
  split at hstep
  next terminal hterminal => simp at hstep
  next continued hcontinued =>
    split at hstep
    next hback => exact hcontinued.trans (congrArg Sum.inl hback)
    next hnotBack => contradiction




theorem exists_partialForest_terminal_or_backtrack_or_longCycle
    {A B : Type*} [Fintype A] [DecidableEq A]
    (step : A → A ⊕ B)
    (hloopFree : ∀ current next, step current = Sum.inl next →
      next ≠ current)
    (start : PartialForestNonbacktrackingState A) :
    ( ∃ n ≤ Fintype.card (PartialForestNonbacktrackingState A),
        ∃ terminal, step
          (((partialForestAdvance
            (partialForestNonbacktrackingStep step hloopFree))^[n]
              start).1.2) = Sum.inr terminal) ∨
    ( ∃ n ≤ Fintype.card (PartialForestNonbacktrackingState A),
        step (((partialForestAdvance
          (partialForestNonbacktrackingStep step hloopFree))^[n]
            start).1.2) =
          Sum.inl (((partialForestAdvance
            (partialForestNonbacktrackingStep step hloopFree))^[n]
              start).1.1)) ∨
    ∃ i j : Nat, i + 3 ≤ j ∧
      j ≤ Fintype.card (PartialForestNonbacktrackingState A) ∧
      ((partialForestAdvance
          (partialForestNonbacktrackingStep step hloopFree))^[i] start) =
        ((partialForestAdvance
          (partialForestNonbacktrackingStep step hloopFree))^[j] start) ∧
      ∀ n < j, ∃ next,
        partialForestNonbacktrackingStep step hloopFree
          ((partialForestAdvance
            (partialForestNonbacktrackingStep step hloopFree))^[n]
              start) = Sum.inl next := by
  classical
  let lifted := partialForestNonbacktrackingStep step hloopFree
  let advance := partialForestAdvance lifted
  rcases exists_partialForest_terminal_or_cycle lifted start with
    hterminal | ⟨i, j, hij, hj, hrepeat, hsteps⟩
  · obtain ⟨n, hn, terminal, hterminal⟩ := hterminal
    rcases terminal with terminal | unit
    · left
      refine ⟨n, hn, terminal, ?_⟩
      exact partialForestNonbacktrackingStep_eq_terminal
        step hloopFree (advance^[n] start) terminal hterminal
    · right
      left
      refine ⟨n, hn, ?_⟩
      exact partialForestNonbacktrackingStep_eq_backtrack
        step hloopFree (advance^[n] start) (by simpa using hterminal)
  · right
    right
    have hshift (n : Nat) (hn : n < j) :
        (advance^[n + 1] start).1.1 = (advance^[n] start).1.2 ∧
          (advance^[n + 1] start).1.2 ≠ (advance^[n] start).1.1 := by
      obtain ⟨next, hnext⟩ := hsteps n hn
      have hnextShape := partialForestNonbacktrackingStep_eq_inl
        step hloopFree (advance^[n] start) next hnext
      have hadvance : advance^[n + 1] start = next := by
        rw [show n + 1 = Nat.succ n by omega]
        rw [Function.iterate_succ_apply']
        change partialForestAdvance lifted (advance^[n] start) = next
        unfold partialForestAdvance
        rw [hnext]
      rw [hadvance]
      exact hnextShape
    have hlong : i + 3 ≤ j := by
      by_contra hnotLong
      have hshort : j = i + 1 ∨ j = i + 2 := by omega
      rcases hshort with hshort | hshort
      · have hfirst := (hshift i (by omega)).1
        apply (advance^[i] start).2
        calc
          (advance^[i] start).1.1 = (advance^[j] start).1.1 :=
            congrArg (fun state => state.1.1) hrepeat
          _ = (advance^[i] start).1.2 := by
            simpa only [hshort] using hfirst
      · have hfirst := (hshift i (by omega)).2
        have hsecond := (hshift (i + 1) (by omega)).1
        apply hfirst
        calc
          (advance^[i + 1] start).1.2 =
              (advance^[i + 2] start).1.1 := hsecond.symm
          _ = (advance^[j] start).1.1 := by rw [hshort]
          _ = (advance^[i] start).1.1 :=
            congrArg (fun state => state.1.1) hrepeat.symm
    exact ⟨i, j, hlong, hj, hrepeat, hsteps⟩

theorem CanonicalStableRawComponentBalancedDirectBlock.postSecondStep_continuation_ne
    {ends : I → Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (entrance : Fin block.size) (state next : block.PostSecondState)
    (hstep : block.postSecondStep entrance state = Sum.inl next) :
    next ≠ state := by
  cases state with
  | inl outside =>
      have hnext : Sum.inr entrance = next := by
        simpa only [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
          Sum.inl.injEq] using hstep
      rw [← hnext]
      simp
  | inr index =>
      cases hdirect : block.directSuccessorStep index with
      | inl retained =>
          have hnext : Sum.inr retained = next := by
            simpa only [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
              hdirect, Sum.inl.injEq] using hstep
          rw [← hnext]
          intro heq
          apply (block.directSuccessorStep_eq_inl index retained hdirect).1
          exact Sum.inr.inj heq
      | inr terminal =>
          simp [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
            hdirect] at hstep

theorem CanonicalStableRawComponentBalancedDirectBlock.postSecondStep_terminal_fresh
    {ends : I → Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (entrance : Fin block.size) (state : block.PostSecondState)
    (token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstep : block.postSecondStep entrance state = Sum.inr token) :
    token ∉ finiteEmbeddingBlock block.size block.tokenBlock := by
  cases hstate : state with
  | inl outside =>
      simp [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
        hstate] at hstep
  | inr index =>
      rw [hstate] at hstep
      cases hdirect : block.directSuccessorStep index with
      | inl retained =>
          simp [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
            hdirect] at hstep
      | inr fresh =>
          simp only [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
            hdirect, Sum.inr.injEq] at hstep
          subst fresh
          exact (block.directSuccessorStep_eq_inr index token hdirect).2

abbrev CanonicalStableRawComponentBalancedDirectBlock.PostSecondContinuationState
    {ends : I → Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :=
  PartialForestNonbacktrackingState block.PostSecondState

def CanonicalStableRawComponentBalancedDirectBlock.postSecondInitialState
    {ends : I → Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (entrance : Fin block.size) : block.PostSecondContinuationState :=
  ⟨(Sum.inl (), Sum.inr entrance), by simp⟩

noncomputable def
    CanonicalStableRawComponentBalancedDirectBlock.postSecondContinuationStep
    {ends : I → Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (entrance : Fin block.size) :
    block.PostSecondContinuationState →
      block.PostSecondContinuationState ⊕
        (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕ Unit) :=
  partialForestNonbacktrackingStep (block.postSecondStep entrance)
    (block.postSecondStep_continuation_ne entrance)





theorem CanonicalStableRawComponentBalancedDirectBlock.exists_postSecond_terminal_or_backtrack_or_longCycle
    {ends : I → Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (entrance : Fin block.size) :
    let lifted := block.postSecondContinuationStep entrance
    let advance := partialForestAdvance lifted
    let start := block.postSecondInitialState entrance
    ( ∃ n ≤ Fintype.card block.PostSecondContinuationState,
        ∃ token, block.postSecondStep entrance
          (advance^[n] start).1.2 = Sum.inr token ∧
          token ∉ finiteEmbeddingBlock block.size block.tokenBlock) ∨
    ( ∃ n ≤ Fintype.card block.PostSecondContinuationState,
        block.postSecondStep entrance (advance^[n] start).1.2 =
          Sum.inl (advance^[n] start).1.1) ∨
    ∃ i j : Nat, i + 3 ≤ j ∧
      j ≤ Fintype.card block.PostSecondContinuationState ∧
      advance^[i] start = advance^[j] start ∧
      ∀ n < j, ∃ next, lifted (advance^[n] start) = Sum.inl next := by
  classical
  dsimp only
  rcases exists_partialForest_terminal_or_backtrack_or_longCycle
      (block.postSecondStep entrance)
      (block.postSecondStep_continuation_ne entrance)
      (block.postSecondInitialState entrance) with
    hterminal | hbacktrack | hcycle
  · left
    obtain ⟨n, hn, token, htoken⟩ := hterminal
    exact ⟨n, hn, token, htoken,
      block.postSecondStep_terminal_fresh entrance _ token htoken⟩
  · exact Or.inr (Or.inl hbacktrack)
  · exact Or.inr (Or.inr hcycle)


theorem CanonicalStableRawComponentBalancedDirectBlock.postSecondStep_terminal_growth_or_nonexceptional
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (entrance : Fin block.size) (state : block.PostSecondState)
    (token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstep : block.postSecondStep entrance state = Sum.inr token) :
    (∃ extended : CanonicalStableRawComponentBalancedDirectBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        extended.size = block.size + 1) ∨
      Nonempty (CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  obtain ⟨index, hstate⟩ : ∃ index, state = Sum.inr index := by
    cases hstate : state with
    | inl outside =>
        simp [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
          hstate] at hstep
    | inr index => exact ⟨index, rfl⟩
  rw [hstate] at hstep
  cases hdirect : block.directSuccessorStep index with
  | inl retained =>
      simp [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
        hdirect] at hstep
  | inr fresh =>
      simp only [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
        hdirect, Sum.inr.injEq] at hstep
      subst fresh
      have hdata := block.directSuccessorStep_eq_inr index token hdirect
      have htoken := hdata.1
      have hfresh := hdata.2
      cases hforest : canonicalStableRawComponentForestStep
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (block.sourceBlock index) with
      | inr terminal => exact Or.inr ⟨terminal⟩
      | inl direct =>
          left
          have hforestToken := canonicalStableRawComponentForestStep_token
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (block.sourceBlock index)
          rw [hforest] at hforestToken
          have hdirectFresh : ∀ q, direct ≠ block.directs q := by
            intro q heq
            apply hfresh
            apply Finset.mem_map.mpr
            refine ⟨q, Finset.mem_univ _, ?_⟩
            calc
              block.tokenBlock q =
                  canonicalStableRawComponentDirectEmbedding
                    ends m j k l zero hloop hjk hkl hk0 p hno component
                      (block.directs q) := rfl
              _ = canonicalStableRawComponentDirectEmbedding
                    ends m j k l zero hloop hjk hkl hk0 p hno component
                      direct := congrArg _ heq.symm
              _ = canonicalStableRawComponentSuccessorToken
                    ends m j k l zero hloop hjk hkl hk0 p hno component
                      (block.sourceBlock index) := hforestToken
              _ = token := htoken.symm
          obtain ⟨directs, _hprefix, _hlast⟩ :=
            finiteEmbedding_snoc block.size block.directs direct hdirectFresh
          let tokens : Fin (block.size + 1) ↪
              CanonicalStableRawComponentToken
                ends m j k l zero hloop hjk hkl hk0 p hno component :=
            directs.trans (canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component)
          exact ⟨⟨block.size + 1, by omega, directs, tokens⟩, rfl⟩


noncomputable def
    CanonicalStableRawComponentBalancedDirectBlock.postSecondContinuationAdvance
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (entrance : Fin block.size) :
    block.PostSecondContinuationState ->
      block.PostSecondContinuationState :=
  partialForestAdvance (block.postSecondContinuationStep entrance)

noncomputable def
    CanonicalStableRawComponentBalancedDirectBlock.HasPostSecondBacktrack
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (entrance : Fin block.size) : Prop :=
  ∃ n ≤ Fintype.card block.PostSecondContinuationState,
    block.postSecondStep entrance
      ((block.postSecondContinuationAdvance entrance)^[n]
        (block.postSecondInitialState entrance)).1.2 =
      Sum.inl
        ((block.postSecondContinuationAdvance entrance)^[n]
          (block.postSecondInitialState entrance)).1.1

noncomputable def
    CanonicalStableRawComponentBalancedDirectBlock.HasPostSecondLongCycle
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (entrance : Fin block.size) : Prop :=
  let advance := block.postSecondContinuationAdvance entrance
  let start := block.postSecondInitialState entrance
  ∃ i j : Nat, i + 3 ≤ j ∧
    j ≤ Fintype.card block.PostSecondContinuationState ∧
    advance^[i] start = advance^[j] start ∧
    ∀ n < j, ∃ next,
      block.postSecondContinuationStep entrance (advance^[n] start) =
        Sum.inl next

theorem CanonicalStableRawComponentBalancedDirectBlock.postSecond_growth_or_nonexceptional_or_backtrack_or_longCycle
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (entrance : Fin block.size) :
    (∃ extended : CanonicalStableRawComponentBalancedDirectBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        extended.size = block.size + 1) ∨
      Nonempty (CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      block.HasPostSecondBacktrack entrance ∨
      block.HasPostSecondLongCycle entrance := by
  classical
  rcases block.exists_postSecond_terminal_or_backtrack_or_longCycle entrance with
    hterminal | hbacktrack | hcycle
  · obtain ⟨n, _hn, token, hstep, _hfresh⟩ := hterminal
    rcases block.postSecondStep_terminal_growth_or_nonexceptional entrance
        _ token hstep with hgrowth | hterminal
    · exact Or.inl hgrowth
    · exact Or.inr (Or.inl hterminal)
  · exact Or.inr (Or.inr (Or.inl hbacktrack))
  · exact Or.inr (Or.inr (Or.inr hcycle))

theorem CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.growth_or_self_or_augmented_or_postSecond_or_terminal_or_rankDrop
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    (hcross : block.HasGeometricCrossing) :
    (∃ extended : CanonicalStableRawComponentBalancedDirectBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        extended.size = block.size + 1) ∨
      Nonempty (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      block.HasAugmentedIncidentBlock ∨
      (∃ entrance, block.HasPostSecondBacktrack entrance) ∨
      (∃ entrance, block.HasPostSecondLongCycle entrance) ∨
      Nonempty (CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      ∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
          canonicalStableRawSourceRank ends m j k l zero p u.source <
            canonicalStableRawSourceRank ends m j k l zero p
              source.1.source := by
  rcases hcross.growth_or_self_or_naturalEscape_or_terminal_or_rankDrop with
    hgrowth | hself | hescape | hterminal | hrank
  · exact Or.inl hgrowth
  · exact Or.inr (Or.inl hself)
  · rcases hescape.augmentedBlock_or_alternate with haugmented |
        ⟨_source, _index, entrance, _hsource, _hcrossing, _hne, _hnatural⟩
    · exact Or.inr (Or.inr (Or.inl haugmented))
    · rcases block.postSecond_growth_or_nonexceptional_or_backtrack_or_longCycle
          entrance with hgrowth | hterminal | hbacktrack | hcycle
      · exact Or.inl hgrowth
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hterminal)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨entrance, hbacktrack⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨entrance, hcycle⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hterminal)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hrank)))))


theorem partialForestNonbacktrackingStep_eq_inl_relation
    {A B : Type*} (step : A -> A ⊕ B)
    (hloopFree : ∀ current next, step current = Sum.inl next ->
      next ≠ current)
    (state next : PartialForestNonbacktrackingState A)
    (hstep : partialForestNonbacktrackingStep step hloopFree state =
      Sum.inl next) :
    step next.1.1 = Sum.inl next.1.2 := by
  classical
  unfold partialForestNonbacktrackingStep at hstep
  split at hstep
  next terminal hterminal => contradiction
  next continued hcontinued =>
    split at hstep
    next hback => contradiction
    next hnotBack =>
      have hnext : (⟨(state.1.2, continued),
          (hloopFree state.1.2 continued hcontinued).symm⟩ :
            PartialForestNonbacktrackingState A) = next :=
        Sum.inl.inj hstep
      rw [← hnext]
      exact hcontinued

theorem CanonicalStableRawComponentBalancedDirectBlock.postSecondContinuationAdvance_invariant
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (entrance : Fin block.size) (n : Nat) :
    let state := (block.postSecondContinuationAdvance entrance)^[n]
      (block.postSecondInitialState entrance)
    block.postSecondStep entrance state.1.1 = Sum.inl state.1.2 := by
  classical
  induction n with
  | zero =>
      simp [CanonicalStableRawComponentBalancedDirectBlock.postSecondInitialState,
        CanonicalStableRawComponentBalancedDirectBlock.postSecondStep]
  | succ n ih =>
      let previous := (block.postSecondContinuationAdvance entrance)^[n]
        (block.postSecondInitialState entrance)
      have hiterate :
          (block.postSecondContinuationAdvance entrance)^[Nat.succ n]
              (block.postSecondInitialState entrance) =
            block.postSecondContinuationAdvance entrance previous := by
        exact Function.iterate_succ_apply'
          (block.postSecondContinuationAdvance entrance) n
            (block.postSecondInitialState entrance)
      rw [hiterate]
      cases hcontinued : block.postSecondContinuationStep entrance previous with
      | inl next =>
          have hadvance : block.postSecondContinuationAdvance entrance previous =
              next := by
            unfold CanonicalStableRawComponentBalancedDirectBlock.postSecondContinuationAdvance
            unfold partialForestAdvance
            rw [hcontinued]
          rw [hadvance]
          exact partialForestNonbacktrackingStep_eq_inl_relation
            (block.postSecondStep entrance)
            (block.postSecondStep_continuation_ne entrance)
            previous next hcontinued
      | inr terminal =>
          have hadvance : block.postSecondContinuationAdvance entrance previous =
              previous := by
            unfold CanonicalStableRawComponentBalancedDirectBlock.postSecondContinuationAdvance
            unfold partialForestAdvance
            rw [hcontinued]
          rw [hadvance]
          exact ih

theorem CanonicalStableRawComponentBalancedDirectBlock.HasPostSecondBacktrack.exists_twoCycle
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    {entrance : Fin block.size} (hback : block.HasPostSecondBacktrack entrance) :
    ∃ previous current : block.PostSecondState,
      previous ≠ current ∧
      block.postSecondStep entrance previous = Sum.inl current ∧
      block.postSecondStep entrance current = Sum.inl previous := by
  obtain ⟨n, _hn, hreverse⟩ := hback
  let state := (block.postSecondContinuationAdvance entrance)^[n]
    (block.postSecondInitialState entrance)
  exact ⟨state.1.1, state.1.2, state.2,
    block.postSecondContinuationAdvance_invariant entrance n, hreverse⟩

theorem CanonicalStableRawComponentBalancedDirectBlock.HasPostSecondBacktrack.exists_directIndexTwoCycle
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    {entrance : Fin block.size} (hback : block.HasPostSecondBacktrack entrance) :
    ∃ previous current : Fin block.size, previous ≠ current ∧
      block.directSuccessorStep previous = Sum.inl current ∧
      block.directSuccessorStep current = Sum.inl previous := by
  obtain ⟨previous, current, hne, hforward, hreverse⟩ := hback.exists_twoCycle
  obtain ⟨previousIndex, hprevious⟩ : ∃ index, previous = Sum.inr index := by
    cases hprevious : previous with
    | inl outside =>
        have hcurrent : current = Sum.inr entrance := by
          simpa [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
            hprevious] using hforward.symm
        rw [hprevious, hcurrent] at hreverse
        cases hdirect : block.directSuccessorStep entrance <;>
          simp [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
            hdirect] at hreverse
    | inr index => exact ⟨index, rfl⟩
  obtain ⟨currentIndex, hcurrent⟩ : ∃ index, current = Sum.inr index := by
    cases hcurrent : current with
    | inl outside =>
        rw [hprevious, hcurrent] at hforward
        cases hdirect : block.directSuccessorStep previousIndex with
        | inl retained =>
            simp [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
              hdirect] at hforward
        | inr terminal =>
            simp [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
              hdirect] at hforward
    | inr index => exact ⟨index, rfl⟩
  rw [hprevious, hcurrent] at hne hforward hreverse
  refine ⟨previousIndex, currentIndex, ?_, ?_, ?_⟩
  · intro heq
    exact hne (congrArg Sum.inr heq)
  · cases hdirect : block.directSuccessorStep previousIndex with
    | inl retained =>
        simpa [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
          hdirect] using hforward
    | inr terminal =>
        simp [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
          hdirect] at hforward
  · cases hdirect : block.directSuccessorStep currentIndex with
    | inl retained =>
        simpa [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
          hdirect] using hreverse
    | inr terminal =>
        simp [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
          hdirect] at hreverse

theorem CanonicalStableRawComponentBalancedDirectBlock.HasPostSecondBacktrack.threeTokens_or_directTwoCycle
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    {entrance : Fin block.size} (hback : block.HasPostSecondBacktrack entrance) :
    let sources := finiteEmbeddingBlock block.size block.sourceBlock
    Nonempty (Fin 3 ↪
        ↑(canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨
      ∃ previous current : Fin block.size, previous ≠ current ∧
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (block.sourceBlock previous) = Sum.inl (block.directs current) ∧
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (block.sourceBlock current) = Sum.inl (block.directs previous) := by
  classical
  dsimp only
  obtain ⟨previous, current, hne, _hforward, _hreverse⟩ :=
    hback.exists_directIndexTwoCycle
  let sources := finiteEmbeddingBlock block.size block.sourceBlock
  let previousState : ↑sources := ⟨block.sourceBlock previous,
    Finset.mem_map.mpr ⟨previous, Finset.mem_univ _, rfl⟩⟩
  let currentState : ↑sources := ⟨block.sourceBlock current,
    Finset.mem_map.mpr ⟨current, Finset.mem_univ _, rfl⟩⟩
  rcases canonicalStableRawComponent_directPair_threeTokens_or_twoCycle
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
        previousState currentState (block.directs previous) (block.directs current)
        (fun heq => hne (block.directs.injective heq)) rfl rfl with
    hthree | hcycle
  · exact Or.inl hthree
  · exact Or.inr ⟨previous, current, hne, hcycle.1, hcycle.2⟩


theorem CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.growth_or_self_or_augmented_or_threeTokens_or_cycle_or_terminal_or_rankDrop
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    (hcross : block.HasGeometricCrossing) :
    (∃ extended : CanonicalStableRawComponentBalancedDirectBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        extended.size = block.size + 1) ∨
      Nonempty (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      block.HasAugmentedIncidentBlock ∨
      Nonempty (Fin 3 ↪
        ↑(canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (finiteEmbeddingBlock block.size block.sourceBlock))) ∨
      (∃ previous current : Fin block.size, previous ≠ current ∧
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (block.sourceBlock previous) = Sum.inl (block.directs current) ∧
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (block.sourceBlock current) = Sum.inl (block.directs previous)) ∨
      (∃ entrance, block.HasPostSecondLongCycle entrance) ∨
      Nonempty (CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      ∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
          canonicalStableRawSourceRank ends m j k l zero p u.source <
            canonicalStableRawSourceRank ends m j k l zero p
              source.1.source := by
  rcases hcross.growth_or_self_or_augmented_or_postSecond_or_terminal_or_rankDrop with
    hgrowth | hself | haugmented | ⟨entrance, hbacktrack⟩ |
      hcycle | hterminal | hrank
  · exact Or.inl hgrowth
  · exact Or.inr (Or.inl hself)
  · exact Or.inr (Or.inr (Or.inl haugmented))
  · rcases hbacktrack.threeTokens_or_directTwoCycle with hthree | htwoCycle
    · exact Or.inr (Or.inr (Or.inr (Or.inl hthree)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl htwoCycle))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hcycle)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hterminal))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hrank))))))







theorem
    CanonicalStableRawTightChargeOrbit.HasBalancedResidualDeficit.smallerRecursion_or_finiteCycleDischarge
    {I : Type uI} {W : Type uW} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W]
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (hresidual : orbit.HasBalancedResidualDeficit)
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ block : CanonicalStableRawComponentBalancedDirectBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      (block.IsClosed ∧
        ∃ problem : FiniteRelationMinimalTightProblem.{uI, uI},
          problem.rank < Fintype.card (CanonicalStableRawComponentState
            ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
          ∀ source : block.StateComplement,
            ∀ token : CanonicalStableRawComponentToken
                ends m j k l zero hloop hjk hkl hk0 p hno component,
              CanonicalStableRawComponentIncident
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    source.1 token ->
                token ∉ finiteEmbeddingBlock block.size block.tokenBlock) ∨
      (∃ extended : CanonicalStableRawComponentBalancedDirectBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        extended.size = block.size + 1) ∨
      Nonempty (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      block.HasAugmentedIncidentBlock ∨
      Nonempty (Fin 3 ↪
        ↑(canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (finiteEmbeddingBlock block.size block.sourceBlock))) ∨
      (∃ previous current : Fin block.size, previous ≠ current ∧
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (block.sourceBlock previous) = Sum.inl (block.directs current) ∧
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (block.sourceBlock current) = Sum.inl (block.directs previous)) ∨
      (∃ entrance, block.HasPostSecondLongCycle entrance) ∨
      Nonempty (CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      ∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
          canonicalStableRawSourceRank ends m j k l zero p u.source <
            canonicalStableRawSourceRank ends m j k l zero p
              source.1.source := by
  obtain ⟨block, hclosed | ⟨hcross, _continuation⟩⟩ :=
    hresidual.smallerRecursion_or_crossingContinuation hdeficit
  · exact ⟨block, Or.inl hclosed⟩
  · exact ⟨block, Or.inr
      hcross.growth_or_self_or_augmented_or_threeTokens_or_cycle_or_terminal_or_rankDrop⟩


end StatMech.GrahamGHS.FourColor
