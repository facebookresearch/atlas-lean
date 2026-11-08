/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Computable reduction of encoded context-free grammars
-/
module

public import CSLibExt.Computability.Decidability.ContextFree
public import CSLibExt.Computability.Languages.ContextFree.Reduced

/-!
# Computable reduction of encoded context-free grammars

`Reduced.lean` removes empty and unit productions (`epsGrammar`, `unitGrammar`) with classical
choices. For encoded grammars (`Cslib.Language.EncodedCFG`) this file computes the same
productions with primitive recursive functions.

* `EncodedCFG.nullable`: the nullable nonterminals, found as the generating nonterminals
  (`EncodedCFG.generating`) of the productions without terminals;
  `EncodedCFG.mem_nullable_iff`.
* `EncodedCFG.deletions`, `EncodedCFG.epsElim`: delete nullable nonterminals from right-hand
  sides and drop empty ones; `EncodedCFG.mem_epsElim_rules`: the productions are those of
  `epsGrammar`.
* `EncodedCFG.unitReach`, `EncodedCFG.unitElim`: copy non-unit productions along chains of unit
  productions; `EncodedCFG.mem_unitElim_rules`: the productions are those of `unitGrammar`.
* `EncodedCFG.reduce`: both steps. `EncodedCFG.language_reduce`: it generates the original
  language minus the empty word; `EncodedCFG.isReduced_reduce`: no production is empty or a
  unit; `EncodedCFG.primrec_reduce`: it is primitive recursive.
-/

@[expose] public section

namespace Cslib.Language

variable {T : Type*}

/-- A yield of the empty word uses no terminal. -/
theorem Yields.terminal_not_mem {G : ContextFreeGrammar T} {α : List (Symbol T G.NT)}
    (h : Yields G α []) {a : T} : Symbol.terminal a ∉ α := by
  generalize hw : ([] : List T) = w at h
  induction h with
  | nil => simp
  | terminal b _ _ => simp at hw
  | nonterminal _ _ _ _ ihrest =>
      have := (List.append_eq_nil_iff.1 hw.symm).2
      simpa using ihrest this.symm

namespace EncodedCFG

open Cslib.Decidability

/-! ## Nullable nonterminals -/

/-- The productions without terminals. -/
def noTerminals (g : EncodedCFG T) : EncodedCFG T :=
  ⟨g.start, g.rules.filter fun e => e.2.all Sum.isLeft⟩

/-- The nullable nonterminals: the generating nonterminals of the productions without
terminals. -/
def nullable (g : EncodedCFG T) : List ℕ :=
  g.noTerminals.generating

variable [DecidableEq T]

theorem mem_noTerminals_rules {g : EncodedCFG T} {r : ContextFreeRule T ℕ} :
    r ∈ g.noTerminals.toCFG.rules ↔ r ∈ g.toCFG.rules ∧ ∀ a, Symbol.terminal a ∉ r.output := by
  rw [mem_toCFG_rules, mem_toCFG_rules]
  simp only [noTerminals, List.mem_filter, List.all_eq_true]
  constructor
  · rintro ⟨e, ⟨he, hall⟩, rfl⟩
    refine ⟨⟨e, he, rfl⟩, fun a ha => ?_⟩
    obtain ⟨s, hs, hsa⟩ := List.mem_map.1 ha
    cases s with
    | inl i => simp [decodeSymbol] at hsa
    | inr b => simpa using hall _ hs
  · rintro ⟨⟨e, he, rfl⟩, hno⟩
    refine ⟨e, ⟨he, fun s hs => ?_⟩, rfl⟩
    cases s with
    | inl i => rfl
    | inr b => exact absurd (List.mem_map.2 ⟨_, hs, rfl⟩) (hno b)

/-- A yield of the empty word uses only productions without terminals. -/
theorem yields_noTerminals {g : EncodedCFG T} {α : List (Symbol T g.toCFG.NT)}
    (h : Yields g.toCFG α []) : Yields g.noTerminals.toCFG α [] := by
  generalize hw : ([] : List T) = w at h
  induction h with
  | nil => exact Yields.nil
  | terminal b _ _ => simp at hw
  | @nonterminal r hr u w₁ w₂ hout hrest ihout ihrest =>
      obtain ⟨h₁, h₂⟩ := List.append_eq_nil_iff.1 hw.symm
      subst h₁ h₂
      have hr' : r ∈ g.noTerminals.toCFG.rules :=
        mem_noTerminals_rules.2 ⟨hr, fun a => hout.terminal_not_mem⟩
      exact Yields.nonterminal hr' (ihout rfl) (ihrest rfl)

/-- In a grammar without terminals in its productions, only the empty word is yielded. -/
theorem eq_nil_of_yields_noTerminals {g : EncodedCFG T} {α : List (Symbol T g.noTerminals.toCFG.NT)}
    {w : List T}
    (h : Yields g.noTerminals.toCFG α w) (hα : ∀ a, Symbol.terminal a ∉ α) : w = [] := by
  induction h with
  | nil => rfl
  | terminal b _ _ => exact absurd List.mem_cons_self (hα b)
  | nonterminal hr _ _ ihout ihrest =>
      rw [ihout (mem_noTerminals_rules.1 hr).2,
        ihrest fun a ha => hα a (List.mem_cons_of_mem _ ha), List.append_nil]

/-- Yields in the grammar of productions without terminals are yields of the grammar. -/
theorem yields_of_yields_noTerminals {g : EncodedCFG T}
    {α : List (Symbol T g.noTerminals.toCFG.NT)} {w : List T}
    (h : Yields g.noTerminals.toCFG α w) : Yields g.toCFG α w := by
  induction h with
  | nil => exact Yields.nil
  | terminal b _ ih => exact Yields.terminal b ih
  | nonterminal hr _ _ ihout ihrest =>
      exact Yields.nonterminal (mem_noTerminals_rules.1 hr).1 ihout ihrest

/-- **The nullable nonterminals are computed.** -/
theorem mem_nullable_iff {g : EncodedCFG T} {A : ℕ} : A ∈ g.nullable ↔ Nullable g.toCFG A := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ := exists_derives_of_mem_generating h
    have hy := yields_of_derives hw
    have hw0 : w = [] := eq_nil_of_yields_noTerminals hy (by simp)
    subst hw0
    exact nullable_of_yields (yields_of_yields_noTerminals hy)
  · intro h
    have hy := yields_noTerminals (yields_of_nullable h)
    have hd : g.noTerminals.toCFG.Derives [Symbol.nonterminal A] [] := derives_of_yields hy
    have hmem : [] ∈ (⟨A, g.noTerminals.rules⟩ : EncodedCFG T).language := hd
    exact start_mem_generating_of_mem_language hmem

/-! ## Removing empty productions -/

omit [DecidableEq T] in
/-- The right-hand sides obtained from `u` by deleting some occurrences of nonterminals in
`N`. -/
def deletions (N : List ℕ) (u : List (ℕ ⊕ T)) : List (List (ℕ ⊕ T)) :=
  u.foldr (fun s acc => acc.map (s :: ·) ++
    cond (Sum.elim (Decidability.memB N) (fun _ => false) s) acc []) [[]]

omit [DecidableEq T] in
theorem mem_deletions_nil {N : List ℕ} {v : List (ℕ ⊕ T)} :
    v ∈ deletions N [] ↔ v = [] := by
  simp [deletions]

omit [DecidableEq T] in
theorem mem_deletions_cons {N : List ℕ} {s : ℕ ⊕ T} {u v : List (ℕ ⊕ T)} :
    v ∈ deletions N (s :: u) ↔ (∃ v' ∈ deletions N u, s :: v' = v) ∨
      (Sum.elim (Decidability.memB N) (fun _ => false) s = true ∧ v ∈ deletions N u) := by
  change v ∈ (deletions N u).map (s :: ·) ++
    cond (Sum.elim (Decidability.memB N) (fun _ => false) s) (deletions N u) [] ↔ _
  rw [List.mem_append, List.mem_map]
  cases Sum.elim (Decidability.memB N) (fun _ => false) s <;> simp

/-- The deletions of nullable nonterminals are those of `nullableDeletions`. -/
theorem mem_nullableDeletions_iff {g : EncodedCFG T} :
    ∀ (u : List (ℕ ⊕ T)) (α : List (Symbol T ℕ)),
      α ∈ nullableDeletions g.toCFG (u.map decodeSymbol) ↔
        ∃ v ∈ deletions g.nullable u, v.map decodeSymbol = α
  | [], α => by
      simp only [List.map_nil, nullableDeletions, Finset.mem_singleton, mem_deletions_nil]
      constructor
      · rintro rfl
        exact ⟨[], rfl, rfl⟩
      · rintro ⟨v, rfl, rfl⟩
        rfl
  | s :: u, α => by
      have ih := mem_nullableDeletions_iff (g := g) u
      cases s with
      | inr a =>
          simp only [List.map_cons, decodeSymbol, nullableDeletions, Finset.mem_image, ih,
            mem_deletions_cons, Sum.elim_inr, Bool.false_eq_true, false_and, or_false]
          constructor
          · rintro ⟨β, ⟨v, hv, rfl⟩, rfl⟩
            exact ⟨Sum.inr a :: v, ⟨v, hv, rfl⟩, rfl⟩
          · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
            exact ⟨v.map decodeSymbol, ⟨v, hv, rfl⟩, rfl⟩
      | inl i =>
          have hm : Decidability.memB g.nullable i = true ↔ Nullable g.toCFG i :=
            Decidability.memB_iff.trans mem_nullable_iff
          simp only [List.map_cons, decodeSymbol, nullableDeletions, Finset.mem_union,
            Finset.mem_image, ih, mem_deletions_cons, Sum.elim_inl, hm]
          constructor
          · rintro (⟨β, ⟨v, hv, rfl⟩, rfl⟩ | h)
            · exact ⟨Sum.inl i :: v, Or.inl ⟨v, hv, rfl⟩, rfl⟩
            · by_cases hN : Nullable g.toCFG i
              · simp only [hN, ↓reduceIte, ih] at h
                obtain ⟨v, hv, rfl⟩ := h
                exact ⟨v, Or.inr ⟨hN, hv⟩, rfl⟩
              · simp only [hN, ↓reduceIte, Finset.notMem_empty] at h
          · rintro ⟨_, ⟨v, hv, rfl⟩ | ⟨hN, hv⟩, rfl⟩
            · exact Or.inl ⟨v.map decodeSymbol, ⟨v, hv, rfl⟩, rfl⟩
            · refine Or.inr ?_
              simp only [hN, ↓reduceIte, ih]
              exact ⟨_, hv, rfl⟩

omit [DecidableEq T] in
/-- Remove empty productions: from each production, all productions obtained by deleting
nullable nonterminals, except empty ones. -/
def epsElim (g : EncodedCFG T) : EncodedCFG T :=
  let N := g.nullable
  ⟨g.start, g.rules.flatMap fun e =>
    ((deletions N e.2).filter fun v => decide (0 < v.length)).map (e.1, ·)⟩

/-- The productions of `epsElim` are those of `epsGrammar`. -/
theorem mem_epsElim_rules {g : EncodedCFG T} {r : ContextFreeRule T ℕ} :
    r ∈ g.epsElim.toCFG.rules ↔ r ∈ (epsGrammar g.toCFG).rules := by
  rw [mem_toCFG_rules]
  simp only [epsElim, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq,
    List.length_pos_iff]
  constructor
  · rintro ⟨_, ⟨e, he, v, ⟨hv, hne⟩, rfl⟩, rfl⟩
    refine mem_epsGrammar_rules (A := e.1) (u := e.2.map decodeSymbol)
      (mem_toCFG_rules.2 ⟨e, he, rfl⟩) ((mem_nullableDeletions_iff _ _).2 ⟨v, hv, rfl⟩) ?_
    simpa using hne
  · intro hr
    obtain ⟨r₀, hr₀, hin, hdel, hne⟩ := cases_of_mem_epsGrammar_rules hr
    obtain ⟨e, he, rfl⟩ := mem_toCFG_rules.1 hr₀
    obtain ⟨v, hv, hvα⟩ := (mem_nullableDeletions_iff _ _).1 hdel
    refine ⟨(e.1, v), ⟨e, he, v, ⟨hv, ?_⟩, rfl⟩, ?_⟩
    · rintro rfl
      exact hne (by simpa using hvα.symm)
    · obtain ⟨A, α⟩ := r
      simp only [decodeRule] at hin hvα ⊢
      rw [hin, hvα]


/-- **`epsElim` computes `epsGrammar`.** -/
theorem epsElim_toCFG (g : EncodedCFG T) : g.epsElim.toCFG = epsGrammar g.toCFG := by
  have h : g.epsElim.toCFG = ⟨ℕ, g.start, (g.epsElim.rules.map decodeRule).toFinset⟩ := rfl
  rw [h]
  unfold epsGrammar
  congr 1
  ext r
  exact mem_epsElim_rules

/-- `epsElim` generates the language minus the empty word. -/
theorem language_epsElim (g : EncodedCFG T) :
    g.epsElim.language = {w | w ∈ g.language ∧ w ≠ []} := by
  ext w
  change w ∈ g.epsElim.toCFG.language ↔ _
  rw [epsElim_toCFG, epsGrammar_language]
  rfl

/-! ## Removing unit productions -/

omit [DecidableEq T] in
/-- The nonterminals mentioned, without repetitions: the start, and the left-hand sides and
right-hand-side nonterminals of the productions. -/
def ntList (g : EncodedCFG T) : List ℕ :=
  dedupB (g.start :: g.rules.flatMap fun e => e.1 :: e.2.filterMap Sum.getLeft?)

theorem mem_ntList_iff {g : EncodedCFG T} {A : ℕ} : A ∈ g.ntList ↔ A ∈ grammarNTs g.toCFG := by
  simp only [ntList, mem_dedupB, grammarNTs, List.mem_cons, List.mem_flatMap, List.mem_filterMap,
    Finset.mem_insert, Finset.mem_biUnion, mem_formNTs]
  constructor
  · rintro (rfl | ⟨e, he, rfl | ⟨s, hs, hsA⟩⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨decodeRule e, mem_toCFG_rules.2 ⟨e, he, rfl⟩, Or.inl rfl⟩
    · refine Or.inr ⟨decodeRule e, mem_toCFG_rules.2 ⟨e, he, rfl⟩, Or.inr ?_⟩
      cases s with
      | inl i =>
          obtain rfl : i = A := by simpa using hsA
          exact List.mem_map.2 ⟨_, hs, rfl⟩
      | inr a => simp at hsA
  · rintro (rfl | ⟨r, hr, h | h⟩)
    · exact Or.inl rfl
    · obtain ⟨e, he, rfl⟩ := mem_toCFG_rules.1 hr
      exact Or.inr ⟨e, he, Or.inl h⟩
    · obtain ⟨e, he, rfl⟩ := mem_toCFG_rules.1 hr
      obtain ⟨s, hs, hsA⟩ := List.mem_map.1 h
      cases s with
      | inl i =>
          obtain rfl : i = A := by simpa [decodeSymbol] using hsA
          exact Or.inr ⟨e, he, Or.inr ⟨_, hs, rfl⟩⟩
      | inr a => simp [decodeSymbol] at hsA

omit [DecidableEq T] in
/-- The nonterminal of a unit right-hand side. -/
def unitTarget (u : List (ℕ ⊕ T)) : Option ℕ :=
  cond (decide (u.length = 1)) (u.head?.bind Sum.getLeft?) none

omit [DecidableEq T] in
theorem unitTarget_eq_some {u : List (ℕ ⊕ T)} {B : ℕ} :
    unitTarget u = some B ↔ u = [Sum.inl B] := by
  match u with
  | [] => simp [unitTarget]
  | [s] => cases s <;> simp [unitTarget]
  | _ :: _ :: _ => simp [unitTarget]

omit [DecidableEq T] in
theorem isUnitOutput_iff {u : List (ℕ ⊕ T)} :
    IsUnitOutput (u.map decodeSymbol) ↔ (unitTarget u).isSome = true := by
  rw [Option.isSome_iff_exists]
  simp only [IsUnitOutput, unitTarget_eq_some]
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    have hid : encodeSymbol ∘ decodeSymbol = (id : ℕ ⊕ T → ℕ ⊕ T) :=
      funext encodeSymbol_decodeSymbol
    have h2 : u.map (encodeSymbol ∘ decodeSymbol) = [Sum.inl B] := by
      rw [← List.map_map, hB]
      rfl
    rwa [hid, List.map_id] at h2
  · rintro ⟨B, rfl⟩
    exact ⟨B, rfl⟩

omit [DecidableEq T] in
/-- One round of unit reachability from `A`: `A`, and the right-hand sides of unit productions
from nonterminals found so far. -/
def unitStep (g : EncodedCFG T) (A : ℕ) (S : List ℕ) : List ℕ :=
  A :: g.rules.filterMap fun e => cond (Decidability.memB S e.1) (unitTarget e.2) none

omit [DecidableEq T] in
theorem mem_unitStep {g : EncodedCFG T} {A B : ℕ} {S : List ℕ} :
    B ∈ g.unitStep A S ↔ B = A ∨ ∃ e ∈ g.rules, e.1 ∈ S ∧ e.2 = [Sum.inl B] := by
  simp only [unitStep, List.mem_cons, List.mem_filterMap]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨e, he, h⟩
    cases hm : Decidability.memB S e.1
    · simp [hm] at h
    · simp only [hm, Bool.cond_true, unitTarget_eq_some] at h
      exact ⟨e, he, Decidability.memB_iff.1 hm, h⟩
  · rintro ⟨e, he, hS, h⟩
    exact ⟨e, he, by simp [Decidability.memB_iff.2 hS, unitTarget_eq_some.2 h]⟩

omit [DecidableEq T] in
theorem unitStep_mono {g : EncodedCFG T} {A : ℕ} {S S' : List ℕ} (h : S ⊆ S') :
    g.unitStep A S ⊆ g.unitStep A S' := by
  intro B hB
  rcases mem_unitStep.1 hB with rfl | ⟨e, he, hS, h2⟩
  · exact mem_unitStep.2 (Or.inl rfl)
  · exact mem_unitStep.2 (Or.inr ⟨e, he, h hS, h2⟩)

omit [DecidableEq T] in
theorem unitStep_subset {g : EncodedCFG T} {A : ℕ} (S : List ℕ) :
    g.unitStep A S ⊆ A :: g.ntList := by
  intro B hB
  rcases mem_unitStep.1 hB with rfl | ⟨e, he, -, h2⟩
  · exact List.mem_cons_self
  · refine List.mem_cons_of_mem _ (mem_dedupB.2 (List.mem_cons_of_mem _
      (List.mem_flatMap.2 ⟨e, he, ?_⟩)))
    rw [h2]
    simp

omit [DecidableEq T] in
/-- The nonterminals reachable from `A` by unit productions. -/
def unitReach (g : EncodedCFG T) (A : ℕ) : List ℕ :=
  (g.unitStep A)^[(A :: g.ntList).length] []

omit [DecidableEq T] in
theorem unitStep_unitReach_subset (g : EncodedCFG T) (A : ℕ) :
    g.unitStep A (g.unitReach A) ⊆ g.unitReach A :=
  Decidability.iterate_closed (fun _ _ => unitStep_mono) (A :: g.ntList) unitStep_subset

omit [DecidableEq T] in
theorem decodeRule_eq_unit {e : ℕ × List (ℕ ⊕ T)} {C B : ℕ}
    (h : decodeRule e = ⟨C, [Symbol.nonterminal B]⟩) : e = (C, [Sum.inl B]) := by
  rw [← encodeRule_decodeRule e, h]
  rfl

/-- **Unit reachability is computed.** -/
theorem mem_unitReach_iff {g : EncodedCFG T} {A B : ℕ} :
    B ∈ g.unitReach A ↔ UnitSteps g.toCFG A B := by
  constructor
  · suffices ∀ k, B ∈ (g.unitStep A)^[k] [] → UnitSteps g.toCFG A B from this _
    intro k
    induction k generalizing B with
    | zero => simp
    | succ k ih =>
        intro hB
        rw [Function.iterate_succ_apply'] at hB
        rcases mem_unitStep.1 hB with rfl | ⟨e, he, hS, h2⟩
        · exact Relation.ReflTransGen.refl
        · refine (ih hS).tail ?_
          exact mem_toCFG_rules.2 ⟨e, he, by
            obtain ⟨C, u⟩ := e
            simp only at h2
            subst h2
            rfl⟩
  · intro h
    induction h with
    | refl => exact unitStep_unitReach_subset g A (mem_unitStep.2 (Or.inl rfl))
    | tail _ hstep ih =>
        obtain ⟨e, he, hdec⟩ := mem_toCFG_rules.1 hstep
        obtain rfl := decodeRule_eq_unit hdec
        exact unitStep_unitReach_subset g A (mem_unitStep.2 (Or.inr ⟨_, he, ih, rfl⟩))

omit [DecidableEq T] in
/-- Remove unit productions: every non-unit production of a nonterminal reachable by unit
productions is copied to each mentioned nonterminal that reaches it. -/
def unitElim (g : EncodedCFG T) : EncodedCFG T :=
  ⟨g.start, g.ntList.flatMap fun A =>
    let R := g.unitReach A
    g.rules.filterMap fun e =>
      cond (Decidability.memB R e.1 && !(unitTarget e.2).isSome) (some (A, e.2)) none⟩

/-- The productions of `unitElim` are those of `unitGrammar`. -/
theorem mem_unitElim_rules {g : EncodedCFG T} {r : ContextFreeRule T ℕ} :
    r ∈ g.unitElim.toCFG.rules ↔ r ∈ (unitGrammar g.toCFG).rules := by
  rw [mem_toCFG_rules]
  simp only [unitElim, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨x, ⟨A, hA, e, he, hx⟩, rfl⟩
    cases hc : (Decidability.memB (g.unitReach A) e.1 && !(unitTarget e.2).isSome)
    · rw [hc] at hx
      exact absurd hx (by simp)
    · rw [hc] at hx
      obtain rfl : (A, e.2) = x := by simpa using hx
      simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isSome_eq_false_iff] at hc
      exact mem_unitGrammar_rules (B := e.1) (r := decodeRule e)
        (mem_unitReach_iff.1 (Decidability.memB_iff.1 hc.1)) (mem_toCFG_rules.2 ⟨e, he, rfl⟩) rfl
        (by
          change ¬ IsUnitOutput (e.2.map decodeSymbol)
          have h2 := hc.2
          rw [isUnitOutput_iff]
          cases h : unitTarget e.2 <;> simp_all)
        (mem_ntList_iff.1 hA)
  · intro hr
    obtain ⟨B, r₀, hr₀, hin, hunit, hsteps, hout⟩ := cases_of_mem_unitGrammar_rules hr
    obtain ⟨e, he, rfl⟩ := mem_toCFG_rules.1 hr₀
    have hA : r.input ∈ grammarNTs g.toCFG :=
      mem_grammarNTs_of_unitSteps hsteps ⟨(decodeRule e).output, by
        rw [← hin]
        exact hr₀⟩
    refine ⟨(r.input, e.2), ⟨r.input, mem_ntList_iff.2 hA, e, he, ?_⟩, ?_⟩
    · have h1 : Decidability.memB (g.unitReach r.input) e.1 = true :=
        Decidability.memB_iff.2 (mem_unitReach_iff.2 (by rw [← hin] at hsteps; exact hsteps))
      have h2 : (unitTarget e.2).isSome = false := by
        cases h : (unitTarget e.2).isSome
        · rfl
        · exact absurd (isUnitOutput_iff.2 h) hunit
      simp [h1, h2]
    · obtain ⟨A, α⟩ := r
      simp only [decodeRule] at hout ⊢
      rw [hout]

/-- **`unitElim` computes `unitGrammar`.** -/
theorem unitElim_toCFG (g : EncodedCFG T) : g.unitElim.toCFG = unitGrammar g.toCFG := by
  have h : g.unitElim.toCFG = ⟨ℕ, g.start, (g.unitElim.rules.map decodeRule).toFinset⟩ := rfl
  rw [h]
  unfold unitGrammar
  congr 1
  ext r
  exact mem_unitElim_rules

/-! ## Reduction -/

omit [DecidableEq T] in
/-- Remove empty productions, then unit productions. -/
def reduce (g : EncodedCFG T) : EncodedCFG T :=
  g.epsElim.unitElim

/-- **The reduced grammar generates the language minus the empty word.** -/
theorem language_reduce (g : EncodedCFG T) :
    g.reduce.language = {w | w ∈ g.language ∧ w ≠ []} := by
  ext w
  change w ∈ g.epsElim.unitElim.toCFG.language ↔ _
  rw [unitElim_toCFG, unitGrammar_language]
  change w ∈ g.epsElim.language ↔ _
  rw [language_epsElim]

/-- **The reduced grammar has no empty and no unit productions.** -/
theorem isReduced_reduce (g : EncodedCFG T) : IsReduced g.reduce.toCFG := by
  change IsReduced g.epsElim.unitElim.toCFG
  rw [unitElim_toCFG]
  refine ⟨fun r hr => ?_, fun r hr => unitGrammar_not_isUnitOutput (g := g.epsElim.toCFG) hr⟩
  obtain ⟨r₀, hr₀, hout⟩ := unitGrammar_output_of_mem (g := g.epsElim.toCFG) hr
  rw [← hout]
  exact epsGrammar_output_ne_nil (g := g.toCFG) (mem_epsElim_rules.1 hr₀)

end EncodedCFG

/-! ## Primitive recursiveness -/

namespace EncodedCFG

section Primrec

open Cslib.Decidability

variable [Primcodable T]

theorem primrec_isLeft : Primrec (Sum.isLeft : ℕ ⊕ T → Bool) :=
  (Primrec.sumCasesOn Primrec.id (Primrec₂.const true) (Primrec₂.const false)).of_eq fun s => by
    cases s <;> rfl

theorem primrec_getLeft : Primrec (Sum.getLeft? : ℕ ⊕ T → Option ℕ) :=
  (Primrec.sumCasesOn Primrec.id (Primrec.option_some.comp₂ Primrec₂.right)
    (Primrec₂.const none)).of_eq fun s => by cases s <;> rfl

theorem primrec_noTerminals : Primrec (noTerminals (T := T)) :=
  primrec₂_mk.comp primrec_start
    (primrec_list_filter
      (primrec_list_all (primrec_isLeft.comp₂ Primrec₂.right)
        (Primrec.snd.comp Primrec.snd)).to₂ primrec_rules)

theorem primrec_nullable : Primrec (nullable (T := T)) :=
  primrec_generating.comp primrec_noTerminals

theorem primrec_deletions : Primrec₂ (deletions (T := T)) := by
  have hc : Primrec fun x : (List ℕ × List (ℕ ⊕ T)) × ((ℕ ⊕ T) × List (List (ℕ ⊕ T))) =>
      Sum.elim (Decidability.memB x.1.1) (fun _ => false) x.2.1 :=
    (Primrec.sumCasesOn (Primrec.fst.comp Primrec.snd)
      (Decidability.primrec_memB.comp₂ (Primrec.fst.comp₂ (Primrec.fst.comp₂ Primrec₂.left))
        Primrec₂.right)
      (Primrec₂.const false)).of_eq fun x => by cases x.2.1 <;> rfl
  have hh : Primrec fun x : (List ℕ × List (ℕ ⊕ T)) × ((ℕ ⊕ T) × List (List (ℕ ⊕ T))) =>
      x.2.2.map (x.2.1 :: ·) ++
        cond (Sum.elim (Decidability.memB x.1.1) (fun _ => false) x.2.1) x.2.2 [] :=
    Primrec.list_append.comp
      (Primrec.list_map (Primrec.snd.comp Primrec.snd)
        (Primrec.list_cons.comp₂ (Primrec.fst.comp₂ (Primrec.snd.comp₂ Primrec₂.left))
          Primrec₂.right))
      (Primrec.cond hc (Primrec.snd.comp Primrec.snd) (Primrec.const []))
  exact (Primrec.list_foldr Primrec.snd (Primrec.const [[]]) hh.to₂).to₂

theorem primrec_epsElim : Primrec (epsElim (T := T)) :=
  primrec₂_mk.comp primrec_start
    (Primrec.list_flatMap primrec_rules
      (Primrec.list_map
        (primrec_list_filter
          (Primrec.nat_lt.comp (Primrec.const 0)
            (Primrec.list_length.comp Primrec.snd)).decide.to₂
          (primrec_deletions.comp (primrec_nullable.comp Primrec.fst)
            (Primrec.snd.comp Primrec.snd)))
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd).to₂).to₂)

theorem primrec_ntList : Primrec (ntList (T := T)) :=
  primrec_dedupB.comp <| Primrec.list_cons.comp primrec_start
    (Primrec.list_flatMap primrec_rules
      (Primrec.list_cons.comp₂ (Primrec.fst.comp₂ Primrec₂.right)
        (Primrec.listFilterMap (Primrec.snd.comp Primrec.snd)
          (primrec_getLeft.comp₂ Primrec₂.right)).to₂))

theorem primrec_unitTarget : Primrec (unitTarget (T := T)) :=
  Primrec.cond (Primrec.eq.comp Primrec.list_length (Primrec.const 1)).decide
    (Primrec.option_bind Primrec.list_head? (primrec_getLeft.comp₂ Primrec₂.right))
    (Primrec.const none)

theorem primrec_unitStep :
    Primrec fun p : EncodedCFG T × ℕ × List ℕ => p.1.unitStep p.2.1 p.2.2 :=
  Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
    (Primrec.listFilterMap (primrec_rules.comp Primrec.fst)
      (Primrec.cond
        (Decidability.primrec_memB.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.fst.comp Primrec.snd))
        (primrec_unitTarget.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const none)).to₂)

theorem primrec_unitReach : Primrec₂ (unitReach (T := T)) :=
  (Primrec.nat_iterate
    (Primrec.list_length.comp
      (Primrec.list_cons.comp Primrec.snd (primrec_ntList.comp Primrec.fst)))
    (Primrec.const [])
    (primrec_unitStep.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))).to₂).to₂

theorem primrec_unitElim : Primrec (unitElim (T := T)) :=
  primrec₂_mk.comp primrec_start
    (Primrec.list_flatMap primrec_ntList
      (Primrec.listFilterMap (primrec_rules.comp Primrec.fst)
        (Primrec.cond
          (Primrec.and.comp
            (Decidability.primrec_memB.comp
              (primrec_unitReach.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))
              (Primrec.fst.comp Primrec.snd))
            (Primrec.not.comp (Primrec.option_isSome.comp
              (primrec_unitTarget.comp (Primrec.snd.comp Primrec.snd)))))
          (Primrec.option_some.comp
            (Primrec.pair (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)))
          (Primrec.const none)).to₂).to₂)

/-- **Reduction is primitive recursive.** -/
theorem primrec_reduce : Primrec (reduce (T := T)) :=
  primrec_unitElim.comp primrec_epsElim

end Primrec

end EncodedCFG

end Cslib.Language
