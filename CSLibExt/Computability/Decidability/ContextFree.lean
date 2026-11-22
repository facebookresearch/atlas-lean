/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Emptiness of context-free grammars
-/
module

public import CSLibExt.Computability.Decidability.Basic
public import CSLibExt.Computability.Decidability.PrimrecList
public import CSLibExt.Computability.Languages.ContextFree.Encoded
public import CSLibExt.Computability.Languages.ContextFree.Ogden
public import CSLibExt.Computability.Languages.ContextFree.Yields
public import Mathlib.Computability.RE

/-!
# Emptiness of context-free grammars is computable

For an encoded grammar (`Cslib.Language.EncodedCFG`), `EncodedCFG.generating` computes the
nonterminals that derive some terminal word: start from none and repeatedly add the left-hand
side of every production whose right-hand side mentions only nonterminals found so far, as many
rounds as there are productions. `EncodedCFG.isEmptyB` tests whether the start nonterminal is
missing (Sipser, *Introduction to the Theory of Computation*, 3rd ed., Theorem 4.8, E_CFG).

* `EncodedCFG.exists_derives_of_mem_generating`: every nonterminal found derives a terminal word.
* `EncodedCFG.start_mem_generating_of_mem_language`: if the grammar generates some word, the
  start nonterminal is found. The proof assigns `⊤` to the nonterminals found and `0` to the
  others and checks that this is a valuation (`Cslib.Language.IsValuation`), because the set
  found is closed under the round.
* `EncodedCFG.isEmptyB_iff`: `isEmptyB g = true ↔ g.language = 0`.
* `EncodedCFG.primrec_isEmptyB` and `EncodedCFG.computablePred_language_eq_zero`: the test is
  primitive recursive, so emptiness of encoded context-free grammars is a computable predicate,
  and `EncodedCFG.tm2Decidable_language_eq_zero`: it is decidable by a multi-stack machine.

Membership (Sipser, Theorem 4.7, A_CFG) is decided for arbitrary encoded grammars, without a
normal form, by a fixed point over items `(A, i, j)`: `A` yields the factor of `w` from position
`i` to position `j` (`EncodedCFG.factor`).

* `EncodedCFG.starts`: the positions from which a right-hand side yields the factor ending at
  `j`, given the items found so far; `EncodedCFG.memStep`: one round; `EncodedCFG.found`: the
  items after as many rounds as there are candidate items, a fixed point by `iterate_closed`.
* `EncodedCFG.found_sound`: every item found is yielded (built with `Yields`);
  `EncodedCFG.mem_starts_of_yields`: every yield is found, by induction on `Yields`.
* `EncodedCFG.memLanguageB_iff`: `memLanguageB g w = true ↔ w ∈ g.language`;
  `EncodedCFG.primrec_memLanguageB` and `EncodedCFG.tm2Decidable_mem_language`.

Infiniteness (INFINITE_CFG) is decided by trying the words over the grammar's terminals whose
length is between the pumping bound `N` and `2N`.

* `EncodedCFG.pumpBound`: `N = lenBound ^ (K + 1)` for `K` the number of distinct left-hand
  sides, a computable bound for
  which Ogden's lemma with every letter marked gives the pumping lemma
  (`EncodedCFG.pumping_pumpBound`, from `pumping_of_bound` in `Ogden.lean`).
* `EncodedCFG.infinite_of_mem_of_le`: a generated word of length at least `N` pumps up;
  `EncodedCFG.exists_mem_le_lt`: pumping down reaches a length in `[N, 2N)`.
* `EncodedCFG.infiniteB_iff`: `infiniteB g = true ↔ g.language.Infinite`;
  `EncodedCFG.primrec_infiniteB` and `EncodedCFG.tm2Decidable_language_infinite`.

The list helpers (`memB`, `iterate_closed`, primitive recursiveness of `List.all`, `List.any`
and `List.filter`, `computablePred_of_primrec_bool`) are in `Decidability/PrimrecList.lean`;
their former names in this namespace (`EncodedCFG.memB`, `memB_iff`, `iterate_closed`,
`primrec_memB`) remain as deprecated aliases.
-/

@[expose] public section

namespace Cslib.Language.EncodedCFG

open Cslib.Decidability

variable {T : Type*}

/-! ## The procedure -/

/-- A symbol is acceptable when it is a terminal or a nonterminal in `G`. -/
def symOk (G : List ℕ) (s : ℕ ⊕ T) : Bool :=
  Sum.elim (memB G) (fun _ => true) s

/-- A production is acceptable when all symbols of its right-hand side are. -/
def ruleOk (G : List ℕ) (e : ℕ × List (ℕ ⊕ T)) : Bool :=
  e.2.foldr (fun s b => symOk G s && b) true

theorem ruleOk_iff {G : List ℕ} {e : ℕ × List (ℕ ⊕ T)} :
    ruleOk G e = true ↔ ∀ j, Sum.inl j ∈ e.2 → j ∈ G := by
  obtain ⟨A, rhs⟩ := e
  simp only [ruleOk]
  induction rhs with
  | nil => simp
  | cons s rhs ih =>
      simp only [List.foldr_cons, Bool.and_eq_true, ih, List.mem_cons]
      cases s with
      | inl i =>
          simp only [symOk, Sum.elim_inl, memB_iff, Sum.inl.injEq]
          constructor
          · rintro ⟨hi, h⟩ j (rfl | hj)
            · exact hi
            · exact h j hj
          · intro h
            exact ⟨h i (Or.inl rfl), fun j hj => h j (Or.inr hj)⟩
      | inr a =>
          simp [symOk]

/-- One round: the left-hand sides of the acceptable productions. -/
def genStep (rules : List (ℕ × List (ℕ ⊕ T))) (G : List ℕ) : List ℕ :=
  rules.filterMap fun e => cond (ruleOk G e) (some e.1) none

theorem mem_genStep {rules : List (ℕ × List (ℕ ⊕ T))} {G : List ℕ} {j : ℕ} :
    j ∈ genStep rules G ↔ ∃ e ∈ rules, e.1 = j ∧ ∀ i, Sum.inl i ∈ e.2 → i ∈ G := by
  simp only [genStep, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, h⟩
    cases hok : ruleOk G e
    · simp [hok] at h
    · simp only [hok, Bool.cond_true, Option.some.injEq] at h
      exact ⟨e, he, h, ruleOk_iff.1 hok⟩
  · rintro ⟨e, he, rfl, h⟩
    exact ⟨e, he, by simp [ruleOk_iff.2 h]⟩

theorem genStep_mono {rules : List (ℕ × List (ℕ ⊕ T))} {G G' : List ℕ} (h : G ⊆ G') :
    genStep rules G ⊆ genStep rules G' := by
  intro j hj
  obtain ⟨e, he, rfl, hall⟩ := mem_genStep.1 hj
  exact mem_genStep.2 ⟨e, he, rfl, fun i hi => h (hall i hi)⟩

theorem genStep_subset {rules : List (ℕ × List (ℕ ⊕ T))} (G : List ℕ) :
    genStep rules G ⊆ rules.map Prod.fst := by
  intro j hj
  obtain ⟨e, he, rfl, -⟩ := mem_genStep.1 hj
  exact List.mem_map_of_mem he

/-- The nonterminals that derive a terminal word. -/
def generating (g : EncodedCFG T) : List ℕ :=
  (genStep g.rules)^[g.rules.length] []

/-- **The emptiness test**: the start nonterminal derives no terminal word. -/
def isEmptyB (g : EncodedCFG T) : Bool :=
  !memB g.generating g.start

/-! ## Stabilization -/

theorem genStep_generating_subset (g : EncodedCFG T) :
    genStep g.rules g.generating ⊆ g.generating := by
  have h := iterate_closed (f := genStep g.rules) (fun _ _ => genStep_mono)
    (g.rules.map Prod.fst) genStep_subset
  rwa [List.length_map] at h

/-! ## Computability -/

section Primrec

variable [Primcodable T]

theorem primrec_ruleOk : Primrec₂ (ruleOk (T := T)) :=
  Primrec.list_foldr (Primrec.snd.comp Primrec.snd) (Primrec.const true)
    (Primrec.and.comp₂
      (Primrec.sumCasesOn (Primrec.fst.comp Primrec.snd)
        (primrec_memB.comp₂ (Primrec.fst.comp₂ (Primrec.fst.comp₂ Primrec₂.left)) Primrec₂.right)
        (Primrec.const true |>.comp₂ Primrec₂.left)).to₂
      (Primrec.snd.comp₂ Primrec₂.right))

theorem primrec_genStep : Primrec₂ (genStep (T := T)) :=
  Primrec.listFilterMap Primrec.fst
    (Primrec.cond (primrec_ruleOk.comp₂ (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right)
      (Primrec.option_some.comp₂ (Primrec.fst.comp₂ Primrec₂.right))
      (Primrec.const none |>.comp₂ Primrec₂.left))

theorem primrec_generating : Primrec (generating (T := T)) :=
  Primrec.nat_iterate (Primrec.list_length.comp primrec_rules) (Primrec.const [])
    (primrec_genStep.comp₂ (primrec_rules.comp₂ Primrec₂.left) Primrec₂.right)

theorem primrec_isEmptyB : Primrec (isEmptyB (T := T)) :=
  Primrec.not.comp (primrec_memB.comp primrec_generating primrec_start)

end Primrec

/-! ## Correctness -/

variable [DecidableEq T]

omit [DecidableEq T] in
/-- A sentential form whose nonterminals each derive a terminal word derives a terminal word. -/
theorem exists_derives_of_forall {G : ContextFreeGrammar T} :
    ∀ u : List (Symbol T G.NT),
      (∀ A, Symbol.nonterminal A ∈ u → ∃ w : List T, G.Derives [.nonterminal A] (w.map .terminal))
      → ∃ w : List T, G.Derives u (w.map .terminal)
  | [], _ => ⟨[], .refl _⟩
  | s :: u, h => by
      obtain ⟨w, hw⟩ := exists_derives_of_forall u fun A hA => h A (List.mem_cons_of_mem _ hA)
      cases s with
      | terminal a =>
          exact ⟨a :: w, by
            simpa using derives_append (Relation.ReflTransGen.refl (a := [Symbol.terminal a])) hw⟩
      | nonterminal A =>
          obtain ⟨v, hv⟩ := h A List.mem_cons_self
          exact ⟨v ++ w, by
            simpa [List.map_append] using derives_append hv hw⟩

/-- **Soundness**: every nonterminal found derives a terminal word. -/
theorem exists_derives_of_mem_iterate (g : EncodedCFG T) :
    ∀ (k : ℕ) {j : ℕ}, j ∈ (genStep g.rules)^[k] [] →
      ∃ w : List T, g.toCFG.Derives [.nonterminal j] (w.map .terminal)
  | 0, j, h => absurd h (List.not_mem_nil)
  | k + 1, j, h => by
      rw [Function.iterate_succ_apply'] at h
      obtain ⟨e, he, rfl, hall⟩ := mem_genStep.1 h
      have hrule : decodeRule e ∈ g.toCFG.rules := mem_toCFG_rules.2 ⟨e, he, rfl⟩
      have hstep : g.toCFG.Produces [.nonterminal e.1] (e.2.map decodeSymbol) :=
        ⟨decodeRule e, hrule, ContextFreeRule.Rewrites.input_output⟩
      obtain ⟨w, hw⟩ := exists_derives_of_forall (G := g.toCFG) (e.2.map decodeSymbol)
        fun A hA => by
          obtain ⟨s, hs, hsA⟩ := List.mem_map.1 hA
          cases s with
          | inl i =>
              obtain rfl : i = A := by simpa [decodeSymbol] using hsA
              exact exists_derives_of_mem_iterate g k (hall i hs)
          | inr a => simp [decodeSymbol] at hsA
      exact ⟨w, hstep.trans_derives hw⟩

theorem exists_derives_of_mem_generating {g : EncodedCFG T} {j : ℕ} (h : j ∈ g.generating) :
    ∃ w : List T, g.toCFG.Derives [.nonterminal j] (w.map .terminal) :=
  exists_derives_of_mem_iterate g _ h

omit [DecidableEq T] in
/-- The interpretation of a sentential form with a nonterminal assigned `0` is `0`. -/
theorem evalForm_eq_zero_of_mem {N : Type*} {V : N → Language T} {A : N} (hA : V A = 0) :
    ∀ {u : List (Symbol T N)}, Symbol.nonterminal A ∈ u → evalForm V u = 0
  | s :: u, h => by
      rw [evalForm_cons]
      rcases List.mem_cons.1 h with rfl | h
      · rw [evalSymbol_nonterminal, hA, zero_mul]
      · rw [evalForm_eq_zero_of_mem hA h, mul_zero]

/-- **Completeness**: if the grammar generates a word, its start nonterminal is found. -/
theorem start_mem_generating_of_mem_language {g : EncodedCFG T} {w : List T}
    (hw : w ∈ g.language) : g.start ∈ g.generating := by
  classical
  let V : ℕ → Language T := fun j => if j ∈ g.generating then ⊤ else 0
  have hV : IsValuation g.toCFG V := by
    intro r hr
    obtain ⟨e, he, rfl⟩ := mem_toCFG_rules.1 hr
    by_cases hall : ∀ i, Sum.inl i ∈ e.2 → i ∈ g.generating
    · have hmem : e.1 ∈ g.generating :=
        genStep_generating_subset g (mem_genStep.2 ⟨e, he, rfl, hall⟩)
      change _ ≤ V e.1
      simp only [V, hmem, ↓reduceIte]
      exact le_top
    · push Not at hall
      obtain ⟨i, hi, hni⟩ := hall
      have h0 : evalForm V ((decodeRule e).output) = 0 :=
        evalForm_eq_zero_of_mem (A := i) (by simp [V, hni])
          (List.mem_map.2 ⟨Sum.inl i, hi, rfl⟩)
      rw [h0]
      exact bot_le
  have h := language_le_of_valuation hV hw
  by_contra hns
  change w ∈ V g.start at h
  simp only [V, hns, ↓reduceIte] at h
  exact Language.notMem_zero w h

/-- **Correctness of the emptiness test.** -/
theorem isEmptyB_iff (g : EncodedCFG T) : g.isEmptyB = true ↔ g.language = 0 := by
  simp only [isEmptyB, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, memB_iff]
  constructor
  · intro hns
    ext w
    simp only [Language.notMem_zero, iff_false]
    exact fun hw => hns (start_mem_generating_of_mem_language hw)
  · intro h hs
    obtain ⟨w, hw⟩ := exists_derives_of_mem_generating hs
    have : w ∈ g.language := hw
    rw [h] at this
    exact Language.notMem_zero w this

/-- Emptiness of an encoded grammar's language, decided by `isEmptyB`. -/
instance decidableLanguageEqZero (g : EncodedCFG T) : Decidable (g.language = 0) :=
  decidable_of_iff _ (isEmptyB_iff g)

/-! ## Emptiness is computable -/

section Computable

variable [Primcodable T]

/-- **Emptiness of context-free grammars is computable.** -/
theorem computablePred_language_eq_zero :
    ComputablePred fun g : EncodedCFG T => g.language = 0 :=
  ⟨inferInstance,
    primrec_isEmptyB.to_comp.of_eq fun g => by
      cases h : g.isEmptyB
      · exact (decide_eq_false fun h0 => by simp [(isEmptyB_iff g).2 h0] at h).symm
      · exact (decide_eq_true ((isEmptyB_iff g).1 h)).symm⟩

/-- **Sipser, Theorem 4.8**: emptiness for context-free grammars (E_CFG) is decidable by a
multi-stack machine. -/
theorem tm2Decidable_language_eq_zero :
    Cslib.Decidability.TM2Decidable fun g : EncodedCFG T => g.language = 0 :=
  Cslib.Decidability.tm2Decidable_iff_computablePred.2 computablePred_language_eq_zero

end Computable

end Cslib.Language.EncodedCFG

/-! ## Membership (Sipser, Theorem 4.7) -/

namespace Cslib.Language.EncodedCFG

open Cslib.Decidability

variable {T : Type*}

/-! ## Factors -/

/-- The factor of `w` from position `i` to position `j`. -/
def factor (w : List T) (i j : ℕ) : List T :=
  (w.drop i).take (j - i)

theorem length_factor {w : List T} {i j : ℕ} (hj : j ≤ w.length) :
    (factor w i j).length = j - i := by
  simp [factor]; omega

theorem factor_self (w : List T) (i : ℕ) : factor w i i = [] := by
  simp [factor]

theorem factor_append {w : List T} {i k j : ℕ} (hik : i ≤ k) (hkj : k ≤ j) :
    factor w i k ++ factor w k j = factor w i j := by
  unfold factor
  have : j - i = (k - i) + (j - k) := by omega
  rw [this, List.take_add, List.drop_drop]
  congr 3
  omega

theorem factor_cons {w : List T} {i j : ℕ} (hij : i < j) (hj : j ≤ w.length) :
    factor w i j = w[i] :: factor w (i + 1) j := by
  unfold factor
  rw [List.drop_eq_getElem_cons (by omega)]
  have : j - i = (j - (i + 1)) + 1 := by omega
  rw [this, List.take_succ_cons]

theorem factor_zero_length (w : List T) : factor w 0 w.length = w := by
  simp [factor]

/-- A split of a factor is a pair of adjacent factors. -/
theorem factor_eq_append {w u v : List T} {i j : ℕ} (hij : i ≤ j) (hj : j ≤ w.length)
    (h : factor w i j = u ++ v) :
    i + u.length ≤ j ∧ factor w i (i + u.length) = u ∧ factor w (i + u.length) j = v := by
  have hlen := congrArg List.length h
  rw [length_factor hj, List.length_append] at hlen
  refine ⟨by omega, ?_, ?_⟩
  · have h2 := congrArg (List.take u.length) h
    rw [List.take_left] at h2
    conv_rhs => rw [← h2]
    unfold factor
    rw [List.take_take]
    congr 1
    omega
  · have h2 := congrArg (List.drop u.length) h
    rw [List.drop_left] at h2
    conv_rhs => rw [← h2]
    unfold factor
    rw [List.drop_take, List.drop_drop]
    congr 1
    omega

/-! ## Matching right-hand sides -/

variable [DecidableEq T]

/-- Whether a symbol can start at `i`, given the positions `S` where the rest can start and
the items `R` found so far. -/
def symFits (w : List T) (R : List ℕ) (S : List ℕ) (X : ℕ ⊕ T) (i : ℕ) : Bool :=
  match X with
  | .inr a => memB S (i + 1) && decide (w[i]? = some a)
  | .inl B => S.any fun k => memB R (Nat.pair B (Nat.pair i k))

/-- The positions from which a right-hand side can derive the factor of `w` ending at `j`,
given the items `R` found so far. -/
def starts (w : List T) (R : List ℕ) (j : ℕ) (rhs : List (ℕ ⊕ T)) : List ℕ :=
  rhs.foldr (fun X S => (List.range (w.length + 1)).filter (symFits w R S X)) [j]

/-- One round: the items `(A, i, j)` for productions `A → rhs` and positions `i` from which
`rhs` derives the factor ending at `j`. -/
def memStep (g : EncodedCFG T) (w : List T) (R : List ℕ) : List ℕ :=
  g.rules.flatMap fun e => (List.range (w.length + 1)).flatMap fun j =>
    (starts w R j e.2).map fun i => Nat.pair e.1 (Nat.pair i j)

/-- All items `(A, i, j)` with `A` a left-hand side and `i, j ≤ |w|`. -/
def items (g : EncodedCFG T) (w : List T) : List ℕ :=
  (g.rules.map Prod.fst).flatMap fun A => (List.range (w.length + 1)).flatMap fun j =>
    (List.range (w.length + 1)).map fun i => Nat.pair A (Nat.pair i j)

/-- The items found: the closure of `memStep`. -/
def found (g : EncodedCFG T) (w : List T) : List ℕ :=
  (memStep g w)^[(items g w).length] []

/-- **Membership test** for encoded grammars. -/
def memLanguageB (g : EncodedCFG T) (w : List T) : Bool :=
  memB (found g w) (Nat.pair g.start (Nat.pair 0 w.length))

theorem starts_subset {w : List T} {R : List ℕ} {j : ℕ} (hj : j ≤ w.length)
    (rhs : List (ℕ ⊕ T)) : ∀ i ∈ starts w R j rhs, i ≤ w.length := by
  cases rhs with
  | nil => simp [starts]; omega
  | cons X rhs =>
      intro i hi
      simp only [starts, List.foldr_cons] at hi
      have := (List.mem_filter.1 hi).1
      rw [List.mem_range] at this
      omega

theorem starts_mono {w : List T} {R R' : List ℕ} (h : R ⊆ R') (j : ℕ) :
    ∀ rhs : List (ℕ ⊕ T), starts w R j rhs ⊆ starts w R' j rhs
  | [] => List.Subset.refl _
  | X :: rhs => by
      intro i hi
      simp only [starts, List.foldr_cons] at hi ⊢
      obtain ⟨hr, hfit⟩ := List.mem_filter.1 hi
      refine List.mem_filter.2 ⟨hr, ?_⟩
      have ih := starts_mono (w := w) h j rhs
      change symFits w R (starts w R j rhs) X i = true at hfit
      change symFits w R' (starts w R' j rhs) X i = true
      cases X with
      | inr a =>
          simp only [symFits, Bool.and_eq_true, memB_iff] at hfit ⊢
          exact ⟨ih hfit.1, hfit.2⟩
      | inl B =>
          simp only [symFits, List.any_eq_true, memB_iff] at hfit ⊢
          obtain ⟨k, hk, hR⟩ := hfit
          exact ⟨k, ih hk, h hR⟩

theorem memStep_mono {g : EncodedCFG T} {w : List T} {R R' : List ℕ} (h : R ⊆ R') :
    memStep g w R ⊆ memStep g w R' := by
  intro x hx
  simp only [memStep, List.mem_flatMap, List.mem_map] at hx ⊢
  obtain ⟨e, he, j, hj, i, hi, rfl⟩ := hx
  exact ⟨e, he, j, hj, i, starts_mono h j e.2 hi, rfl⟩

theorem memStep_subset_items {g : EncodedCFG T} {w : List T} (R : List ℕ) :
    memStep g w R ⊆ items g w := by
  intro x hx
  simp only [memStep, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨e, he, j, hj, i, hi, rfl⟩ := hx
  simp only [items, List.mem_flatMap, List.mem_map]
  refine ⟨e.1, ⟨e, he, rfl⟩, j, hj, i, ?_, rfl⟩
  rw [List.mem_range] at hj ⊢
  have := starts_subset (by omega) e.2 i hi
  omega

theorem memStep_found_subset (g : EncodedCFG T) (w : List T) :
    memStep g w (found g w) ⊆ found g w :=
  iterate_closed (fun _ _ => memStep_mono) (items g w) memStep_subset_items

/-! ## Soundness -/

/-- An item is sound when it codes `(A, i, j)` with `i ≤ j ≤ |w|` and `A` yielding the factor. -/
def SoundItem (g : EncodedCFG T) (w : List T) (x : ℕ) : Prop :=
  ∃ A i j, x = Nat.pair A (Nat.pair i j) ∧ i ≤ j ∧ j ≤ w.length ∧
    Yields g.toCFG [.nonterminal A] (factor w i j)

theorem starts_sound {g : EncodedCFG T} {w : List T} {R : List ℕ}
    (hR : ∀ x ∈ R, SoundItem g w x) {j : ℕ} (hj : j ≤ w.length) :
    ∀ (rhs : List (ℕ ⊕ T)) i, i ∈ starts w R j rhs →
      i ≤ j ∧ Yields g.toCFG (rhs.map decodeSymbol) (factor w i j)
  | [], i, hi => by
      simp only [starts, List.foldr_nil, List.mem_singleton] at hi
      subst hi
      exact ⟨le_rfl, by rw [factor_self]; exact Yields.nil⟩
  | X :: rhs, i, hi => by
      simp only [starts, List.foldr_cons] at hi
      obtain ⟨-, hfit⟩ := List.mem_filter.1 hi
      change symFits w R (starts w R j rhs) X i = true at hfit
      cases X with
      | inr a =>
          simp only [symFits, Bool.and_eq_true, memB_iff, decide_eq_true_eq] at hfit
          obtain ⟨hnext, hwi⟩ := hfit
          obtain ⟨hle, hy⟩ := starts_sound hR hj rhs (i + 1) hnext
          have hi : i < w.length := by
            by_contra h
            rw [List.getElem?_eq_none (by omega)] at hwi
            simp at hwi
          have hwa : w[i] = a := by
            rw [List.getElem?_eq_getElem hi] at hwi
            exact Option.some.inj hwi
          refine ⟨by omega, ?_⟩
          rw [factor_cons (by omega) hj, hwa]
          exact Yields.terminal a hy
      | inl B =>
          simp only [symFits, List.any_eq_true, memB_iff] at hfit
          obtain ⟨k, hk, hRk⟩ := hfit
          obtain ⟨hkj, hy⟩ := starts_sound hR hj rhs k hk
          obtain ⟨A, i', k', hcode, hik, -, hyB⟩ := hR _ hRk
          obtain ⟨rfl, rfl, rfl⟩ : B = A ∧ i = i' ∧ k = k' := by
            have h1 := congrArg Nat.unpair hcode
            simp only [Nat.unpair_pair, Prod.mk.injEq] at h1
            obtain ⟨h1, h2⟩ := h1
            have h3 := congrArg Nat.unpair h2
            simp only [Nat.unpair_pair, Prod.mk.injEq] at h3
            exact ⟨h1, h3.1, h3.2⟩
          refine ⟨by omega, ?_⟩
          rw [← factor_append hik hkj]
          exact Yields.append (u := [.nonterminal B]) hyB hy

theorem memStep_sound {g : EncodedCFG T} {w : List T} {R : List ℕ}
    (hR : ∀ x ∈ R, SoundItem g w x) : ∀ x ∈ memStep g w R, SoundItem g w x := by
  intro x hx
  simp only [memStep, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨e, he, j, hj, i, hi, rfl⟩ := hx
  rw [List.mem_range] at hj
  obtain ⟨hij, hy⟩ := starts_sound hR (by omega) e.2 i hi
  refine ⟨e.1, i, j, rfl, hij, by omega, ?_⟩
  exact yields_of_rule (r := decodeRule e) (mem_toCFG_rules.2 ⟨e, he, rfl⟩) hy

theorem found_sound (g : EncodedCFG T) (w : List T) : ∀ x ∈ found g w, SoundItem g w x := by
  unfold found
  generalize (items g w).length = n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact memStep_sound ih

/-! ## Completeness -/

theorem mem_starts_of_yields {g : EncodedCFG T} {w : List T} {β : List (Symbol T g.toCFG.NT)}
    {u : List T} (h : Yields g.toCFG β u) :
    ∀ (rhs : List (ℕ ⊕ T)) (i j : ℕ), β = rhs.map decodeSymbol → u = factor w i j → i ≤ j →
      j ≤ w.length → i ∈ starts w (found g w) j rhs := by
  induction h with
  | nil =>
      intro rhs i j hrhs hu hij hj
      obtain rfl : rhs = [] := List.map_eq_nil_iff.1 hrhs.symm
      have hlen := congrArg List.length hu
      rw [length_factor hj] at hlen
      simp only [List.length_nil] at hlen
      obtain rfl : i = j := by omega
      simp [starts]
  | terminal a h ih =>
      intro rhs i j hrhs hu hij hj
      obtain ⟨X, rest, rfl⟩ : ∃ X rest, rhs = X :: rest := by
        cases rhs with
        | nil => simp at hrhs
        | cons X rest => exact ⟨X, rest, rfl⟩
      simp only [List.map_cons, List.cons.injEq] at hrhs
      obtain ⟨hX, hrest⟩ := hrhs
      obtain rfl : X = .inr a := by
        cases X with
        | inl B => simp [decodeSymbol] at hX
        | inr b => simp only [decodeSymbol, Symbol.terminal.injEq] at hX; rw [hX]
      have hlen := congrArg List.length hu
      rw [length_factor hj] at hlen
      simp only [List.length_cons] at hlen
      have hlt : i < j := by omega
      rw [factor_cons hlt hj, List.cons.injEq] at hu
      obtain ⟨hwa, hu⟩ := hu
      have hnext := ih rest (i + 1) j hrest hu hlt hj
      simp only [starts, List.foldr_cons]
      refine List.mem_filter.2 ⟨List.mem_range.2 (by omega), ?_⟩
      change symFits w _ (starts w _ j rest) (.inr a) i = true
      simp only [symFits, Bool.and_eq_true, memB_iff, decide_eq_true_eq]
      refine ⟨hnext, ?_⟩
      rw [List.getElem?_eq_getElem (by omega), hwa]
  | @nonterminal r hr u w₁ w₂ hout hrest ihout ihrest =>
      intro rhs i j hrhs hu hij hj
      obtain ⟨X, rest, rfl⟩ : ∃ X rest, rhs = X :: rest := by
        cases rhs with
        | nil => simp at hrhs
        | cons X rest => exact ⟨X, rest, rfl⟩
      simp only [List.map_cons, List.cons.injEq] at hrhs
      obtain ⟨hX, hrestEq⟩ := hrhs
      obtain rfl : X = .inl r.input := by
        cases X with
        | inl B => simp only [decodeSymbol, Symbol.nonterminal.injEq] at hX; rw [hX]
        | inr b => simp [decodeSymbol] at hX
      obtain ⟨hk, h₁, h₂⟩ := factor_eq_append hij hj hu.symm
      set k := i + w₁.length
      have hkrest := ihrest rest k j hrestEq h₂.symm hk hj
      obtain ⟨e, he, rfl⟩ := mem_toCFG_rules.1 hr
      have hik : i ≤ k := Nat.le_add_right _ _
      have hstart := ihout e.2 i k rfl h₁.symm hik (by omega)
      have hitem : Nat.pair e.1 (Nat.pair i k) ∈ found g w := by
        apply memStep_found_subset
        simp only [memStep, List.mem_flatMap, List.mem_map]
        exact ⟨e, he, k, List.mem_range.2 (by omega), i, hstart, rfl⟩
      simp only [starts, List.foldr_cons]
      refine List.mem_filter.2 ⟨List.mem_range.2 (by omega), ?_⟩
      change symFits w _ (starts w _ j rest) (.inl (decodeRule e).input) i = true
      simp only [symFits, List.any_eq_true, memB_iff]
      exact ⟨k, hkrest, hitem⟩

/-- **Correctness of the membership test.** -/
theorem memLanguageB_iff {g : EncodedCFG T} {w : List T} :
    memLanguageB g w = true ↔ w ∈ g.language := by
  rw [memLanguageB, memB_iff]
  change _ ↔ w ∈ g.toCFG.language
  rw [mem_language_iff_yields]
  constructor
  · intro h
    obtain ⟨A, i, j, hcode, -, -, hy⟩ := found_sound g w _ h
    have h1 := congrArg Nat.unpair hcode
    simp only [Nat.unpair_pair, Prod.mk.injEq] at h1
    obtain ⟨rfl, h2⟩ := h1
    have h3 := congrArg Nat.unpair h2
    simp only [Nat.unpair_pair, Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    rw [factor_zero_length] at hy
    exact hy
  · intro h
    have := mem_starts_of_yields h [.inl g.start] 0 w.length rfl (factor_zero_length w).symm
      (Nat.zero_le _) le_rfl
    simp only [starts, List.foldr_cons, List.foldr_nil] at this
    obtain ⟨-, hfit⟩ := List.mem_filter.1 this
    simp only [symFits, List.any_eq_true, memB_iff, List.mem_singleton] at hfit
    obtain ⟨k, rfl, hk⟩ := hfit
    exact hk


section MembershipComputable

variable [Primcodable T]

theorem primrec_symFits :
    Primrec fun x : (List T × List ℕ) × (List ℕ × (ℕ ⊕ T)) × ℕ =>
      symFits x.1.1 x.1.2 x.2.1.1 x.2.1.2 x.2.2 := by
  refine (Primrec.sumCasesOn (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
    (Cslib.Decidability.primrec_list_any
      (primrec_memB.comp₂ (Primrec.snd.comp₂ (Primrec.fst.comp₂ (Primrec.fst.comp₂ Primrec₂.left)))
        (Primrec₂.natPair.comp₂ (Primrec.snd.comp₂ Primrec₂.left)
          (Primrec₂.natPair.comp₂ (Primrec.snd.comp₂ (Primrec.snd.comp₂ (Primrec.fst.comp₂
            Primrec₂.left))) Primrec₂.right)))
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))).to₂
    (Primrec.and.comp₂
      (primrec_memB.comp₂ (Primrec.fst.comp₂ (Primrec.fst.comp₂ (Primrec.snd.comp₂ Primrec₂.left)))
        (Primrec.succ.comp₂ (Primrec.snd.comp₂ (Primrec.snd.comp₂ Primrec₂.left))))
      (Primrec.eq.decide.comp₂
        (Primrec.list_getElem?.comp₂ (Primrec.fst.comp₂ (Primrec.fst.comp₂ Primrec₂.left))
          (Primrec.snd.comp₂ (Primrec.snd.comp₂ Primrec₂.left)))
        (Primrec.option_some.comp₂ Primrec₂.right)))).of_eq ?_
  rintro ⟨⟨w, R⟩, ⟨S, X⟩, i⟩
  cases X <;> rfl

theorem primrec_starts :
    Primrec fun c : (List T × List ℕ) × ℕ × List (ℕ ⊕ T) => starts c.1.1 c.1.2 c.2.1 c.2.2 :=
  Primrec.list_foldr (Primrec.snd.comp Primrec.snd)
    (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.const []))
    (Cslib.Decidability.primrec_list_filter
      (primrec_symFits.comp (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.pair
          (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
            (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
          Primrec.snd))).to₂
      (Primrec.list_range.comp (Primrec.succ.comp
        (Primrec.list_length.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))))).to₂

theorem primrec_memStep :
    Primrec fun c : (EncodedCFG T × List T) × List ℕ => memStep c.1.1 c.1.2 c.2 :=
  Primrec.list_flatMap (primrec_rules.comp (Primrec.fst.comp Primrec.fst))
    (Primrec.list_flatMap
      (Primrec.list_range.comp (Primrec.succ.comp
        (Primrec.list_length.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))))
      (Primrec.list_map
        (primrec_starts.comp (Primrec.pair
          (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
            (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.pair Primrec.snd (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
        (Primrec₂.natPair.comp
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec₂.natPair.comp Primrec.snd (Primrec.snd.comp Primrec.fst))).to₂).to₂).to₂

omit [DecidableEq T] in
theorem primrec_items : Primrec₂ (items (T := T)) :=
  Primrec.list_flatMap (Primrec.list_map (primrec_rules.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd).to₂)
    (Primrec.list_flatMap
      (Primrec.list_range.comp (Primrec.succ.comp
        (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))))
      (Primrec.list_map
        (Primrec.list_range.comp (Primrec.succ.comp
          (Primrec.list_length.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))))
        (Primrec₂.natPair.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (Primrec₂.natPair.comp Primrec.snd (Primrec.snd.comp Primrec.fst))).to₂).to₂).to₂

theorem primrec_found : Primrec₂ (found (T := T)) :=
  Primrec.nat_iterate (Primrec.list_length.comp primrec_items) (Primrec.const [])
    primrec_memStep.to₂

theorem primrec_memLanguageB : Primrec₂ (memLanguageB (T := T)) :=
  primrec_memB.comp primrec_found
    (Primrec₂.natPair.comp (primrec_start.comp Primrec.fst)
      (Primrec₂.natPair.comp (Primrec.const 0) (Primrec.list_length.comp Primrec.snd)))


/-- **Sipser, Theorem 4.7**: membership for context-free grammars (A_CFG) is decidable by a
multi-stack machine. -/
theorem tm2Decidable_mem_language :
    Cslib.Decidability.TM2Decidable fun p : EncodedCFG T × List T => p.2 ∈ p.1.language :=
  Cslib.Decidability.tm2Decidable_iff_computablePred.2
    (Cslib.Decidability.computablePred_of_primrec_bool primrec_memLanguageB
      fun _ => memLanguageB_iff)

end MembershipComputable

end Cslib.Language.EncodedCFG

/-! ## Infiniteness -/

namespace Cslib.Language.EncodedCFG

open Cslib.Decidability

variable {T : Type*}

/-- A bound on the lengths of the right-hand sides, at least `2`: the largest length, or `2`. -/
def lenBound (g : EncodedCFG T) : ℕ :=
  g.rules.foldr (fun e m => max e.2.length m) 2

/-- The pumping bound of Ogden's lemma for the decoded grammar (`pumping_of_bound`):
`lenBound ^ (K + 1)` for `K` the number of distinct left-hand sides. -/
def pumpBound (g : EncodedCFG T) : ℕ :=
  g.lenBound ^ ((dedupB (g.rules.map Prod.fst)).length + 1)

/-- The words of length `n` over the letters `A`. -/
def wordsOver (A : List T) (n : ℕ) : List (List T) :=
  (fun W => W.flatMap fun w => A.map fun a => a :: w)^[n] [[]]

theorem mem_wordsOver {A : List T} {n : ℕ} {w : List T} :
    w ∈ wordsOver A n ↔ w.length = n ∧ ∀ a ∈ w, a ∈ A := by
  induction n generalizing w with
  | zero =>
      simp only [wordsOver, Function.iterate_zero, id_eq, List.mem_singleton,
        List.length_eq_zero_iff]
      constructor
      · rintro rfl
        simp
      · exact fun h => h.1
  | succ n ih =>
      rw [wordsOver, Function.iterate_succ_apply', ← wordsOver]
      simp only [List.mem_flatMap, List.mem_map, ih]
      constructor
      · rintro ⟨v, ⟨hv, hvA⟩, a, ha, rfl⟩
        refine ⟨by simp [hv], fun b hb => ?_⟩
        rcases List.mem_cons.1 hb with rfl | hb
        · exact ha
        · exact hvA b hb
      · rintro ⟨hlen, hA⟩
        obtain ⟨a, v, rfl⟩ : ∃ a v, w = a :: v := by
          cases w with
          | nil => simp at hlen
          | cons a v => exact ⟨a, v, rfl⟩
        exact ⟨v, ⟨by simpa using hlen, fun b hb => hA b (List.mem_cons_of_mem _ hb)⟩, a,
          hA a List.mem_cons_self, rfl⟩

theorem two_le_lenBound (g : EncodedCFG T) : 2 ≤ g.lenBound := by
  unfold lenBound
  induction g.rules with
  | nil => exact le_rfl
  | cons e l ih => simp only [List.foldr_cons]; omega

theorem length_le_lenBound {g : EncodedCFG T} {e : ℕ × List (ℕ ⊕ T)} (he : e ∈ g.rules) :
    e.2.length ≤ g.lenBound := by
  unfold lenBound
  generalize g.rules = l at he
  induction l with
  | nil => simp at he
  | cons e' l ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.1 he with rfl | he
      · omega
      · have := ih he
        omega

variable [DecidableEq T]

/-- The terminals occurring in the productions, each listed once (repetitions would make
`wordsOver` enumerate the same word many times). -/
def terminals (g : EncodedCFG T) : List T :=
  (g.rules.flatMap fun e => e.2.filterMap Sum.getRight?).foldr
    (fun a acc => cond (acc.any fun b => decide (b = a)) acc (a :: acc)) []

theorem mem_terminals {g : EncodedCFG T} {a : T} :
    a ∈ g.terminals ↔ ∃ e ∈ g.rules, Sum.inr a ∈ e.2 := by
  have key : ∀ (l : List T) (x : T), x ∈ l.foldr
      (fun a acc => cond (acc.any fun b => decide (b = a)) acc (a :: acc)) [] ↔ x ∈ l := by
    intro l
    induction l with
    | nil => simp
    | cons y l ih =>
        intro x
        simp only [List.foldr_cons]
        cases h : (l.foldr (fun a acc => cond (acc.any fun b => decide (b = a)) acc (a :: acc))
            []).any fun b => decide (b = y)
        · simp only [Bool.cond_false, List.mem_cons, ih]
        · simp only [Bool.cond_true, List.mem_cons, ih]
          obtain ⟨b, hb, hby⟩ := List.any_eq_true.1 h
          rw [decide_eq_true_eq] at hby
          subst hby
          rw [ih] at hb
          constructor
          · exact Or.inr
          · rintro (rfl | hx)
            · exact hb
            · exact hx
  rw [terminals, key, List.mem_flatMap]
  constructor
  · rintro ⟨e, he, ha⟩
    obtain ⟨s, hs, hsa⟩ := List.mem_filterMap.1 ha
    cases s with
    | inl i => simp at hsa
    | inr b =>
        obtain rfl : b = a := by simpa using hsa
        exact ⟨e, he, hs⟩
  · rintro ⟨e, he, ha⟩
    exact ⟨e, he, List.mem_filterMap.2 ⟨_, ha, rfl⟩⟩

/-- **The infiniteness test**: some word over the terminals whose length is between the pumping
bound `N` and `2N` is generated. -/
def infiniteB (g : EncodedCFG T) : Bool :=
  (List.range g.pumpBound).any fun i =>
    (wordsOver g.terminals (g.pumpBound + i)).any g.memLanguageB

omit [DecidableEq T] in
/-- Every letter of a yielded word occurs in the form or in a production. -/
private theorem terminal_mem_of_yields {G : ContextFreeGrammar T} {α : List (Symbol T G.NT)}
    {w : List T} (h : Yields G α w) {a : T} (ha : a ∈ w) :
    Symbol.terminal a ∈ α ∨ ∃ r ∈ G.rules, Symbol.terminal a ∈ r.output := by
  induction h with
  | nil => simp at ha
  | terminal b _ ih =>
      rcases List.mem_cons.1 ha with rfl | ha
      · exact Or.inl List.mem_cons_self
      · rcases ih ha with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h
  | nonterminal hr _ _ ihout ihrest =>
      rcases List.mem_append.1 ha with ha | ha
      · rcases ihout ha with h | h
        · exact Or.inr ⟨_, hr, h⟩
        · exact Or.inr h
      · rcases ihrest ha with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h

/-- The letters of the generated words are terminals of the productions. -/
theorem mem_terminals_of_mem_language {g : EncodedCFG T} {w : List T} (hw : w ∈ g.language)
    {a : T} (ha : a ∈ w) : a ∈ g.terminals := by
  rcases terminal_mem_of_yields (mem_language_iff_yields.1 hw) ha with h | ⟨r, hr, h⟩
  · simp at h
  · obtain ⟨e, he, rfl⟩ := mem_toCFG_rules.1 hr
    obtain ⟨s, hs, hsa⟩ := List.mem_map.1 h
    cases s with
    | inl i => simp [decodeSymbol] at hsa
    | inr b =>
        obtain rfl : b = a := by simpa [decodeSymbol] using hsa
        exact mem_terminals.2 ⟨e, he, hs⟩

/-- The pumping lemma for the decoded grammar, with the bound `pumpBound`. -/
theorem pumping_pumpBound (g : EncodedCFG T) :
    ∀ w ∈ g.language, g.pumpBound ≤ w.length → ∃ u v x y z : List T,
      w = u ++ v ++ x ++ y ++ z ∧ v ++ y ≠ [] ∧ (v ++ x ++ y).length ≤ g.pumpBound ∧
      ∀ i : ℕ, u ++ (List.replicate i v).flatten ++ x ++ (List.replicate i y).flatten ++ z ∈
        g.language :=
  pumping_of_bound g.toCFG (two_le_lenBound g)
    (fun r hr => by
      obtain ⟨e, he, rfl⟩ := mem_toCFG_rules.1 hr
      simpa [decodeRule] using length_le_lenBound he)
    ⟨dedupB (g.rules.map Prod.fst), le_rfl, fun r hr => by
      obtain ⟨e, he, rfl⟩ := mem_toCFG_rules.1 hr
      exact mem_dedupB.2 (List.mem_map_of_mem he)⟩ le_rfl

/-- A generated word of length at least `pumpBound` pumps: the language is infinite. -/
theorem infinite_of_mem_of_le {g : EncodedCFG T} {w : List T} (hw : w ∈ g.language)
    (hlen : g.pumpBound ≤ w.length) : g.language.Infinite := by
  obtain ⟨u, v, x, y, z, -, hvy, -, hpump⟩ := pumping_pumpBound g w hw hlen
  refine Set.infinite_of_injective_forall_mem (f := fun i : ℕ =>
    u ++ (List.replicate i v).flatten ++ x ++ (List.replicate i y).flatten ++ z)
    (fun i j hij => ?_) hpump
  have hlen := congrArg List.length hij
  simp only [List.length_append, List.length_flatten, List.map_replicate, List.sum_replicate,
    smul_eq_mul] at hlen
  have hpos : 0 < v.length + y.length := by
    rcases Nat.eq_zero_or_pos (v.length + y.length) with h | h
    · exact absurd (by simp_all [List.length_eq_zero_iff]) hvy
    · exact h
  have : i * (v.length + y.length) = j * (v.length + y.length) := by
    rw [Nat.mul_add, Nat.mul_add]
    omega
  exact Nat.eq_of_mul_eq_mul_right hpos this

/-- A generated word of length at least `pumpBound` can be shortened, keeping it generated and
at least that long, until it is shorter than twice that bound. -/
theorem exists_mem_le_lt {g : EncodedCFG T} :
    ∀ (n : ℕ) (w : List T), w.length = n → w ∈ g.language → g.pumpBound ≤ w.length →
      ∃ v ∈ g.language, g.pumpBound ≤ v.length ∧ v.length < 2 * g.pumpBound := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hn hw hlen
    by_cases hlt : w.length < 2 * g.pumpBound
    · exact ⟨w, hw, hlen, hlt⟩
    · obtain ⟨u, v, x, y, z, rfl, hvy, hvxy, hpump⟩ := pumping_pumpBound g w hw hlen
      have h0 := hpump 0
      simp only [List.replicate_zero, List.flatten_nil, List.append_nil] at h0
      have hpos : 0 < v.length + y.length := by
        rcases Nat.eq_zero_or_pos (v.length + y.length) with h | h
        · exact absurd (by simp_all [List.length_eq_zero_iff]) hvy
        · exact h
      simp only [List.length_append] at hn hlen hlt hvxy
      exact ih (u ++ x ++ z).length (by simp only [List.length_append]; omega) (u ++ x ++ z) rfl
        h0 (by simp only [List.length_append]; omega)

/-- **Infiniteness of context-free languages is decided by `infiniteB`.** -/
theorem infiniteB_iff {g : EncodedCFG T} : g.infiniteB = true ↔ g.language.Infinite := by
  rw [infiniteB, List.any_eq_true]
  constructor
  · rintro ⟨i, -, hi⟩
    obtain ⟨w, hw, hmem⟩ := List.any_eq_true.1 hi
    rw [mem_wordsOver] at hw
    exact infinite_of_mem_of_le (memLanguageB_iff.1 hmem) (by omega)
  · intro hinf
    have hfin : {w : List T | w.length < g.pumpBound ∧ ∀ a ∈ w, a ∈ g.terminals}.Finite := by
      refine ((List.range g.pumpBound).flatMap (wordsOver g.terminals)).finite_toSet.subset ?_
      rintro w ⟨hw, hA⟩
      exact List.mem_flatMap.2 ⟨w.length, List.mem_range.2 hw, mem_wordsOver.2 ⟨rfl, hA⟩⟩
    obtain ⟨w, hw, hlong⟩ := (hinf.sdiff hfin).nonempty
    have hle : g.pumpBound ≤ w.length := by
      by_contra h
      exact hlong ⟨by omega, fun a ha => mem_terminals_of_mem_language hw ha⟩
    obtain ⟨v, hv, hle', hlt⟩ := exists_mem_le_lt _ w rfl hw hle
    refine ⟨v.length - g.pumpBound, List.mem_range.2 (by omega), List.any_eq_true.2
      ⟨v, mem_wordsOver.2 ⟨by omega, fun a ha => mem_terminals_of_mem_language hv ha⟩,
        memLanguageB_iff.2 hv⟩⟩

section InfinitenessComputable

variable [Primcodable T]

theorem primrec_terminals : Primrec (terminals (T := T)) := by
  have hr : Primrec (Sum.getRight? : ℕ ⊕ T → Option T) :=
    (Primrec.sumCasesOn Primrec.id (Primrec₂.const none)
      (Primrec.option_some.comp₂ Primrec₂.right)).of_eq fun s => by cases s <;> rfl
  have hraw :
      Primrec fun g : EncodedCFG T => g.rules.flatMap fun e => e.2.filterMap Sum.getRight? :=
    Primrec.list_flatMap primrec_rules
      (Primrec.listFilterMap (Primrec.snd.comp Primrec.snd) (hr.comp₂ Primrec₂.right)).to₂
  exact Primrec.list_foldr hraw (Primrec.const [])
    (Primrec.cond
      (primrec_list_any (Primrec.eq.decide.comp₂ Primrec₂.right
          (Primrec.fst.comp₂ (Primrec.snd.comp₂ Primrec₂.left)))
        (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))).to₂

omit [DecidableEq T] in
theorem primrec_lenBound : Primrec (lenBound (T := T)) :=
  Primrec.list_foldr primrec_rules (Primrec.const 2)
    (Primrec.nat_max.comp (Primrec.list_length.comp (Primrec.snd.comp (Primrec.fst.comp
      Primrec.snd))) (Primrec.snd.comp Primrec.snd)).to₂

omit [DecidableEq T] in
theorem primrec_pumpBound : Primrec (pumpBound (T := T)) :=
  (Primrec₂.unpaired'.1 Nat.Primrec.pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ)).comp primrec_lenBound
    (Primrec.succ.comp (Primrec.list_length.comp (primrec_dedupB.comp
      (Primrec.list_map primrec_rules (Primrec.fst.comp Primrec.snd).to₂))))

omit [DecidableEq T] in
theorem primrec_wordsOver : Primrec₂ (wordsOver (T := T)) :=
  (Primrec.nat_iterate Primrec.snd (Primrec.const [[]])
    (Primrec.list_flatMap Primrec.snd
      (Primrec.list_map (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.list_cons.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂).to₂).to₂).to₂

theorem primrec_infiniteB : Primrec (infiniteB (T := T)) :=
  primrec_list_any
    (primrec_list_any (primrec_memLanguageB.comp₂ (Primrec.fst.comp₂ Primrec₂.left)
        Primrec₂.right)
      (primrec_wordsOver.comp (primrec_terminals.comp Primrec.fst)
        (Primrec.nat_add.comp (primrec_pumpBound.comp Primrec.fst) Primrec.snd))).to₂
    (Primrec.list_range.comp primrec_pumpBound)

/-- **Infiniteness of context-free languages (INFINITE_CFG) is decidable** by a multi-stack
machine. -/
theorem tm2Decidable_language_infinite :
    Cslib.Decidability.TM2Decidable fun g : EncodedCFG T => g.language.Infinite :=
  Cslib.Decidability.tm2Decidable_iff_computablePred.2
    (Cslib.Decidability.computablePred_of_primrec_bool primrec_infiniteB fun _ => infiniteB_iff)

end InfinitenessComputable

end Cslib.Language.EncodedCFG

/-! ## Deprecated names

The list helpers moved to `Decidability/PrimrecList.lean` (namespace `Cslib.Decidability`). -/

namespace Cslib.Language.EncodedCFG

@[deprecated (since := "2026-10-15")] alias memB := Cslib.Decidability.memB
@[deprecated (since := "2026-10-15")] alias memB_iff := Cslib.Decidability.memB_iff
@[deprecated (since := "2026-10-15")] alias iterate_closed := Cslib.Decidability.iterate_closed
@[deprecated (since := "2026-10-15")] alias primrec_memB := Cslib.Decidability.primrec_memB

end Cslib.Language.EncodedCFG
