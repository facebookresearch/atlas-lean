/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Emptiness of the intersection of a context-free and a regular language
-/
module

public import CSLibExt.Computability.Decidability.ContextFree
public import CSLibExt.Computability.Decidability.Regular

/-!
# Emptiness of the intersection of a context-free and a regular language

For an encoded grammar `g` (`Cslib.Language.EncodedCFG`) and an encoded DFA `D`
(`Cslib.Automata.EncodedDFA`), `EncodedCFG.interEmptyB g D` decides whether no word of `g` is
accepted by `D`. Like the membership test, it is a fixed point over items `(A, p, q)`, read "`A`
yields a word that takes `D` from state `p` to state `q`", with `p` and `q` among the listed states
of `D`.

* `EncodedCFG.dfaStarts`: the states from which a right-hand side yields a word ending in `q`,
  given the items found so far; `EncodedCFG.dfaStep`: one round; `EncodedCFG.dfaFound`: the items
  after as many rounds as there are candidate items, a fixed point by `iterate_closed`.
* `EncodedCFG.dfaFound_sound` and `EncodedCFG.mem_dfaStarts_of_yields`: soundness and
  completeness, by induction on `Yields`.
* `EncodedCFG.interEmptyB_iff`: `interEmptyB g D = true ↔ g.language ⊓ D.language = 0`;
  `EncodedCFG.tm2Decidable_inter_eq_zero`: decidable by a multi-stack machine.
* `EncodedCFG.subsetB_iff`: inclusion `g.language ≤ D.language` is the emptiness of the
  intersection with the complement DFA (`EncodedDFA.compl`, `EncodedDFA.mem_language_compl` in
  `Automata/DA/EncodedDFA.lean`); `EncodedCFG.tm2Decidable_language_le`.
-/

@[expose] public section

namespace Cslib.Language.EncodedCFG

open Cslib.Decidability Cslib.Automata

variable {T : Type*} [DecidableEq T]

/-! ## The procedure -/

/-- **Whether a symbol fits at a DFA state.** Let $D$ be an encoded DFA, $R$ and $S$ lists of
natural numbers (the items found so far and the states where the rest of a right-hand side can
start), $X$ a grammar symbol and $p \in \mathbb{N}$. The test is true exactly when either $X$ is a
terminal $a$ and the step of $D$ from $p$ on $a$ lies in $S$, or $X$ is a nonterminal $B$ and some
$k$ in $S$ has $\langle B, \langle p, k \rangle \rangle$ in $R$, where
$\langle \cdot, \cdot \rangle$ is the natural-number pairing. -/
def dfaSymFits (D : EncodedDFA T) (R S : List ℕ) (X : ℕ ⊕ T) (p : ℕ) : Bool :=
  match X with
  | .inr a => Decidability.memB S (D.step p a)
  | .inl B => S.any fun k => Decidability.memB R (Nat.pair B (Nat.pair p k))

/-- **Start states of a right-hand side in a DFA.** Let $D$ be an encoded DFA, $R$ a list of
natural numbers (the items found so far) and $q \in \mathbb{N}$. The start states of a right-hand
side $\beta$, a list of grammar symbols, for $q$ given $R$ are defined by recursion on $\beta$: for
the empty right-hand side they are the one-element list $[q]$, and for a symbol $X$ followed by
$\beta'$ they are the states of $D$, in order, at which $X$ fits given $R$ and the start states of
$\beta'$ for $q$ given $R$. -/
def dfaStarts (D : EncodedDFA T) (R : List ℕ) (q : ℕ) (rhs : List (ℕ ⊕ T)) : List ℕ :=
  rhs.foldr (fun X S => D.states.filter (dfaSymFits D R S X)) [q]

/-- **One round of the item search against a DFA.** For an encoded grammar $g$, an encoded DFA
$D$ and a list $R$ of natural numbers (the items found so far), one round produces the list of the
codes $\langle A, \langle p, q \rangle \rangle$, where $\langle \cdot, \cdot \rangle$ is the
natural-number pairing, for every production $A \to \beta$ of $g$, every state $q$ of $D$ and
every start state $p$ of $\beta$ for $q$ given $R$. -/
def dfaStep (g : EncodedCFG T) (D : EncodedDFA T) (R : List ℕ) : List ℕ :=
  g.rules.flatMap fun e => D.states.flatMap fun q =>
    (dfaStarts D R q e.2).map fun p => Nat.pair e.1 (Nat.pair p q)

/-- **Candidate items for a grammar and a DFA.** For an encoded grammar $g$ and an encoded DFA
$D$, the candidate items form the list of the codes $\langle A, \langle p, q \rangle \rangle$, where
$\langle \cdot, \cdot \rangle$ is the natural-number pairing, for every left-hand side $A$ of a
production of $g$ (listed once per production) and all states $p$ and $q$ of $D$. -/
def dfaItems (g : EncodedCFG T) (D : EncodedDFA T) : List ℕ :=
  (g.rules.map Prod.fst).flatMap fun A => D.states.flatMap fun q =>
    D.states.map fun p => Nat.pair A (Nat.pair p q)

/-- **Items found for a grammar and a DFA.** For an encoded grammar $g$ and an encoded DFA $D$,
the found items are the list obtained from the empty list by applying one round of the item
search of $g$ and $D$ as many times as the length of the list of candidate items of $g$ and
$D$. -/
def dfaFound (g : EncodedCFG T) (D : EncodedDFA T) : List ℕ :=
  (dfaStep g D)^[(dfaItems g D).length] []

/-- **The intersection-emptiness test for a grammar and a DFA.** Let $g$ be an encoded grammar with
start nonterminal $S$, let $D$ be an encoded DFA with start state $s$, and write
$\langle \cdot, \cdot \rangle$ for the natural-number pairing. The test of $g$ and $D$ is true
exactly when there is no accepting state $f$ of $D$ that is also one of the states of $D$ and for
which the code $\langle S, \langle s, f \rangle \rangle$ is among the found items of $g$ and
$D$. -/
def interEmptyB (g : EncodedCFG T) (D : EncodedDFA T) : Bool :=
  !(D.accept.any fun f => Decidability.memB D.states f &&
    Decidability.memB (dfaFound g D) (Nat.pair g.start (Nat.pair D.start f)))

/-! ## Stabilization -/

/-- **Start states of a right-hand side are states of the DFA.** Let $D$ be an encoded DFA, $R$ a
list of natural numbers and $q$ one of the states of $D$. Then for every right-hand side $\beta$,
every start state of $\beta$ for $q$ given $R$ is one of the states of $D$. -/
theorem dfaStarts_subset {D : EncodedDFA T} {R : List ℕ} {q : ℕ} (hq : q ∈ D.states)
    (rhs : List (ℕ ⊕ T)) : ∀ p ∈ dfaStarts D R q rhs, p ∈ D.states := by
  cases rhs with
  | nil =>
      intro p hp
      simp only [dfaStarts, List.foldr_nil, List.mem_singleton] at hp
      rw [hp]
      exact hq
  | cons X rhs =>
      intro p hp
      simp only [dfaStarts, List.foldr_cons] at hp
      exact (List.mem_filter.1 hp).1

theorem dfaStarts_mono {D : EncodedDFA T} {R R' : List ℕ} (h : R ⊆ R') (q : ℕ) :
    ∀ rhs : List (ℕ ⊕ T), dfaStarts D R q rhs ⊆ dfaStarts D R' q rhs
  | [] => List.Subset.refl _
  | X :: rhs => by
      intro p hp
      simp only [dfaStarts, List.foldr_cons] at hp ⊢
      obtain ⟨hs, hfit⟩ := List.mem_filter.1 hp
      refine List.mem_filter.2 ⟨hs, ?_⟩
      have ih := dfaStarts_mono (D := D) h q rhs
      change dfaSymFits D R (dfaStarts D R q rhs) X p = true at hfit
      change dfaSymFits D R' (dfaStarts D R' q rhs) X p = true
      cases X with
      | inr a =>
          simp only [dfaSymFits, Decidability.memB_iff] at hfit ⊢
          exact ih hfit
      | inl B =>
          simp only [dfaSymFits, List.any_eq_true, Decidability.memB_iff] at hfit ⊢
          obtain ⟨k, hk, hR⟩ := hfit
          exact ⟨k, ih hk, h hR⟩

theorem dfaStep_mono {g : EncodedCFG T} {D : EncodedDFA T} {R R' : List ℕ} (h : R ⊆ R') :
    dfaStep g D R ⊆ dfaStep g D R' := by
  intro x hx
  simp only [dfaStep, List.mem_flatMap, List.mem_map] at hx ⊢
  obtain ⟨e, he, q, hq, p, hp, rfl⟩ := hx
  exact ⟨e, he, q, hq, p, dfaStarts_mono h q e.2 hp, rfl⟩

theorem dfaStep_subset_items {g : EncodedCFG T} {D : EncodedDFA T} (R : List ℕ) :
    dfaStep g D R ⊆ dfaItems g D := by
  intro x hx
  simp only [dfaStep, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨e, he, q, hq, p, hp, rfl⟩ := hx
  simp only [dfaItems, List.mem_flatMap, List.mem_map]
  exact ⟨e.1, ⟨e, he, rfl⟩, q, hq, p, dfaStarts_subset hq e.2 p hp, rfl⟩

theorem dfaStep_dfaFound_subset (g : EncodedCFG T) (D : EncodedDFA T) :
    dfaStep g D (dfaFound g D) ⊆ dfaFound g D :=
  Decidability.iterate_closed (fun _ _ => dfaStep_mono) (dfaItems g D) dfaStep_subset_items

/-! ## Soundness -/

/-- **Sound items for a grammar and a DFA.** For an encoded grammar $g$ and an encoded DFA $D$, a
natural number $x$ is a sound item when there are natural numbers $A$, $p$, $q$ and a word $w$
such that $x = \langle A, \langle p, q \rangle \rangle$, where $\langle \cdot, \cdot \rangle$ is the
natural-number pairing, the nonterminal $A$ yields $w$ in the grammar denoted by $g$, and the
automaton denoted by $D$, run on $w$ from state $p$, ends in state $q$. -/
def DfaSoundItem (g : EncodedCFG T) (D : EncodedDFA T) (x : ℕ) : Prop :=
  ∃ A p q w, x = Nat.pair A (Nat.pair p q) ∧ Yields g.toCFG [.nonterminal A] w ∧
    D.toDFA.evalFrom p w = q

theorem dfaStarts_sound {g : EncodedCFG T} {D : EncodedDFA T} {R : List ℕ}
    (hR : ∀ x ∈ R, DfaSoundItem g D x) {q : ℕ} :
    ∀ (rhs : List (ℕ ⊕ T)) p, p ∈ dfaStarts D R q rhs →
      ∃ w, Yields g.toCFG (rhs.map decodeSymbol) w ∧ D.toDFA.evalFrom p w = q
  | [], p, hp => by
      simp only [dfaStarts, List.foldr_nil, List.mem_singleton] at hp
      exact ⟨[], Yields.nil, hp⟩
  | X :: rhs, p, hp => by
      simp only [dfaStarts, List.foldr_cons] at hp
      obtain ⟨-, hfit⟩ := List.mem_filter.1 hp
      change dfaSymFits D R (dfaStarts D R q rhs) X p = true at hfit
      cases X with
      | inr a =>
          simp only [dfaSymFits, Decidability.memB_iff] at hfit
          obtain ⟨w, hy, hrun⟩ := dfaStarts_sound hR rhs _ hfit
          exact ⟨a :: w, Yields.terminal a hy, hrun⟩
      | inl B =>
          simp only [dfaSymFits, List.any_eq_true, Decidability.memB_iff] at hfit
          obtain ⟨k, hk, hRk⟩ := hfit
          obtain ⟨w₂, hy₂, hrun₂⟩ := dfaStarts_sound hR rhs k hk
          obtain ⟨A, p', k', w₁, hcode, hy₁, hrun₁⟩ := hR _ hRk
          obtain ⟨hB, hp', hk'⟩ : B = A ∧ p = p' ∧ k = k' := by
            have h1 := congrArg Nat.unpair hcode
            simp only [Nat.unpair_pair, Prod.mk.injEq] at h1
            obtain ⟨h1, h2⟩ := h1
            have h3 := congrArg Nat.unpair h2
            simp only [Nat.unpair_pair, Prod.mk.injEq] at h3
            exact ⟨h1, h3.1, h3.2⟩
          subst hB hp' hk'
          have hy : Yields g.toCFG ([.nonterminal B] ++ rhs.map decodeSymbol) (w₁ ++ w₂) :=
            Yields.append hy₁ hy₂
          refine ⟨w₁ ++ w₂, hy, ?_⟩
          rw [DFA.evalFrom_of_append, hrun₁, hrun₂]

theorem dfaStep_sound {g : EncodedCFG T} {D : EncodedDFA T} {R : List ℕ}
    (hR : ∀ x ∈ R, DfaSoundItem g D x) : ∀ x ∈ dfaStep g D R, DfaSoundItem g D x := by
  intro x hx
  simp only [dfaStep, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨e, he, q, -, p, hp, rfl⟩ := hx
  obtain ⟨w, hy, hrun⟩ := dfaStarts_sound hR e.2 p hp
  exact ⟨e.1, p, q, w, rfl,
    yields_of_rule (r := decodeRule e) (mem_toCFG_rules.2 ⟨e, he, rfl⟩) hy, hrun⟩

theorem dfaFound_sound (g : EncodedCFG T) (D : EncodedDFA T) :
    ∀ x ∈ dfaFound g D, DfaSoundItem g D x := by
  unfold dfaFound
  generalize (dfaItems g D).length = n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact dfaStep_sound ih

/-! ## Completeness -/

/-- **Completeness of the start states in a DFA.** Let $g$ be an encoded context-free grammar and
$D$ an encoded DFA over an alphabet $T$ with decidable equality, and let $\rho$ be an encoded
right-hand side whose decoding yields a word $u$ in the grammar that $g$ denotes. If $p$ is one
of the states of $D$ and the automaton that $D$ denotes, run on $u$ from state $p$, ends in state
$q$, then $p$ is a start state of $\rho$ for $q$ given the items found for $g$ and $D$. -/
theorem mem_dfaStarts_of_yields {g : EncodedCFG T} {D : EncodedDFA T}
    {β : List (Symbol T g.toCFG.NT)} {u : List T} (h : Yields g.toCFG β u) :
    ∀ (rhs : List (ℕ ⊕ T)) (p q : ℕ), β = rhs.map decodeSymbol → p ∈ D.states →
      D.toDFA.evalFrom p u = q → p ∈ dfaStarts D (dfaFound g D) q rhs := by
  induction h with
  | nil =>
      intro rhs p q hrhs _ hrun
      obtain rfl : rhs = [] := List.map_eq_nil_iff.1 hrhs.symm
      simp only [dfaStarts, List.foldr_nil, List.mem_singleton]
      exact hrun
  | terminal a h ih =>
      intro rhs p q hrhs hp hrun
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
      have hnext := ih rest (D.step p a) q hrest (EncodedDFA.step_mem_states hp a) hrun
      simp only [dfaStarts, List.foldr_cons]
      refine List.mem_filter.2 ⟨hp, ?_⟩
      change dfaSymFits D _ (dfaStarts D _ q rest) (.inr a) p = true
      simp only [dfaSymFits, Decidability.memB_iff]
      exact hnext
  | @nonterminal r hr u w₁ w₂ hout hrest ihout ihrest =>
      intro rhs p q hrhs hp hrun
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
      set k := D.toDFA.evalFrom p w₁
      have hk : k ∈ D.states := EncodedDFA.evalFrom_mem_states hp w₁
      rw [DFA.evalFrom_of_append] at hrun
      have hkrest := ihrest rest k q hrestEq hk hrun
      obtain ⟨e, he, rfl⟩ := mem_toCFG_rules.1 hr
      have hstart := ihout e.2 p k rfl hp rfl
      have hitem : Nat.pair e.1 (Nat.pair p k) ∈ dfaFound g D := by
        apply dfaStep_dfaFound_subset
        simp only [dfaStep, List.mem_flatMap, List.mem_map]
        exact ⟨e, he, k, hk, p, hstart, rfl⟩
      simp only [dfaStarts, List.foldr_cons]
      refine List.mem_filter.2 ⟨hp, ?_⟩
      change dfaSymFits D _ (dfaStarts D _ q rest) (.inl (decodeRule e).input) p = true
      simp only [dfaSymFits, List.any_eq_true, Decidability.memB_iff]
      exact ⟨k, hkrest, hitem⟩

/-- **Correctness of the intersection-emptiness test.** For every encoded grammar $g$ and every
encoded DFA $D$, the intersection-emptiness test of $g$ and $D$ returns true if and only if the
intersection of the language of $g$ and the language of $D$ is empty. -/
theorem interEmptyB_iff {g : EncodedCFG T} {D : EncodedDFA T} :
    interEmptyB g D = true ↔ g.language ⊓ D.language = 0 := by
  rw [interEmptyB, Bool.not_eq_true', ← Bool.not_eq_true, List.any_eq_true]
  constructor
  · intro hno
    ext w
    simp only [Language.notMem_zero, iff_false]
    rintro ⟨hg, hD⟩
    refine hno ⟨D.toDFA.eval w, hD, ?_⟩
    have hy : Yields g.toCFG [.nonterminal g.start] w := mem_language_iff_yields.1 hg
    have := mem_dfaStarts_of_yields hy [.inl g.start] D.start (D.toDFA.eval w) rfl
      List.mem_cons_self rfl
    simp only [dfaStarts, List.foldr_cons, List.foldr_nil] at this
    obtain ⟨-, hfit⟩ := List.mem_filter.1 this
    simp only [dfaSymFits, List.any_eq_true, Decidability.memB_iff, List.mem_singleton] at hfit
    obtain ⟨k, rfl, hk⟩ := hfit
    simp only [Bool.and_eq_true, Decidability.memB_iff]
    exact ⟨EncodedDFA.eval_mem_states D w, hk⟩
  · rintro h ⟨f, hf, hfound⟩
    simp only [Bool.and_eq_true, Decidability.memB_iff] at hfound
    obtain ⟨A, p, q, w, hcode, hy, hrun⟩ := dfaFound_sound g D _ hfound.2
    have h1 := congrArg Nat.unpair hcode
    simp only [Nat.unpair_pair, Prod.mk.injEq] at h1
    obtain ⟨rfl, h2⟩ := h1
    have h3 := congrArg Nat.unpair h2
    simp only [Nat.unpair_pair, Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    have hw : w ∈ g.language ⊓ D.language :=
      ⟨mem_language_iff_yields.2 hy, by
        change D.toDFA.evalFrom D.start w ∈ D.accept
        rw [hrun]
        exact hf⟩
    rw [h] at hw
    exact Language.notMem_zero w hw

/-- **The inclusion test for a grammar and a DFA.** For an encoded context-free grammar $g$ and an
encoded DFA $D$ over the same alphabet $T$, where $T$ has decidable equality, the inclusion test on
$g$ and $D$ is the Boolean value of the emptiness test on $g$ and the complement of $D$. -/
def subsetB (g : EncodedCFG T) (D : EncodedDFA T) : Bool :=
  interEmptyB g D.compl

/-- **Correctness of the inclusion test.** For every alphabet $T$ with decidable equality, every
encoded context-free grammar $g$ over $T$ and every encoded DFA $D$ over $T$, the inclusion test
on $g$ and $D$ returns true if and only if the language of $g$ is contained in the language of
$D$. -/
theorem subsetB_iff {g : EncodedCFG T} {D : EncodedDFA T} :
    subsetB g D = true ↔ g.language ≤ D.language := by
  rw [subsetB, interEmptyB_iff]
  constructor
  · intro h w hw
    by_contra hD
    have : w ∈ g.language ⊓ D.compl.language := ⟨hw, EncodedDFA.mem_language_compl.2 hD⟩
    rw [h] at this
    exact Language.notMem_zero w this
  · intro h
    ext w
    simp only [Language.notMem_zero, iff_false]
    rintro ⟨hg, hc⟩
    exact EncodedDFA.mem_language_compl.1 hc (h hg)

/-! ## Computability -/

section Computable

variable [Primcodable T]

theorem primrec_dfaSymFits :
    Primrec fun x : (EncodedDFA T × List ℕ) × (List ℕ × (ℕ ⊕ T)) × ℕ =>
      dfaSymFits x.1.1 x.1.2 x.2.1.1 x.2.1.2 x.2.2 := by
  refine (Primrec.sumCasesOn (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
    (primrec_list_any
      (Decidability.primrec_memB.comp₂
        (Primrec.snd.comp₂ (Primrec.fst.comp₂ (Primrec.fst.comp₂ Primrec₂.left)))
        (Primrec₂.natPair.comp₂ (Primrec.snd.comp₂ Primrec₂.left)
          (Primrec₂.natPair.comp₂ (Primrec.snd.comp₂ (Primrec.snd.comp₂ (Primrec.fst.comp₂
            Primrec₂.left))) Primrec₂.right)))
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))).to₂
    (Decidability.primrec_memB.comp₂
      (Primrec.fst.comp₂ (Primrec.fst.comp₂ (Primrec.snd.comp₂ Primrec₂.left)))
      (EncodedDFA.primrec_step.comp₂ (Primrec₂.pair.comp₂
        (Primrec.fst.comp₂ (Primrec.fst.comp₂ Primrec₂.left))
        (Primrec₂.pair.comp₂ (Primrec.snd.comp₂ (Primrec.snd.comp₂ Primrec₂.left))
          Primrec₂.right))))).of_eq ?_
  rintro ⟨⟨D, R⟩, ⟨S, X⟩, p⟩
  cases X <;> rfl

theorem primrec_dfaStarts :
    Primrec fun c : (EncodedDFA T × List ℕ) × ℕ × List (ℕ ⊕ T) =>
      dfaStarts c.1.1 c.1.2 c.2.1 c.2.2 := by
  have hfit : Primrec₂ fun (y : ((EncodedDFA T × List ℕ) × ℕ × List (ℕ ⊕ T)) ×
      ((ℕ ⊕ T) × List ℕ)) (p : ℕ) => dfaSymFits y.1.1.1 y.1.1.2 y.2.2 y.2.1 p :=
    (primrec_dfaSymFits.comp (Primrec.pair
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.pair
        (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
        Primrec.snd))).to₂
  have hl : Primrec fun (y : ((EncodedDFA T × List ℕ) × ℕ × List (ℕ ⊕ T)) ×
      ((ℕ ⊕ T) × List ℕ)) => y.1.1.1.states :=
    EncodedDFA.primrec_states.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hstep := primrec_list_filter hfit hl
  have hfold := Primrec.list_foldr (Primrec.snd.comp Primrec.snd)
    (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.const [])) hstep.to₂
  refine hfold.of_eq fun c => ?_
  simp only [dfaStarts]

theorem primrec_dfaStep :
    Primrec fun c : (EncodedCFG T × EncodedDFA T) × List ℕ => dfaStep c.1.1 c.1.2 c.2 :=
  Primrec.list_flatMap (primrec_rules.comp (Primrec.fst.comp Primrec.fst))
    (Primrec.list_flatMap
      (EncodedDFA.primrec_states.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.list_map
        (primrec_dfaStarts.comp (Primrec.pair
          (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
            (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.pair Primrec.snd (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
        (Primrec₂.natPair.comp
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec₂.natPair.comp Primrec.snd (Primrec.snd.comp Primrec.fst))).to₂).to₂).to₂

omit [DecidableEq T] in
theorem primrec_dfaItems : Primrec₂ (dfaItems (T := T)) :=
  Primrec.list_flatMap (Primrec.list_map (primrec_rules.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd).to₂)
    (Primrec.list_flatMap (EncodedDFA.primrec_states.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.list_map
        (EncodedDFA.primrec_states.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec₂.natPair.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (Primrec₂.natPair.comp Primrec.snd (Primrec.snd.comp Primrec.fst))).to₂).to₂).to₂

theorem primrec_dfaFound : Primrec₂ (dfaFound (T := T)) :=
  Primrec.nat_iterate (Primrec.list_length.comp primrec_dfaItems) (Primrec.const [])
    primrec_dfaStep.to₂

theorem primrec_interEmptyB : Primrec₂ (interEmptyB (T := T)) :=
  Primrec.not.comp (primrec_list_any
    (Primrec.and.comp₂
      (Decidability.primrec_memB.comp₂
        (EncodedDFA.primrec_states.comp₂ (Primrec.snd.comp₂ Primrec₂.left)) Primrec₂.right)
      (Decidability.primrec_memB.comp₂ (primrec_dfaFound.comp₂ (Primrec.fst.comp₂ Primrec₂.left)
          (Primrec.snd.comp₂ Primrec₂.left))
        (Primrec₂.natPair.comp₂ (primrec_start.comp₂ (Primrec.fst.comp₂ Primrec₂.left))
          (Primrec₂.natPair.comp₂
            (EncodedDFA.primrec_start.comp₂ (Primrec.snd.comp₂ Primrec₂.left))
            Primrec₂.right))))
    (EncodedDFA.primrec_accept.comp Primrec.snd))

theorem primrec_subsetB : Primrec₂ (subsetB (T := T)) :=
  primrec_interEmptyB.comp₂ Primrec₂.left (EncodedDFA.primrec_compl.comp₂ Primrec₂.right)

/-- **Emptiness of the intersection of a context-free and a regular language is decidable.** For
every alphabet $T$ with decidable equality and a primitive recursive encoding, the property of a
pair $(g, D)$, where $g$ is an encoded context-free grammar over $T$ and $D$ is an encoded DFA
over $T$, that the intersection of the language of $g$ and the language of $D$ is empty is
decidable by a multi-stack machine. -/
theorem tm2Decidable_inter_eq_zero :
    TM2Decidable fun p : EncodedCFG T × EncodedDFA T => p.1.language ⊓ p.2.language = 0 :=
  tm2Decidable_iff_computablePred.2
    (computablePred_of_primrec_bool primrec_interEmptyB fun _ => interEmptyB_iff)

/-- **Inclusion of a context-free language in a regular language is decidable.** For every
alphabet $T$ with decidable equality and a primitive recursive encoding, the property of a pair
$(g, D)$, where $g$ is an encoded context-free grammar over $T$ and $D$ is an encoded DFA over
$T$, that the language of $g$ is contained in the language of $D$ is decidable by a multi-stack
machine. -/
theorem tm2Decidable_language_le :
    TM2Decidable fun p : EncodedCFG T × EncodedDFA T => p.1.language ≤ p.2.language :=
  tm2Decidable_iff_computablePred.2
    (computablePred_of_primrec_bool primrec_subsetB fun _ => subsetB_iff)

end Computable

end Cslib.Language.EncodedCFG
