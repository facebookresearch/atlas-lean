/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.PDA
public import Mathlib.Data.Finset.Prod

/-!
# From pushdown automata to context-free grammars

The classic triple construction: for a pushdown automaton `M` with finite
state and stack alphabets whose transitions consume letters from a finite
set `T₀`, the grammar with nonterminals `Option (σ × Γ × σ)` (where
`some (p, γ, q)` derives exactly the words that take `M` from state `p`
with stack `[γ]` to state `q` with empty stack) generates the language
accepted by `M`.

## Main results

* `Cslib.Language.pdaGrammar`: the triple grammar.
* `Cslib.Automata.PDA.pdaGrammar_language`: it generates `M.accepts`.
* `Cslib.Automata.PDA.isContextFree_accepts`: languages accepted by finite
  PDAs are context-free.
* `Cslib.Language.isContextFree_iff_exists_pda_accepts`: over a `Type`
  alphabet, the context-free languages are exactly the languages accepted
  by empty stack by finite pushdown automata.
-/

@[expose] public section

namespace Cslib.Language

open Automata

attribute [local instance] Classical.propDecidable

variable {T : Type*} {σ : Type} {Γ : Type} {M : PDA T σ Γ} {T₀ : Finset T}

/-- The form of triple nonterminals for a stack `γs` read along a state
sequence `ss` of length `γs.length + 1`: consecutive states bracket each
stack symbol. -/
def chainForm : List Γ → List σ → List (Symbol T (Option (σ × Γ × σ)))
  | [], _ => []
  | _ :: _, [] => []
  | _ :: _, _ :: [] => []
  | γ :: γs, p :: q :: ss =>
    Symbol.nonterminal (some (p, γ, q)) :: chainForm γs (q :: ss)

theorem chainForm_nil (ss : List σ) :
    @chainForm T σ Γ [] ss = [] := rfl

theorem chainForm_cons_cons {γ : Γ} {γs : List Γ} {p q : σ} {ss : List σ} :
    @chainForm T σ Γ (γ :: γs) (p :: q :: ss) =
      Symbol.nonterminal (some (p, γ, q)) :: @chainForm T σ Γ γs (q :: ss) :=
  rfl

/-- Every symbol of a chain form is a nonterminal. -/
theorem nonterminal_of_mem_chainForm {s : Symbol T (Option (σ × Γ × σ))}
    {γs : List Γ} {ss : List σ} (hs : s ∈ chainForm γs ss) :
    ∃ A, s = Symbol.nonterminal A := by
  induction γs generalizing ss with
  | nil => simp [chainForm] at hs
  | cons γ γs ih =>
    cases ss with
    | nil => simp [chainForm] at hs
    | cons p ss =>
      cases ss with
      | nil => simp [chainForm] at hs
      | cons q ss =>
        rw [chainForm_cons_cons] at hs
        cases List.mem_cons.mp hs with
        | inl h => exact ⟨_, h⟩
        | inr h => exact ih h

/-- A chain form over an appended stack splits into two chain forms at
some intermediate state. -/
private theorem chainForm_append_split :
    ∀ (L₁ L₂ : List Γ) (ss : List σ),
      ss.length = (L₁ ++ L₂).length + 1 →
      ∀ {p q : σ}, ss.head? = some p → ss.getLast? = some q →
        ∃ ss₁ ss₂ m, ss₁.length = L₁.length + 1 ∧
          ss₂.length = L₂.length + 1 ∧ ss₁.head? = some p ∧
          ss₁.getLast? = some m ∧ ss₂.head? = some m ∧
          ss₂.getLast? = some q ∧
          @chainForm T σ Γ (L₁ ++ L₂) ss =
            @chainForm T σ Γ L₁ ss₁ ++ @chainForm T σ Γ L₂ ss₂ := by
  intro L₁
  induction L₁ with
  | nil =>
    intro L₂ ss hlen p q hhead hlast
    exact ⟨[p], ss, p, rfl, hlen, rfl, rfl, hhead, hlast, rfl⟩
  | cons δ L₁ ih =>
    intro L₂ ss hlen p q hhead hlast
    cases ss with
    | nil =>
      simp only [List.length_nil, List.length_cons, List.length_append] at hlen
      omega
    | cons b ss₀ =>
      cases ss₀ with
      | nil =>
        simp only [List.length_nil, List.length_cons, List.length_append] at hlen
        omega
      | cons c ss₀ =>
        have hb : b = p := Option.some.inj hhead
        subst hb
        have hlast' : (c :: ss₀).getLast? = some q := by
          rwa [List.getLast?_cons_cons] at hlast
        have hlen' : (c :: ss₀).length = (L₁ ++ L₂).length + 1 := by
          simp only [List.length_cons, List.length_append] at hlen ⊢
          omega
        obtain ⟨ss₁', ss₂, m, h1len, h2len, h1head, h1last, h2head, h2last,
          hchain⟩ := ih L₂ (c :: ss₀) hlen' rfl hlast'
        obtain ⟨ss₁'', hss₁'⟩ := List.head?_eq_some_iff.mp h1head
        refine ⟨b :: ss₁', ss₂, m, by simp [h1len], h2len, rfl, ?_, h2head,
          h2last, ?_⟩
        · rw [hss₁'] at h1last ⊢
          rwa [List.getLast?_cons_cons]
        · rw [hss₁'] at hchain ⊢
          rw [List.cons_append, chainForm_cons_cons, chainForm_cons_cons,
            hchain, List.cons_append]

variable [Fintype σ] [Fintype Γ]

/-- All lists of states of a given length, as a finset. -/
noncomputable def stateLists : ℕ → Finset (List σ)
  | 0 => {[]}
  | n + 1 => (Finset.univ ×ˢ stateLists n).image fun x => x.1 :: x.2

theorem mem_stateLists {n : ℕ} {ss : List σ} :
    ss ∈ stateLists n ↔ ss.length = n := by
  induction n generalizing ss with
  | zero =>
    simp [stateLists]
  | succ n ih =>
    simp only [stateLists, Finset.mem_image, Finset.mem_product,
      Finset.mem_univ, true_and, ih]
    constructor
    · rintro ⟨⟨p, ss'⟩, hlen, rfl⟩
      simp [hlen]
    · intro h
      cases ss with
      | nil => simp at h
      | cons p ss' =>
        exact ⟨(p, ss'), by simpa using h, rfl⟩

/-- The terminal prefix contributed by an optional input letter. -/
def optTerms (opt : Option T) : List (Symbol T (Option (σ × Γ × σ))) :=
  opt.toList.map Symbol.terminal

/-- The production for one transition popping `γ` in state `p`, moving to
state `r` and pushing `εs`, with `ss` the states after `r` bracketing the
pushed symbols; the last of these states is the target state of the
triple. -/
def stepRule (p : σ) (γ : Γ) (opt : Option T) (r : σ) (εs : List Γ)
    (ss : List σ) : ContextFreeRule T (Option (σ × Γ × σ)) :=
  ⟨some (p, γ, (r :: ss).getLast (List.cons_ne_nil r ss)),
    optTerms opt ++ chainForm εs (r :: ss)⟩

omit [Fintype σ] [Fintype Γ] in
theorem stepRule_input {p : σ} {γ : Γ} {opt : Option T} {r : σ}
    {εs : List Γ} {ss : List σ} :
    (stepRule p γ opt r εs ss).input =
      some (p, γ, (r :: ss).getLast (List.cons_ne_nil r ss)) := rfl

omit [Fintype σ] [Fintype Γ] in
theorem stepRule_output {p : σ} {γ : Γ} {opt : Option T} {r : σ}
    {εs : List Γ} {ss : List σ} :
    (stepRule p γ opt r εs ss).output =
      optTerms opt ++ chainForm εs (r :: ss) := rfl

/-- The triple grammar of a pushdown automaton: nonterminals `none` (the
initial one) and `some (p, γ, q)`, deriving the words that pop `γ` while
going from state `p` to state `q`. Transitions are only used for letters
in `T₀` (plus `ε`-transitions). -/
noncomputable def pdaGrammar (M : PDA T σ Γ) (T₀ : Finset T) :
    ContextFreeGrammar T where
  NT := Option (σ × Γ × σ)
  initial := none
  rules :=
    (Finset.univ.image fun q =>
        (⟨none, [Symbol.nonterminal (some (M.start, M.startStack, q))]⟩ :
          ContextFreeRule T (Option (σ × Γ × σ)))) ∪
      (Finset.univ.biUnion fun p => Finset.univ.biUnion fun γ =>
        (insert none (T₀.image some)).biUnion fun opt =>
          (M.step p opt γ).biUnion fun y =>
            (stateLists y.2.length).image fun ss =>
              stepRule p γ opt y.1 y.2 ss)

theorem pdaGrammar_rules :
    (pdaGrammar M T₀).rules =
      (Finset.univ.image fun q =>
          (⟨none, [Symbol.nonterminal (some (M.start, M.startStack, q))]⟩ :
            ContextFreeRule T (Option (σ × Γ × σ)))) ∪
        (Finset.univ.biUnion fun p => Finset.univ.biUnion fun γ =>
          (insert none (T₀.image some)).biUnion fun opt =>
            (M.step p opt γ).biUnion fun y =>
              (stateLists y.2.length).image fun ss =>
                stepRule p γ opt y.1 y.2 ss) := rfl

/-- The start productions are present. -/
theorem mem_rules_start {q : σ} :
    (⟨none, [Symbol.nonterminal (some (M.start, M.startStack, q))]⟩ :
        ContextFreeRule T (Option (σ × Γ × σ))) ∈
      (pdaGrammar M T₀).rules := by
  refine Finset.mem_union_left _ ?_
  exact Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩

/-- The transition productions are present. -/
theorem mem_rules_step {p : σ} {γ : Γ} {opt : Option T} {r : σ}
    {εs : List Γ} {ss : List σ}
    (hopt : opt = none ∨ ∃ a ∈ T₀, opt = some a)
    (hstep : (r, εs) ∈ M.step p opt γ) (hss : ss.length = εs.length) :
    stepRule p γ opt r εs ss ∈ (pdaGrammar M T₀).rules := by
  have hopt' : opt ∈ insert none (T₀.image some) := by
    cases hopt with
    | inl h => simp [h]
    | inr h =>
      obtain ⟨a, ha, rfl⟩ := h
      simp [ha]
  refine Finset.mem_union_right _ ?_
  refine Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ p, ?_⟩
  refine Finset.mem_biUnion.mpr ⟨γ, Finset.mem_univ γ, ?_⟩
  refine Finset.mem_biUnion.mpr ⟨opt, hopt', ?_⟩
  refine Finset.mem_biUnion.mpr ⟨(r, εs), hstep, ?_⟩
  exact Finset.mem_image.mpr ⟨ss, mem_stateLists.mpr hss, rfl⟩

/-- Every production of the triple grammar is a start production or comes
from a transition. -/
theorem cases_of_mem_rules {r : ContextFreeRule T (Option (σ × Γ × σ))}
    (hr : r ∈ (pdaGrammar M T₀).rules) :
    (∃ q : σ, r = ⟨none,
      [Symbol.nonterminal (some (M.start, M.startStack, q))]⟩) ∨
    (∃ (p : σ) (γ : Γ) (opt : Option T) (r₀ : σ) (εs : List Γ) (ss : List σ),
      (r₀, εs) ∈ M.step p opt γ ∧ ss.length = εs.length ∧
        r = stepRule p γ opt r₀ εs ss) := by
  obtain (h | h) := Finset.mem_union.mp hr
  · obtain ⟨q, -, hq⟩ := Finset.mem_image.mp h
    exact Or.inl ⟨q, hq.symm⟩
  · obtain ⟨p, -, h⟩ := Finset.mem_biUnion.mp h
    obtain ⟨γ, -, h⟩ := Finset.mem_biUnion.mp h
    obtain ⟨opt, -, h⟩ := Finset.mem_biUnion.mp h
    obtain ⟨y, hstep, h⟩ := Finset.mem_biUnion.mp h
    obtain ⟨ss, hss, hr'⟩ := Finset.mem_image.mp h
    exact Or.inr ⟨p, γ, opt, y.1, y.2, ss, hstep, mem_stateLists.mp hss,
      hr'.symm⟩

/-- Forward simulation, generalized over terminal prefixes and chain
forms: a yield of `t ++ chainForm δs ss` splits off the forced terminal
prefix `t`, and the rest is a computation emptying the stack `δs`. -/
private theorem derives_of_yields_aux :
    ∀ {α : List (Symbol T (pdaGrammar M T₀).NT)} {w : List T},
      Yields (pdaGrammar M T₀) α w →
      ∀ (t : List T) (δs : List Γ) (ss : List σ),
        α = t.map Symbol.terminal ++ chainForm δs ss →
        ss.length = δs.length + 1 →
        ∀ {p q : σ}, ss.head? = some p → ss.getLast? = some q →
          ∃ w', w = t ++ w' ∧ M.Derives ⟨p, w', δs⟩ ⟨q, [], []⟩ := by
  intro α w h
  induction h with
  | nil =>
    intro t δs ss hα hlen p q hhead hlast
    have ht : t = [] := by
      cases t with
      | nil => rfl
      | cons b t' => cases hα
    cases δs with
    | nil =>
      cases ss with
      | nil => simp only [List.length_nil] at hlen; omega
      | cons p₀ ss₀ =>
        cases ss₀ with
        | nil =>
          have hp₀ : p₀ = p := Option.some.inj hhead
          have hq₀ : p₀ = q := Option.some.inj hlast
          subst hp₀
          subst hq₀
          exact ⟨[], by simp [ht], Relation.ReflTransGen.refl⟩
        | cons q₀ ss₀ => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons δ δs₀ =>
      cases ss with
      | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons p₀ ss₀ =>
        cases ss₀ with
        | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
        | cons q₀ ss₀ =>
          rw [chainForm_cons_cons, ht] at hα
          cases hα
  | terminal a _ ih =>
    intro t δs ss hα hlen p q hhead hlast
    cases t with
    | nil =>
      exfalso
      have hhead2 : (chainForm δs ss).head? =
          some (Symbol.terminal (N := Option (σ × Γ × σ)) a) :=
        (congrArg List.head? hα).symm
      obtain ⟨tl, htl⟩ := List.head?_eq_some_iff.mp hhead2
      have hmem : Symbol.terminal (N := Option (σ × Γ × σ)) a ∈
          chainForm δs ss := by
        rw [htl]
        exact List.mem_cons.mpr (Or.inl rfl)
      obtain ⟨A, hA⟩ := nonterminal_of_mem_chainForm hmem
      cases hA
    | cons b t' =>
      obtain ⟨hab, hu⟩ := List.cons.inj hα
      obtain rfl : a = b := Symbol.terminal.inj hab
      obtain ⟨w', hw', hder⟩ := ih t' δs ss hu hlen hhead hlast
      exact ⟨w', by simp [hw'], hder⟩
  | nonterminal hr _ _ ihout ihrest =>
    rename_i r u w₁ w₂ hout hrest
    intro t δs ss hα hlen p q hhead hlast
    cases t with
    | cons b t' =>
      exfalso
      cases (List.cons.inj hα).1
    | nil =>
      cases δs with
      | nil =>
        rw [chainForm_nil] at hα
        cases hα
      | cons δ δs₀ =>
        cases ss with
        | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
        | cons p₀ ss₀ =>
          cases ss₀ with
          | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
          | cons m ss₀ =>
            obtain ⟨hinput, hu⟩ := List.cons.inj hα
            have hp₀ : p₀ = p := Option.some.inj hhead
            subst hp₀
            have hlast' : (m :: ss₀).getLast? = some q := by
              rwa [List.getLast?_cons_cons] at hlast
            have hrinput : r.input = some (p₀, δ, m) :=
              Symbol.nonterminal.inj hinput
            obtain (hstart | hstep) := cases_of_mem_rules hr
            · obtain ⟨q', hr'⟩ := hstart
              rw [hr'] at hrinput
              cases hrinput
            · obtain ⟨p₁, γ, opt, r₀, εs, ss', hmem, hss'len, hr'⟩ := hstep
              have hinput2 : (p₀, δ, m) =
                  (p₁, γ, (r₀ :: ss').getLast (List.cons_ne_nil r₀ ss')) := by
                have h1 : r.input = (stepRule p₁ γ opt r₀ εs ss').input := by
                  rw [hr']
                rw [hrinput, stepRule_input] at h1
                exact Option.some.inj h1
              simp only [Prod.mk.injEq] at hinput2
              obtain ⟨rfl, rfl, hm⟩ := hinput2
              have hrout : r.output =
                  optTerms opt ++ chainForm εs (r₀ :: ss') := by
                rw [hr']
                rfl
              have hlastout : (r₀ :: ss').getLast? = some m := by
                rw [List.getLast?_eq_some_getLast (fun h => by cases h)]
                exact congrArg some hm.symm
              obtain ⟨w₁', hw₁, hder₁⟩ := ihout opt.toList εs (r₀ :: ss')
                (by rw [hrout, optTerms])
                (by simp [hss'len]) (p := r₀) (q := m) rfl hlastout
              obtain ⟨w₂', hw₂, hder₂⟩ := ihrest [] δs₀ (m :: ss₀)
                hu
                (by simp only [List.length_cons] at hlen ⊢; omega)
                (p := m) (q := q) rfl hlast'
              obtain rfl : w₂' = w₂ := by simpa using hw₂.symm
              cases opt with
              | none =>
                refine ⟨w₁' ++ w₂', by simp [hw₁], ?_⟩
                exact (Relation.ReflTransGen.single
                    (PDA.Step.epsilon hmem)).trans
                  ((hder₁.append_input_stack w₂' δs₀).trans hder₂)
              | some a =>
                refine ⟨a :: (w₁' ++ w₂'), by simp [hw₁], ?_⟩
                exact (Relation.ReflTransGen.single
                    (PDA.Step.consume hmem)).trans
                  ((hder₁.append_input_stack w₂' δs₀).trans hder₂)

/-- A triple nonterminal yields exactly the words of the corresponding
emptying computations (forward direction). -/
private theorem derives_of_yields_triple {p q : σ} {γ : Γ} {w : List T}
    (h : Yields (pdaGrammar M T₀)
      [Symbol.nonterminal (some (p, γ, q))] w) :
    M.Derives ⟨p, w, [γ]⟩ ⟨q, [], []⟩ := by
  obtain ⟨w', hw', hder⟩ := derives_of_yields_aux h [] [γ] [p, q]
    rfl rfl (p := p) (q := q) rfl rfl
  obtain rfl : w' = w := by simpa using hw'.symm
  exact hder

/-- Backward simulation: every emptying computation is a yield of some
chain form. The hypothesis `hT` says transitions consume only letters
from `T₀`, so the needed transition productions exist. -/
private theorem yields_chain_of_derives
    (hT : ∀ (p : σ) (a : T) (γ : Γ), a ∉ T₀ → M.step p (some a) γ = ∅) :
    ∀ {p q : σ} {w : List T} {δs : List Γ},
      M.Derives ⟨p, w, δs⟩ ⟨q, [], []⟩ →
      ∃ ss : List σ, ss.length = δs.length + 1 ∧ ss.head? = some p ∧
        ss.getLast? = some q ∧
        Yields (pdaGrammar M T₀) (chainForm δs ss) w := by
  intro p q w δs h
  refine Relation.ReflTransGen.head_induction_on
    (motive := fun c _ => ∀ p w δs, c = ⟨p, w, δs⟩ →
      ∃ ss, ss.length = δs.length + 1 ∧ ss.head? = some p ∧
        ss.getLast? = some q ∧
        Yields (pdaGrammar M T₀) (chainForm δs ss) w) h ?_ ?_ p w δs rfl
  · intro p w δs hcfg
    injection hcfg with h1 h2 h3
    subst h1
    subst h2
    subst h3
    exact ⟨[q], rfl, rfl, rfl, Yields.nil⟩
  · intro a c hstep htail ih p w δs ha
    subst ha
    cases hstep with
    | @epsilon p r w δ δs₀ εs hmem =>
      obtain ⟨ss', hlen', hhead', hlast', hY⟩ := ih r w (εs ++ δs₀) rfl
      obtain ⟨ss₁, ss₂, m, h1len, h2len, h1head, h1last, h2head, h2last,
        hsplit⟩ := chainForm_append_split εs δs₀ ss' hlen' hhead' hlast'
      rw [hsplit] at hY
      obtain ⟨w₁, w₂, hw, hY₁, hY₂⟩ := Yields.append_inv hY
      obtain ⟨ss₁t, rfl⟩ := List.head?_eq_some_iff.mp h1head
      obtain ⟨ss₂t, rfl⟩ := List.head?_eq_some_iff.mp h2head
      have hm : (r :: ss₁t).getLast (List.cons_ne_nil r ss₁t) = m := by
        have hsome : some ((r :: ss₁t).getLast (List.cons_ne_nil r ss₁t)) =
            some m := by
          rw [← List.getLast?_eq_some_getLast]
          exact h1last
        exact Option.some.inj hsome
      have hr : stepRule p δ none r εs ss₁t ∈ (pdaGrammar M T₀).rules :=
        mem_rules_step (Or.inl rfl) hmem (by
          rw [List.length_cons] at h1len
          omega)
      have htriple :
          Yields (pdaGrammar M T₀)
            [Symbol.nonterminal (some (p, δ, m))] w₁ := by
        have h0 := yields_of_rule hr hY₁
        rwa [stepRule_input, hm] at h0
      refine ⟨p :: m :: ss₂t, by
        simp only [List.length_cons] at h2len ⊢; omega, rfl, by
        rwa [List.getLast?_cons_cons], ?_⟩
      rw [chainForm_cons_cons, hw]
      exact htriple.append hY₂
    | @consume p r a w₀ δ δs₀ εs hmem =>
      obtain ⟨ss', hlen', hhead', hlast', hY⟩ := ih r w₀ (εs ++ δs₀) rfl
      obtain ⟨ss₁, ss₂, m, h1len, h2len, h1head, h1last, h2head, h2last,
        hsplit⟩ := chainForm_append_split εs δs₀ ss' hlen' hhead' hlast'
      rw [hsplit] at hY
      obtain ⟨w₁, w₂, hw, hY₁, hY₂⟩ := Yields.append_inv hY
      obtain ⟨ss₁t, rfl⟩ := List.head?_eq_some_iff.mp h1head
      obtain ⟨ss₂t, rfl⟩ := List.head?_eq_some_iff.mp h2head
      have hm : (r :: ss₁t).getLast (List.cons_ne_nil r ss₁t) = m := by
        have hsome : some ((r :: ss₁t).getLast (List.cons_ne_nil r ss₁t)) =
            some m := by
          rw [← List.getLast?_eq_some_getLast]
          exact h1last
        exact Option.some.inj hsome
      have ha : a ∈ T₀ := by
        by_contra ha
        rw [hT p a δ ha] at hmem
        simp at hmem
      have hr : stepRule p δ (some a) r εs ss₁t ∈ (pdaGrammar M T₀).rules :=
        mem_rules_step (Or.inr ⟨a, ha, rfl⟩) hmem (by
          rw [List.length_cons] at h1len
          omega)
      have htriple :
          Yields (pdaGrammar M T₀)
            [Symbol.nonterminal (some (p, δ, m))] (a :: w₁) := by
        have h0 := yields_of_rule hr (Yields.terminal a hY₁)
        rwa [stepRule_input, hm] at h0
      refine ⟨p :: m :: ss₂t, by
        simp only [List.length_cons] at h2len ⊢; omega, rfl, by
        rwa [List.getLast?_cons_cons], ?_⟩
      rw [chainForm_cons_cons, hw]
      exact htriple.append hY₂

/-- A triple nonterminal yields exactly the words of the corresponding
emptying computations (backward direction). -/
private theorem yields_triple_of_derives
    (hT : ∀ (p : σ) (a : T) (γ : Γ), a ∉ T₀ → M.step p (some a) γ = ∅)
    {p q : σ} {γ : Γ} {w : List T}
    (h : M.Derives ⟨p, w, [γ]⟩ ⟨q, [], []⟩) :
    Yields (pdaGrammar M T₀) [Symbol.nonterminal (some (p, γ, q))] w := by
  obtain ⟨ss, hlen, hhead, hlast, hY⟩ := yields_chain_of_derives hT h
  cases ss with
  | nil => simp at hlen
  | cons b ss₀ =>
    cases ss₀ with
    | nil => simp at hlen
    | cons c ss₀ =>
      cases ss₀ with
      | nil =>
        have hb : b = p := Option.some.inj hhead
        have hc : c = q := Option.some.inj hlast
        subst hb
        subst hc
        rwa [chainForm_cons_cons, chainForm_nil] at hY
      | cons d ss₀ => simp at hlen

/-- Inversion for yields from a single nonterminal. -/
private theorem exists_of_yields_single {A : (pdaGrammar M T₀).NT}
    {w : List T}
    (h : Yields (pdaGrammar M T₀) [Symbol.nonterminal A] w) :
    ∃ r : ContextFreeRule T (Option (σ × Γ × σ)),
      r ∈ (pdaGrammar M T₀).rules ∧ r.input = A ∧
        Yields (pdaGrammar M T₀) r.output w := by
  cases h with
  | nonterminal hr hout hrest =>
    cases hrest
    exact ⟨_, hr, rfl, by simpa using hout⟩

/-- The triple grammar generates exactly the language accepted by `M`. -/
theorem PDA.pdaGrammar_language
    (hT : ∀ (p : σ) (a : T) (γ : Γ), a ∉ T₀ → M.step p (some a) γ = ∅) :
    (pdaGrammar M T₀).language = M.accepts := by
  ext w
  constructor
  · intro hw
    obtain ⟨r, hr, hrinput, hout⟩ :=
      exists_of_yields_single (mem_language_iff_yields.mp hw)
    obtain (hstart | hstep) := cases_of_mem_rules hr
    · obtain ⟨q, hr'⟩ := hstart
      rw [hr'] at hout
      exact ⟨q, derives_of_yields_triple hout⟩
    · obtain ⟨p, γ, opt, r₀, εs, ss, -, -, hr'⟩ := hstep
      have hnone : r.input = none := hrinput
      rw [hr', stepRule_input] at hnone
      cases hnone
  · intro hw
    rw [PDA.mem_accepts] at hw
    obtain ⟨q, hder⟩ := hw
    apply mem_language_iff_yields.mpr
    exact yields_of_rule mem_rules_start (yields_triple_of_derives hT hder)

omit [Fintype σ] [Fintype Γ] in
/-- Languages accepted by finite pushdown automata (with transitions
consuming letters from a finite set) are context-free. -/
theorem PDA.isContextFree_accepts [Finite σ] [Finite Γ]
    (hT : ∀ (p : σ) (a : T) (γ : Γ), a ∉ T₀ → M.step p (some a) γ = ∅) :
    M.accepts.IsContextFree := by
  have : Fintype σ := Fintype.ofFinite σ
  have : Fintype Γ := Fintype.ofFinite Γ
  exact ⟨pdaGrammar M T₀, PDA.pdaGrammar_language hT⟩

/-- Over an alphabet in `Type`, the context-free languages are exactly
the languages accepted by empty stack by finite pushdown automata whose
transitions consume letters from a finite set. -/
theorem isContextFree_iff_exists_pda_accepts {T : Type} {L : Language T} :
    L.IsContextFree ↔ ∃ (σ Γ : Type) (_ : Fintype σ) (_ : Fintype Γ)
      (M : PDA T σ Γ),
      (∃ T₀ : Finset T, ∀ (p : σ) (a : T) (γ : Γ), a ∉ T₀ →
        M.step p (some a) γ = ∅) ∧ M.accepts = L := by
  constructor
  · intro hL
    obtain ⟨g, rfl⟩ := hL
    classical
    let Γ₀ : Finset (Symbol T g.NT) :=
      insert (Symbol.nonterminal g.initial)
        (g.rules.biUnion fun r => r.output.toFinset)
    have hstart : (cfgPDA g).startStack ∈ Γ₀ :=
      Finset.mem_insert_self _ _
    have hclosed : (cfgPDA g).ClosedUnder Γ₀ := by
      intro q opt γ hγ y hy γ' hγ'
      cases q
      have hy' : y ∈ cfgStep g () opt γ := hy
      cases opt with
      | none =>
        cases γ with
        | terminal b => simp [cfgStep] at hy'
        | nonterminal A =>
          obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hy'
          exact Finset.mem_insert_of_mem
            (Finset.mem_biUnion.mpr
              ⟨r, (Finset.mem_filter.mp hr).1, List.mem_toFinset.mpr hγ'⟩)
      | some a =>
        cases γ with
        | nonterminal A => simp [cfgStep] at hy'
        | terminal b =>
          simp only [cfgStep] at hy'
          split at hy'
          swap
          · simp at hy'
          rename_i hab
          subst hab
          obtain rfl : y = ((), []) := Finset.mem_singleton.mp hy'
          exact absurd hγ' List.not_mem_nil
    refine ⟨Unit, {γ // γ ∈ Γ₀}, inferInstance, inferInstance,
      (cfgPDA g).restrict Γ₀ hstart hclosed, ⟨?_ , ?_⟩, ?_⟩
    · exact g.rules.biUnion fun r =>
        (r.output.filterMap fun s => match s with
          | Symbol.terminal a => some a
          | Symbol.nonterminal _ => none).toFinset
    · intro p a γ ha
      obtain ⟨γ₁, hγ₁⟩ := γ
      cases p
      ext y
      simp only [Finset.notMem_empty, iff_false]
      intro hy
      obtain ⟨pushed, hmem, -⟩ := PDA.mem_restrict_step.mp hy
      have hmem' : (y.1, pushed) ∈ cfgStep g () (some a) γ₁ := hmem
      cases γ₁ with
      | nonterminal A => simp [cfgStep] at hmem'
      | terminal b =>
        simp only [cfgStep] at hmem'
        split at hmem'
        · rename_i hab
          subst hab
          cases Finset.mem_insert.mp hγ₁ with
          | inl heq => cases heq
          | inr hmemΓ₀ =>
            obtain ⟨r, hr, hrout⟩ := Finset.mem_biUnion.mp hmemΓ₀
            exact ha (Finset.mem_biUnion.mpr ⟨r, hr,
              List.mem_toFinset.mpr (List.mem_filterMap.mpr
                ⟨Symbol.terminal a, List.mem_toFinset.mp hrout, rfl⟩)⟩)
        · simp at hmem'
    · rw [PDA.accepts_restrict, ContextFreeGrammar.cfgPDA_accepts]
  · rintro ⟨σ, Γ, hσ, hΓ, M, ⟨T₀, hT⟩, rfl⟩
    have := hσ
    have := hΓ
    exact PDA.isContextFree_accepts (M := M) (T₀ := T₀) hT

end Cslib.Language
