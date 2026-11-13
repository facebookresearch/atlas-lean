/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.Yields
public import Mathlib.Data.Finset.Union

/-!
# Reduced grammars: eliminating `ε`-productions and unit productions

Every context-free grammar can be put in reduced form at the cost of
losing the empty word: first delete nullable nonterminals from
right-hand sides in all possible ways (`epsGrammar`), then lift
non-unit productions along chains of unit productions (`unitGrammar`).
The resulting grammar has no empty output and no output consisting of
a single nonterminal, so every nonterminal yields only nonempty words;
this is the starting point for the pumping lemma and for Chomsky
normal form.

## Main definitions

* `Cslib.Language.Nullable`: a nonterminal deriving the empty word.
* `Cslib.Language.epsGrammar`, `Cslib.Language.unitGrammar`: the two
  eliminating constructions.
* `Cslib.Language.UnitSteps`: reachability by unit productions.
* `Cslib.Language.IsReduced`: grammars with no empty or unit output.

## Main results

* `Cslib.Language.epsGrammar_language`: `epsGrammar` generates the
  original language minus the empty word.
* `Cslib.Language.unitGrammar_language`: `unitGrammar` generates the
  original language.
* `Cslib.Language.exists_reduced_grammar`: every grammar has a reduced
  grammar for its language minus the empty word.
-/

@[expose] public section

namespace Cslib.Language

attribute [local instance] Classical.propDecidable

variable {T : Type*} {g : ContextFreeGrammar T}

private theorem mul_le_mul_of_le {a b c d : Language T} (hac : a ≤ c)
    (hbd : b ≤ d) : a * b ≤ c * d := by
  intro w hw
  obtain ⟨x, hx, y, hy, hxy⟩ := Language.mem_mul.mp hw
  exact Language.mem_mul.mpr ⟨x, hac hx, y, hbd hy, hxy⟩

/-- **No empty words without empty productions.** In a context-free grammar in which no
production has an empty right-hand side, every nonempty sentential form yields only nonempty
words. -/
theorem Yields.ne_nil_of_forall_output_ne_nil {G : ContextFreeGrammar T}
    (hG : ∀ r ∈ G.rules, r.output ≠ []) :
    ∀ {α : List (Symbol T G.NT)} {w : List T}, Yields G α w → α ≠ [] →
      w ≠ [] := by
  intro α w h
  induction h with
  | nil => intro hα; exact absurd rfl hα
  | terminal a _ _ => exact fun _ => List.cons_ne_nil a _
  | nonterminal hr _ _ ihout _ =>
    intro _
    have h1 := ihout (hG _ hr)
    exact fun hw => h1 (List.append_eq_nil_iff.mp hw).1

/-- **Nullable nonterminal.** A nonterminal $A$ of a context-free grammar $g$ is nullable when $g$
derives the empty word from $A$. -/
def Nullable (g : ContextFreeGrammar T) (A : g.NT) :
    Prop :=
  [] ∈ languageFrom g A

theorem nullable_of_yields {A : g.NT}
    (h : Yields g [Symbol.nonterminal A] []) : Nullable g A :=
  mem_languageFrom.mpr (yields_iff_derives.mp h)

theorem yields_of_nullable {A : g.NT}
    (h : Nullable g A) : Yields g [Symbol.nonterminal A] [] :=
  yields_iff_derives.mpr (mem_languageFrom.mp h)

/-- **Nullable deletions.** For a context-free grammar $g$ and a sentential form $u$, the nullable
deletions of $u$ are the forms obtained from $u$ by deleting any selection of occurrences of
nullable nonterminals, possibly none and possibly all, keeping the remaining symbols in order.
They form a finite set. -/
noncomputable def nullableDeletions (g : ContextFreeGrammar T) :
    List (Symbol T g.NT) → Finset (List (Symbol T g.NT))
  | [] => {[]}
  | Symbol.terminal a :: u =>
    (nullableDeletions g u).image (Symbol.terminal a :: ·)
  | Symbol.nonterminal A :: u =>
    (nullableDeletions g u).image (Symbol.nonterminal A :: ·) ∪
      (if Nullable g A then nullableDeletions g u else ∅)

theorem mem_nullableDeletions_cons_terminal {a : T}
    {u α₀ : List (Symbol T g.NT)} (h : α₀ ∈ nullableDeletions g u) :
    Symbol.terminal a :: α₀ ∈
      nullableDeletions g (Symbol.terminal a :: u) :=
  Finset.mem_image.mpr ⟨α₀, h, rfl⟩

theorem mem_nullableDeletions_cons_nonterminal_keep {A : g.NT}
    {u α₀ : List (Symbol T g.NT)} (h : α₀ ∈ nullableDeletions g u) :
    Symbol.nonterminal A :: α₀ ∈
      nullableDeletions g (Symbol.nonterminal A :: u) :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨α₀, h, rfl⟩)

theorem mem_nullableDeletions_cons_nonterminal_delete {A : g.NT}
    (hA : Nullable g A) {u α₀ : List (Symbol T g.NT)}
    (h : α₀ ∈ nullableDeletions g u) :
    α₀ ∈ nullableDeletions g (Symbol.nonterminal A :: u) :=
  Finset.mem_union_right _ (by rw [ite_eq_left hA]; exact h)

/-- **Deleting nullable nonterminals shrinks the denoted language.** Let $g$ be a context-free
grammar and $V$ an assignment of a language $V(A)$ to each nonterminal $A$ of $g$ such that the
empty word belongs to $V(A)$ whenever $A$ is nullable (derives the empty word in $g$). If a
sentential form $\alpha'$ is obtained from a sentential form $u$ by deleting some occurrences of
nullable nonterminals, then the language denoted by $\alpha'$ under $V$ is contained in the
language denoted by $u$ under $V$. -/
theorem evalForm_le_of_mem_nullableDeletions {V : g.NT → Language T}
    (hV : ∀ A, Nullable g A → [] ∈ V A) :
    ∀ {u α' : List (Symbol T g.NT)}, α' ∈ nullableDeletions g u →
      evalForm V α' ≤ evalForm V u := by
  intro u
  induction u with
  | nil =>
    intro α' hα'
    rw [Finset.mem_singleton.mp hα']
  | cons s u ih =>
    intro α' hα'
    cases s with
    | terminal a =>
      obtain ⟨α₀, hα₀, rfl⟩ := Finset.mem_image.mp hα'
      exact mul_le_mul_of_le le_rfl (ih hα₀)
    | nonterminal A =>
      cases Finset.mem_union.mp hα' with
      | inl h =>
        obtain ⟨α₀, hα₀, rfl⟩ := Finset.mem_image.mp h
        exact mul_le_mul_of_le le_rfl (ih hα₀)
      | inr h =>
        by_cases hA : Nullable g A
        · rw [ite_eq_left hA] at h
          refine le_trans (ih h) ?_
          intro w hw
          rw [evalForm_cons, evalSymbol_nonterminal]
          exact Language.mem_mul.mpr ⟨[], hV A hA, w, hw, rfl⟩
        · rw [ite_eq_right hA] at h
          exact absurd h (Finset.notMem_empty α')

/-- **Elimination of $\varepsilon$-productions.** For a context-free grammar $g$, the grammar
obtained from $g$ by eliminating $\varepsilon$-productions has the same nonterminals and the
same initial nonterminal as $g$. Its productions are the productions $A \to \alpha'$ such that
$g$ has a production $A \to \alpha$, the form $\alpha'$ is obtained from $\alpha$ by deleting
some (possibly no) occurrences of nullable nonterminals (those deriving the empty word in $g$),
and $\alpha'$ is nonempty. -/
noncomputable def epsGrammar (g : ContextFreeGrammar T) :
    ContextFreeGrammar T where
  NT := g.NT
  initial := g.initial
  rules := g.rules.biUnion fun r =>
    ((nullableDeletions g r.output).filter (· ≠ [])).image
      (fun α => ⟨r.input, α⟩)

/-- **Productions of the ε-free grammar.** Let $g$ be a context-free grammar with a production
$A \to u$, and let $\alpha$ be a nonempty form obtained from $u$ by deleting some (possibly no)
occurrences of nullable nonterminals. Then $A \to \alpha$ is a production of the grammar obtained
from $g$ by eliminating ε-productions. -/
theorem mem_epsGrammar_rules {A : g.NT} {u α : List (Symbol T g.NT)}
    (hr : (⟨A, u⟩ : ContextFreeRule T g.NT) ∈ g.rules)
    (hα : α ∈ nullableDeletions g u) (hne : α ≠ []) :
    (⟨A, α⟩ : ContextFreeRule T g.NT) ∈ (epsGrammar g).rules :=
  Finset.mem_biUnion.mpr ⟨⟨A, u⟩, hr,
    Finset.mem_image.mpr ⟨α, Finset.mem_filter.mpr ⟨hα, hne⟩, rfl⟩⟩

/-- **Productions of the $\varepsilon$-eliminated grammar come from productions of $g$.**
Let $g$ be a context-free grammar. Every production $A \to \alpha'$ of the grammar obtained
from $g$ by eliminating $\varepsilon$-productions arises from a production $A \to \alpha$ of $g$
with the same left-hand side $A$, such that $\alpha'$ is obtained from $\alpha$ by deleting some
occurrences of nullable nonterminals and $\alpha'$ is nonempty. -/
theorem cases_of_mem_epsGrammar_rules {r' : ContextFreeRule T g.NT}
    (hr : r' ∈ (epsGrammar g).rules) :
    ∃ r ∈ g.rules, r'.input = r.input ∧ r'.output ∈ nullableDeletions g r.output ∧
      r'.output ≠ [] := by
  obtain ⟨r, hrules, h⟩ := Finset.mem_biUnion.mp hr
  obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp h
  obtain ⟨hdel, hne⟩ := Finset.mem_filter.mp hα
  exact ⟨r, hrules, rfl, hdel, hne⟩

/-- **The $\varepsilon$-eliminated grammar has no empty productions.** For a context-free
grammar $g$, no production of the grammar obtained from $g$ by eliminating
$\varepsilon$-productions has empty right-hand side. -/
theorem epsGrammar_output_ne_nil {r : ContextFreeRule T (epsGrammar g).NT}
    (hr : r ∈ (epsGrammar g).rules) : r.output ≠ [] := by
  obtain ⟨-, -, -, -, hne⟩ := cases_of_mem_epsGrammar_rules hr
  exact hne

/-- **Soundness of ε-production elimination.** Let $g$ be a context-free grammar and, for each
nonterminal $A$, let $L_g(A)$ be the language of words $g$ derives from $A$. Then $L_g$ is a
valuation of the grammar obtained from $g$ by eliminating ε-productions: for every production
$A \to \alpha$ of that grammar, the language of $\alpha$ under $L_g$ (the concatenation of the
languages of its symbols, a terminal $a$ denoting $\{a\}$) is contained in $L_g(A)$. -/
theorem isValuation_epsGrammar :
    IsValuation (epsGrammar g) (languageFrom g) := by
  intro r' hr'
  obtain ⟨r, hr, hinput, hdel, -⟩ := cases_of_mem_epsGrammar_rules hr'
  rw [hinput]
  exact le_trans
    (evalForm_le_of_mem_nullableDeletions (fun A hA => hA) hdel)
    (isValuation_languageFrom r hr)

/-- **Completeness of eliminating empty productions.** Let $g$ be a context-free grammar.
If a sentential form $\alpha$ of $g$ yields a terminal word $w$ in $g$, then some form
$\alpha'$ obtained from $\alpha$ by deleting some occurrences of nullable nonterminals
yields $w$ in the grammar obtained from $g$ by eliminating $\varepsilon$-productions, and
$w$ is empty if $\alpha'$ is empty. -/
theorem yields_epsGrammar_of_yields :
    ∀ {α : List (Symbol T g.NT)} {w : List T}, Yields g α w →
      ∃ α' ∈ nullableDeletions g α, Yields (epsGrammar g) α' w ∧
        (α' = [] → w = []) := by
  intro α w h
  induction h with
  | nil => exact ⟨[], Finset.mem_singleton_self [], Yields.nil, fun _ => rfl⟩
  | terminal a _ ih =>
    obtain ⟨α', hα', hY, -⟩ := ih
    exact ⟨Symbol.terminal a :: α',
      mem_nullableDeletions_cons_terminal hα', Yields.terminal a hY,
      fun hcon => (List.cons_ne_nil _ _ hcon).elim⟩
  | nonterminal hr hout hrest ihout ihrest =>
    rename_i r u w₁ w₂
    obtain ⟨β, hβ, hYβ, hβw⟩ := ihout
    obtain ⟨α', hα', hYα, hαw⟩ := ihrest
    by_cases hβ0 : β = []
    · subst hβ0
      have hw₁ : w₁ = [] := hβw rfl
      have hnull : Nullable g r.input :=
        nullable_of_yields
          (hw₁ ▸ yields_of_rule hr hout)
      refine ⟨α', mem_nullableDeletions_cons_nonterminal_delete hnull hα',
        ?_, fun hα'' => by rw [hw₁, hαw hα'']; rfl⟩
      rw [hw₁, List.nil_append]
      exact hYα
    · exact ⟨Symbol.nonterminal r.input :: α',
        mem_nullableDeletions_cons_nonterminal_keep hα',
        Yields.nonterminal (mem_epsGrammar_rules hr hβ hβ0) hYβ hYα,
        fun hcon => (List.cons_ne_nil _ _ hcon).elim⟩

/-- **The $\varepsilon$-eliminated grammar generates the nonempty words of $g$.** For a
context-free grammar $g$ and every word $w$ over its terminals, $w$ is generated by the grammar
obtained from $g$ by eliminating $\varepsilon$-productions if and only if $w$ is generated by
$g$ and $w$ is nonempty. -/
theorem epsGrammar_language {w : List T} :
    w ∈ (epsGrammar g).language ↔ w ∈ g.language ∧ w ≠ [] := by
  constructor
  · intro hw
    have hY : Yields (epsGrammar g)
        [Symbol.nonterminal (epsGrammar g).initial] w :=
      mem_language_iff_yields.mp hw
    have hne : w ≠ [] :=
      Yields.ne_nil_of_forall_output_ne_nil (G := epsGrammar g)
        (fun _ hr => epsGrammar_output_ne_nil (g := g) hr) hY (by simp)
    have hle : w ∈ languageFrom g (epsGrammar g).initial :=
      language_le_of_valuation (g := epsGrammar g) isValuation_epsGrammar hw
    change w ∈ languageFrom g g.initial at hle
    rw [languageFrom_initial] at hle
    exact ⟨hle, hne⟩
  · rintro ⟨hw, hne⟩
    obtain ⟨α', hα', hY, hαw⟩ :=
      yields_epsGrammar_of_yields (mem_language_iff_yields.mp hw)
    have hα'ne : α' ≠ [] := fun h => hne (hαw h)
    apply mem_language_iff_yields.mpr
    have hcases : α' = [Symbol.nonterminal g.initial] ∨ α' = [] := by
      refine (Finset.mem_union.mp hα').elim (fun h => ?_) (fun h => ?_)
      · obtain ⟨α₀, hα₀, rfl⟩ := Finset.mem_image.mp h
        exact Or.inl (by rw [Finset.mem_singleton.mp hα₀])
      · by_cases hnull : Nullable g g.initial
        · rw [ite_eq_left hnull] at h
          exact Or.inr (Finset.mem_singleton.mp h)
        · rw [ite_eq_right hnull] at h
          exact absurd h (Finset.notMem_empty α')
    cases hcases with
    | inl h => rwa [h] at hY
    | inr h => exact absurd h hα'ne

/-- **Reachability by unit productions.** Let $g$ be a context-free grammar. A nonterminal
$A$ of $g$ reaches a nonterminal $B$ by unit productions when there is a chain
$A = A_0, A_1, \dots, A_n = B$ with $n \ge 0$ such that each $A_{i-1} \to A_i$ is a
production of $g$. In particular, every nonterminal reaches itself. -/
def UnitSteps (g : ContextFreeGrammar T) : g.NT → g.NT → Prop :=
  Relation.ReflTransGen
    (fun A B => (⟨A, [Symbol.nonterminal B]⟩ : ContextFreeRule T g.NT) ∈
      g.rules)

/-- **Unit output.** A sentential form is a unit output when it consists of a single
nonterminal. -/
def IsUnitOutput {N : Type*} (α : List (Symbol T N)) : Prop :=
  ∃ B, α = [Symbol.nonterminal B]

/-- **Nonterminals of a sentential form.** For a sentential form $u$, a finite word of terminal
and nonterminal symbols, the nonterminals of $u$ form the finite set of all nonterminals that
occur in $u$. -/
noncomputable def formNTs {N : Type*} (u : List (Symbol T N)) : Finset N :=
  (u.filterMap fun s => match s with
    | Symbol.terminal _ => none
    | Symbol.nonterminal A => some A).toFinset

theorem mem_formNTs {N : Type*} {A : N} {u : List (Symbol T N)} :
    A ∈ formNTs u ↔ Symbol.nonterminal A ∈ u := by
  simp only [formNTs, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨s, hs, hsopt⟩
    cases s with
    | terminal a => cases hsopt
    | nonterminal B =>
      have hBA : B = A := Option.some.inj hsopt
      rwa [hBA] at hs
  · intro h
    exact ⟨Symbol.nonterminal A, h, rfl⟩

/-- **Set of nonterminals mentioned by a grammar.** The nonterminals mentioned by a context-free
grammar $g$ form the finite set consisting of the initial nonterminal of $g$, the left-hand side
of every production of $g$, and every nonterminal occurring in the right-hand side of a
production of $g$. -/
noncomputable def grammarNTs (g : ContextFreeGrammar T) : Finset g.NT :=
  insert g.initial
    (g.rules.biUnion fun r => insert r.input (formNTs r.output))

theorem initial_mem_grammarNTs : g.initial ∈ grammarNTs g :=
  Finset.mem_insert_self _ _

theorem mem_grammarNTs_of_rule_input {r : ContextFreeRule T g.NT}
    (hr : r ∈ g.rules) : r.input ∈ grammarNTs g :=
  Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
    ⟨r, hr, Finset.mem_insert_self _ _⟩)

theorem mem_grammarNTs_of_mem_output {A : g.NT}
    {r : ContextFreeRule T g.NT} (hr : r ∈ g.rules)
    (hA : Symbol.nonterminal A ∈ r.output) : A ∈ grammarNTs g :=
  Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
    ⟨r, hr, Finset.mem_insert_of_mem (mem_formNTs.mpr hA)⟩)

/-- **Unit chains start at mentioned nonterminals.** Let $g$ be a context-free grammar and let $B$
be reachable from $A$ by a chain of zero or more unit productions of $g$. If $B$ is the left-hand
side of some production of $g$, then $A$ is among the nonterminals mentioned by $g$ (its initial
nonterminal, the left-hand sides of its productions, and the nonterminals in their right-hand
sides). -/
theorem mem_grammarNTs_of_unitSteps {A B : g.NT}
    (hsteps : UnitSteps g A B)
    (hB : ∃ α, (⟨B, α⟩ : ContextFreeRule T g.NT) ∈ g.rules) :
    A ∈ grammarNTs g := by
  induction hsteps with
  | refl =>
    obtain ⟨α, hα⟩ := hB
    exact mem_grammarNTs_of_rule_input hα
  | tail _ hstep ih => exact ih ⟨_, hstep⟩

/-- **Eliminating unit productions.** A unit production is one whose output is a single
nonterminal. For a context-free grammar $g$, the grammar obtained by eliminating unit
productions has the same nonterminals and the same start symbol as $g$. Its productions
are the $A \to \alpha$ such that $A$ is a nonterminal mentioned by $g$ (its start symbol
or one occurring in a production of $g$), $g$ has a production $B \to \alpha$ that is not
a unit production, and $A$ reaches $B$ by a chain of zero or more unit productions of $g$. -/
noncomputable def unitGrammar (g : ContextFreeGrammar T) :
    ContextFreeGrammar T where
  NT := g.NT
  initial := g.initial
  rules := (grammarNTs g).biUnion fun A => (grammarNTs g).biUnion fun B =>
    (g.rules.filter fun r =>
      r.input = B ∧ ¬ IsUnitOutput r.output ∧ UnitSteps g A B).image
        (fun r => ⟨A, r.output⟩)

/-- **Productions of the unit-free grammar.** Let $g$ be a context-free grammar, let $B$ be
reachable from $A$ by a chain of zero or more unit productions of $g$, and let $B \to \beta$ be a
production of $g$ whose right-hand side $\beta$ is not a single nonterminal. If $A$ is among the
nonterminals mentioned by $g$, then $A \to \beta$ is a production of the grammar obtained from
$g$ by eliminating unit productions. -/
theorem mem_unitGrammar_rules {A B : g.NT} {r : ContextFreeRule T g.NT}
    (hsteps : UnitSteps g A B) (hr : r ∈ g.rules) (hinput : r.input = B)
    (hunit : ¬ IsUnitOutput r.output) (hA : A ∈ grammarNTs g) :
    (⟨A, r.output⟩ : ContextFreeRule T g.NT) ∈ (unitGrammar g).rules :=
  Finset.mem_biUnion.mpr ⟨A, hA, Finset.mem_biUnion.mpr
    ⟨B, hinput ▸ mem_grammarNTs_of_rule_input hr,
      Finset.mem_image.mpr ⟨r,
        Finset.mem_filter.mpr ⟨hr, hinput, hunit, hsteps⟩, rfl⟩⟩⟩

/-- **Productions of the unit-eliminated grammar come from non-unit productions of $g$.**
Let $g$ be a context-free grammar. For every production $A \to \beta$ of the grammar obtained
from $g$ by eliminating unit productions, there are a nonterminal $B$ and a production
$B \to \beta$ of $g$ such that $\beta$ is not a single nonterminal and $B$ is reachable from $A$
by a possibly empty chain of unit productions of $g$. -/
theorem cases_of_mem_unitGrammar_rules {r' : ContextFreeRule T g.NT}
    (hr : r' ∈ (unitGrammar g).rules) :
    ∃ (B : g.NT) (r : ContextFreeRule T g.NT), r ∈ g.rules ∧
      r.input = B ∧ ¬ IsUnitOutput r.output ∧ UnitSteps g r'.input B ∧
      r'.output = r.output := by
  obtain ⟨A, -, h⟩ := Finset.mem_biUnion.mp hr
  obtain ⟨B, -, h⟩ := Finset.mem_biUnion.mp h
  obtain ⟨r, hf, rfl⟩ := Finset.mem_image.mp h
  obtain ⟨hrules, hinput, hunit, hsteps⟩ := Finset.mem_filter.mp hf
  exact ⟨B, r, hrules, hinput, hunit, hsteps, rfl⟩

/-- **Eliminating unit productions leaves no unit production.** For every context-free
grammar $g$, no production of the grammar obtained from $g$ by eliminating unit
productions has an output consisting of a single nonterminal. -/
theorem unitGrammar_not_isUnitOutput {r : ContextFreeRule T g.NT}
    (hr : r ∈ (unitGrammar g).rules) : ¬ IsUnitOutput r.output := by
  obtain ⟨B, r₀, -, -, hunit, -, hout⟩ := cases_of_mem_unitGrammar_rules hr
  rw [hout]
  exact hunit

/-- **Eliminating unit productions creates no new outputs.** Let $g$ be a context-free
grammar. For every production of the grammar obtained from $g$ by eliminating unit
productions, some production of $g$ has the same output.

In particular, empty outputs are not created. -/
theorem unitGrammar_output_of_mem {r' : ContextFreeRule T g.NT}
    (hr : r' ∈ (unitGrammar g).rules) :
    ∃ r ∈ g.rules, r.output = r'.output := by
  obtain ⟨-, r, hr, -, -, -, hout⟩ := cases_of_mem_unitGrammar_rules hr
  exact ⟨r, hr, hout.symm⟩

/-- **Languages along unit chains.** Let $g$ be a context-free grammar and, for each nonterminal
$A$, let $L_g(A)$ be the language of words $g$ derives from $A$. If $B$ is reachable from $A$ by
a chain of zero or more unit productions $A \to A_1 \to \dots \to B$ of $g$, then
$L_g(B) \subseteq L_g(A)$. -/
theorem languageFrom_le_of_unitSteps {A B : g.NT}
    (hsteps : UnitSteps g A B) : languageFrom g B ≤ languageFrom g A := by
  induction hsteps with
  | refl => exact le_rfl
  | tail _ hstep ih =>
    refine le_trans ?_ ih
    have h := isValuation_languageFrom _ hstep
    simpa using h

/-- **Soundness of unit-production elimination.** Let $g$ be a context-free grammar and, for
each nonterminal $A$, let $L_g(A)$ be the language of words $g$ derives from $A$. Then $L_g$ is a
valuation of the grammar obtained from $g$ by eliminating unit productions: for every production
$A \to \alpha$ of that grammar, the language of $\alpha$ under $L_g$ (the concatenation of the
languages of its symbols, a terminal $a$ denoting $\{a\}$) is contained in $L_g(A)$. -/
theorem isValuation_unitGrammar :
    IsValuation (unitGrammar g) (languageFrom g) := by
  intro r' hr'
  obtain ⟨B, r, hr, hinput, -, hsteps, hout⟩ :=
    cases_of_mem_unitGrammar_rules hr'
  rw [hout]
  exact le_trans (hinput ▸ isValuation_languageFrom r hr)
    (languageFrom_le_of_unitSteps hsteps)

/-- A single unit step from a rule in the grammar. -/
private theorem unitSteps_single {r : ContextFreeRule T g.NT} {B : g.NT}
    (hr : r ∈ g.rules) (hout : r.output = [Symbol.nonterminal B]) :
    UnitSteps g r.input B :=
  Relation.ReflTransGen.single (by
    have hrw : r = ⟨r.input, [Symbol.nonterminal B]⟩ := by
      cases r with
      | mk i o => congr 1
    rwa [hrw] at hr)

/-- Completeness of `unitGrammar`: every yield of `g` is a yield of
`unitGrammar`, and yields from a single nonterminal transfer along unit
chains. Both statements are proved together by induction on `Yields`. -/
private theorem yields_unitGrammar_of_yields_aux :
    ∀ {α : List (Symbol T g.NT)} {w : List T}, Yields g α w →
      Yields (unitGrammar g) α w ∧
        (∀ B, α = [Symbol.nonterminal B] → ∀ A, UnitSteps g A B →
          Yields (unitGrammar g) [Symbol.nonterminal A] w) := by
  intro α w h
  induction h with
  | nil =>
    exact ⟨Yields.nil, fun B hB => by cases hB⟩
  | terminal a _ ih =>
    refine ⟨Yields.terminal a ih.1, ?_⟩
    intro B hB A _
    cases (List.cons.inj hB).1
  | nonterminal hr hout hrest ihout ihrest =>
    rename_i r u w₁ w₂
    by_cases hunit : IsUnitOutput r.output
    · obtain ⟨C, hC⟩ := hunit
      have hstep : UnitSteps g r.input C := unitSteps_single hr hC
      have h1 : Yields (unitGrammar g) [Symbol.nonterminal r.input] w₁ :=
        ihout.2 C hC r.input hstep
      refine ⟨h1.append ihrest.1, ?_⟩
      intro B hB A hsteps
      have h2 := List.cons.inj hB
      have hBeq : r.input = B := Symbol.nonterminal.inj h2.1
      have hu : u = [] := h2.2
      subst hu
      subst hBeq
      cases hrest
      simpa using ihout.2 C hC A (Relation.ReflTransGen.trans hsteps hstep)
    · have hrule : (⟨r.input, r.output⟩ : ContextFreeRule T g.NT) ∈
          (unitGrammar g).rules :=
        mem_unitGrammar_rules Relation.ReflTransGen.refl hr rfl hunit
          (mem_grammarNTs_of_rule_input hr)
      refine ⟨Yields.nonterminal hrule ihout.1 ihrest.1, ?_⟩
      intro B hB A hsteps
      have h2 := List.cons.inj hB
      have hBeq : r.input = B := Symbol.nonterminal.inj h2.1
      have hu : u = [] := h2.2
      subst hu
      subst hBeq
      cases hrest
      have hA : A ∈ grammarNTs g :=
        mem_grammarNTs_of_unitSteps hsteps ⟨r.output, hr⟩
      have hruleA : (⟨A, r.output⟩ : ContextFreeRule T g.NT) ∈
          (unitGrammar g).rules :=
        mem_unitGrammar_rules hsteps hr rfl hunit hA
      simpa using yields_of_rule hruleA ihout.1

/-- **Eliminating unit productions keeps every yield.** Let $g$ be a context-free grammar.
If a sentential form $\alpha$ of $g$ yields a terminal word $w$ in $g$, then $\alpha$
yields $w$ in the grammar obtained from $g$ by eliminating unit productions. -/
theorem yields_unitGrammar_of_yields {α : List (Symbol T g.NT)}
    {w : List T} (h : Yields g α w) : Yields (unitGrammar g) α w :=
  (yields_unitGrammar_of_yields_aux h).1

/-- **Eliminating unit productions preserves the language.** For every context-free
grammar $g$, the grammar obtained from $g$ by eliminating unit productions generates
the same language as $g$. -/
theorem unitGrammar_language : (unitGrammar g).language = g.language := by
  ext w
  constructor
  · intro hw
    have hle := language_le_of_valuation (g := unitGrammar g)
      isValuation_unitGrammar hw
    change w ∈ languageFrom g g.initial at hle
    rwa [languageFrom_initial] at hle
  · intro hw
    exact mem_language_iff_yields.mpr
      (yields_unitGrammar_of_yields (mem_language_iff_yields.mp hw))

/-- **Reduced grammars.** A context-free grammar is reduced when no production has empty
right-hand side and no production has a single nonterminal as its right-hand side.

This is the sense used for the pumping lemma and normal forms. It does not assert that every
nonterminal is reachable or productive. -/
def IsReduced (g : ContextFreeGrammar T) : Prop :=
  (∀ r ∈ g.rules, r.output ≠ []) ∧
    ∀ r ∈ g.rules, ¬ IsUnitOutput r.output

/-- **Existence of reduced grammars.** For every context-free grammar $g$ over an alphabet $T$
there is a context-free grammar $g'$ over $T$ that generates exactly the nonempty words
generated by $g$, such that no production of $g'$ has empty right-hand side and no production
of $g'$ has a single nonterminal as its right-hand side. -/
theorem exists_reduced_grammar (g : ContextFreeGrammar T) :
    ∃ g' : ContextFreeGrammar T,
      (∀ w, w ∈ g'.language ↔ w ∈ g.language ∧ w ≠ []) ∧
      (∀ r ∈ g'.rules, r.output ≠ []) ∧
      (∀ r ∈ g'.rules, ¬ IsUnitOutput r.output) := by
  refine ⟨unitGrammar (epsGrammar g), ?_, ?_, ?_⟩
  · intro w
    rw [unitGrammar_language]
    exact epsGrammar_language
  · intro r hr hr0
    obtain ⟨B, r₀, hr₀, -, -, -, hout⟩ :=
      cases_of_mem_unitGrammar_rules (g := epsGrammar g) hr
    have hne : r₀.output ≠ [] := epsGrammar_output_ne_nil (g := g) hr₀
    exact hne (hout.symm.trans hr0)
  · intro r hr
    exact unitGrammar_not_isUnitOutput (g := epsGrammar g) hr

end Cslib.Language
