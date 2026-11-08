/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Closure of context-free languages under inverse homomorphisms
-/
module

public import CSLibExt.Computability.Languages.Congruences.WordMorphisms
public import CSLibExt.Computability.Languages.ContextFree.Hom
public import CSLibExt.Computability.Languages.ContextFree.InterRegular
public import CSLibExt.Computability.Languages.Finite

/-!
# Closure of context-free languages under inverse homomorphisms

For a homomorphism `φ : T → List T'` from a finite alphabet and a context-free language `L` over
`T'`, the preimage `{w | (w.map φ).flatten ∈ L}` is context-free
(`Cslib.Language.IsContextFree.preimage_hom`), and so is the preimage under a free-monoid
morphism (`Cslib.Language.IsContextFree.preimage_wordMorphism`, for the repository's
`wordMorphismPreimage`).

The proof avoids pushdown automata. Over the alphabet `T ⊕ T'`, write `projRight u` for the
letters of `u` from `T'`.

1. `Cslib.Language.IsContextFree.preimage_projRight`: `{u | projRight u ∈ L}` is context-free.
   The grammar `insGrammar` puts a marker loop `D → inl a D | ε` before every terminal of the
   original productions and after the whole word.
2. With `block a = inl a :: (φ a).map inr` and `R = (range block)∗` (regular, since `T` is
   finite), erasing the right letters maps `{u | projRight u ∈ L} ∩ R` onto the preimage. The
   intersection is context-free (`IsContextFree.inf_isRegular`), and so is its image under a
   homomorphism (`IsContextFree.homImage`).
-/

@[expose] public section

open scoped Computability

namespace Cslib.Language

attribute [local instance] Classical.propDecidable

variable {T T' : Type*}

/-! ## Right letters -/

/-- The letters of a word over `T ⊕ T'` that come from `T'`. -/
def projRight (u : List (T ⊕ T')) : List T' :=
  u.filterMap Sum.getRight?

@[simp]
theorem projRight_nil : projRight ([] : List (T ⊕ T')) = [] :=
  rfl

@[simp]
theorem projRight_cons_inl (a : T) (u : List (T ⊕ T')) :
    projRight (Sum.inl a :: u) = projRight u :=
  rfl

@[simp]
theorem projRight_cons_inr (b : T') (u : List (T ⊕ T')) :
    projRight (Sum.inr b :: u) = b :: projRight u :=
  rfl

@[simp]
theorem projRight_append (u v : List (T ⊕ T')) :
    projRight (u ++ v) = projRight u ++ projRight v :=
  List.filterMap_append

/-! ## Inserting marker letters -/

section Insert

variable (g : ContextFreeGrammar T')

/-- The translation of a symbol: a terminal is preceded by the marker loop `none`, and a
nonterminal `A` becomes `some (some A)`. -/
def insSymbol : Symbol T' g.NT → List (Symbol (T ⊕ T') (Option (Option g.NT)))
  | .terminal b => [.nonterminal none, .terminal (.inr b)]
  | .nonterminal A => [.nonterminal (some (some A))]

/-- The form with a marker loop before each right letter of `u` and after them. -/
def markedForm {g : ContextFreeGrammar T'} (u : List (T ⊕ T')) :
    List (Symbol (T ⊕ T') (Option (Option g.NT))) :=
  (projRight u).flatMap (fun b => [.nonterminal none, .terminal (.inr b)]) ++ [.nonterminal none]

theorem markedForm_eq_cons {g : ContextFreeGrammar T'} (u : List (T ⊕ T')) :
    ∃ rest, markedForm (g := g) u = .nonterminal none :: rest := by
  unfold markedForm
  cases projRight u with
  | nil => exact ⟨[], rfl⟩
  | cons b v => exact ⟨_, rfl⟩

variable [Fintype T]

/-- The grammar for `{u | projRight u ∈ g.language}`: the translated productions, a new start
`some none → some (some g.initial) none`, and the marker loop `none → inl a none | ε`. -/
noncomputable abbrev insGrammar : ContextFreeGrammar (T ⊕ T') where
  NT := Option (Option g.NT)
  initial := some none
  rules :=
    g.rules.image (fun r => ⟨some (some r.input), r.output.flatMap (insSymbol (T := T) g)⟩) ∪
      ({⟨some none, [.nonterminal (some (some g.initial)), .nonterminal none]⟩, ⟨none, []⟩} ∪
        Finset.univ.image fun a : T => ⟨none, [.terminal (.inl a), .nonterminal none]⟩)

variable {g}

theorem insGrammar_rule_of_mem {r : ContextFreeRule T' g.NT} (hr : r ∈ g.rules) :
    (⟨some (some r.input), r.output.flatMap (insSymbol (T := T) g)⟩ :
      ContextFreeRule (T ⊕ T') (Option (Option g.NT))) ∈ (insGrammar (T := T) g).rules :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem _ hr)

theorem insGrammar_rule_start :
    (⟨some none, [.nonterminal (some (some g.initial)), .nonterminal none]⟩ :
      ContextFreeRule (T ⊕ T') (Option (Option g.NT))) ∈ (insGrammar (T := T) g).rules :=
  Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_insert_self _ _))

theorem insGrammar_rule_eps :
    (⟨none, []⟩ : ContextFreeRule (T ⊕ T') (Option (Option g.NT))) ∈
      (insGrammar (T := T) g).rules :=
  Finset.mem_union_right _ (Finset.mem_union_left _
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))

theorem insGrammar_rule_mark (a : T) :
    (⟨none, [.terminal (.inl a), .nonterminal none]⟩ :
      ContextFreeRule (T ⊕ T') (Option (Option g.NT))) ∈ (insGrammar (T := T) g).rules :=
  Finset.mem_union_right _
    (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ a)))

/-- Derivations of the original grammar translate. -/
theorem insGrammar_derives_flatMap {x y : List (Symbol T' g.NT)} (h : g.Derives x y) :
    (insGrammar (T := T) g).Derives (x.flatMap (insSymbol g)) (y.flatMap (insSymbol g)) := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      obtain ⟨r, hr, hrew⟩ := hstep
      obtain ⟨p, q, rfl, rfl⟩ := ContextFreeRule.rewrites_iff.mp hrew
      refine ih.trans_produces ⟨_, insGrammar_rule_of_mem hr, ?_⟩
      have h := ContextFreeRule.rewrites_of_exists_parts
        (⟨some (some r.input), r.output.flatMap (insSymbol (T := T) g)⟩ :
          ContextFreeRule (T ⊕ T') (Option (Option g.NT)))
        (p.flatMap (insSymbol g)) (q.flatMap (insSymbol g))
      have e₁ : (p ++ [Symbol.nonterminal r.input] ++ q).flatMap (insSymbol (T := T) g) =
          p.flatMap (insSymbol g) ++ [Symbol.nonterminal (some (some r.input))] ++
            q.flatMap (insSymbol g) := by
        simp [List.flatMap_append, insSymbol]
      have e₂ : (p ++ r.output ++ q).flatMap (insSymbol (T := T) g) =
          p.flatMap (insSymbol g) ++ r.output.flatMap (insSymbol g) ++ q.flatMap (insSymbol g) := by
        simp [List.flatMap_append]
      rw [e₁, e₂]
      exact h

/-- The marker loops of `markedForm u` derive exactly the left letters of `u`. -/
theorem insGrammar_derives_markedForm :
    ∀ u : List (T ⊕ T'), (insGrammar (T := T) g).Derives (markedForm u) (u.map .terminal)
  | [] => by
      refine ContextFreeGrammar.Produces.single ⟨_, insGrammar_rule_eps, ?_⟩
      exact ContextFreeRule.Rewrites.input_output
  | .inl a :: u => by
      obtain ⟨rest, hrest⟩ := markedForm_eq_cons (g := g) u
      have hstep : (insGrammar (T := T) g).Produces (markedForm (g := g) (.inl a :: u))
          (.terminal (.inl a) :: markedForm (g := g) u) := by
        refine ⟨_, insGrammar_rule_mark a, ?_⟩
        have h := ContextFreeRule.rewrites_of_exists_parts
          (⟨none, [.terminal (.inl a), .nonterminal none]⟩ :
            ContextFreeRule (T ⊕ T') (Option (Option g.NT))) [] rest
        change ContextFreeRule.Rewrites _ (markedForm (g := g) u) _
        rw [hrest]
        simp only [List.nil_append, List.cons_append] at h
        exact h
      exact hstep.trans_derives ((insGrammar_derives_markedForm u).append_left
        [Symbol.terminal (N := Option (Option g.NT)) (Sum.inl a)])
  | .inr b :: u => by
      have hstep : (insGrammar (T := T) g).Produces (markedForm (g := g) (.inr b :: u))
          (.terminal (.inr b) :: markedForm (g := g) u) := by
        refine ⟨_, insGrammar_rule_eps, ?_⟩
        have h := ContextFreeRule.rewrites_of_exists_parts
          (⟨none, []⟩ : ContextFreeRule (T ⊕ T') (Option (Option g.NT))) []
          (.terminal (.inr b) :: markedForm (g := g) u)
        simp only [List.nil_append, List.singleton_append] at h
        exact h
      exact hstep.trans_derives ((insGrammar_derives_markedForm u).append_left
        [Symbol.terminal (N := Option (Option g.NT)) (Sum.inr b)])

/-- The assignment showing that `insGrammar` generates only words whose right letters are in
the original language. -/
def insValuation (g : ContextFreeGrammar T') : Option (Option g.NT) → Language (T ⊕ T')
  | none => {u | projRight u = []}
  | some none => {u | projRight u ∈ g.language}
  | some (some A) => {u | projRight u ∈ languageFrom g A}

omit [Fintype T] in
theorem projRight_mem_evalForm :
    ∀ (α : List (Symbol T' g.NT)) {u : List (T ⊕ T')},
      u ∈ evalForm (insValuation g) (α.flatMap (insSymbol g)) →
        projRight u ∈ evalForm (languageFrom g) α
  | [], u, hu => by
      simp only [List.flatMap_nil, evalForm_nil, Language.mem_one] at hu ⊢
      rw [hu]
      rfl
  | s :: α, u, hu => by
      rw [List.flatMap_cons, evalForm_append] at hu
      obtain ⟨x, hx, y, hy, rfl⟩ := Language.mem_mul.mp hu
      rw [evalForm_cons, projRight_append]
      refine Language.mem_mul.mpr ⟨projRight x, ?_, projRight y,
        projRight_mem_evalForm α hy, rfl⟩
      cases s with
      | terminal b =>
          simp only [insSymbol, evalForm_cons, evalForm_nil, evalSymbol_nonterminal,
            evalSymbol_terminal, mul_one] at hx
          obtain ⟨m, hm, c, hc, rfl⟩ := Language.mem_mul.mp hx
          rw [Set.mem_singleton_iff.1 hc]
          change projRight m = [] at hm
          rw [evalSymbol_terminal, projRight_append, hm]
          rfl
      | nonterminal A =>
          simp only [insSymbol, evalForm_cons, evalForm_nil, evalSymbol_nonterminal,
            mul_one] at hx
          exact hx

theorem isValuation_insValuation :
    IsValuation (insGrammar (T := T) g) (insValuation g) := by
  intro r hr u hu
  rcases Finset.mem_union.1 hr with h₁ | h₂
  · obtain ⟨r₀, hr₀, rfl⟩ := Finset.mem_image.1 h₁
    exact isValuation_languageFrom r₀ hr₀ (projRight_mem_evalForm r₀.output hu)
  rcases Finset.mem_union.1 h₂ with h₃ | h₄
  swap
  · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 h₄
    simp only [evalForm_cons, evalForm_nil, evalSymbol_nonterminal, evalSymbol_terminal,
      mul_one] at hu
    obtain ⟨x, hx, y, hy, rfl⟩ := Language.mem_mul.mp hu
    rw [Set.mem_singleton_iff.1 hx]
    change projRight y = [] at hy
    change projRight ([Sum.inl a] ++ y) = []
    simpa using hy
  rcases Finset.mem_insert.1 h₃ with rfl | h₅
  · simp only [evalForm_cons, evalForm_nil, evalSymbol_nonterminal, mul_one] at hu
    obtain ⟨x, hx, y, hy, rfl⟩ := Language.mem_mul.mp hu
    change projRight x ∈ languageFrom g g.initial at hx
    change projRight y = [] at hy
    change projRight (x ++ y) ∈ g.language
    rw [projRight_append, hy, List.append_nil]
    exact hx
  · rw [Finset.mem_singleton] at h₅
    subst h₅
    simp only [evalForm_nil] at hu
    rw [(Language.mem_one _).1 hu]
    rfl

/-- **`insGrammar` generates the words whose right letters form a word of the original
language.** -/
theorem insGrammar_language :
    (insGrammar (T := T) g).language = {u | projRight u ∈ g.language} := by
  ext u
  constructor
  · intro hu
    exact language_le_of_valuation isValuation_insValuation hu
  · intro hu
    change projRight u ∈ g.language at hu
    rw [ContextFreeGrammar.mem_language_iff] at hu ⊢
    have h₁ := insGrammar_derives_flatMap (T := T) hu
    have hstart : (insGrammar (T := T) g).Produces [.nonterminal (some none)]
        [.nonterminal (some (some g.initial)), .nonterminal none] :=
      ⟨_, insGrammar_rule_start, ContextFreeRule.Rewrites.input_output⟩
    refine hstart.trans_derives ?_
    have h₂ := h₁.append_right [Symbol.nonterminal (T := T ⊕ T') (none : Option (Option g.NT))]
    have hform : ((projRight u).map Symbol.terminal).flatMap (insSymbol (T := T) g) ++
        [.nonterminal none] = markedForm (g := g) u := by
      simp [markedForm, List.flatMap_map, insSymbol]
    rw [hform] at h₂
    exact (by simpa [insSymbol] using h₂ : (insGrammar (T := T) g).Derives
      [.nonterminal (some (some g.initial)), .nonterminal none] (markedForm (g := g) u)).trans
      (insGrammar_derives_markedForm u)

end Insert

/-- **Inserting letters**: if `L` is context-free over `T'`, so is the set of words over
`T ⊕ T'` whose letters from `T'` form a word of `L`, for a finite `T`. -/
theorem IsContextFree.preimage_projRight [Finite T] {L : Language T'} (hL : L.IsContextFree) :
    Language.IsContextFree {u : List (T ⊕ T') | projRight u ∈ L} := by
  have := Fintype.ofFinite T
  obtain ⟨g, rfl⟩ := hL
  exact ⟨insGrammar g, insGrammar_language⟩

/-! ## Inverse homomorphisms -/

/-- A letter `a` followed by its image under `φ`, as right letters. -/
def block (φ : T → List T') (a : T) : List (T ⊕ T') :=
  Sum.inl a :: (φ a).map Sum.inr

/-- Erase the right letters and keep the left ones. -/
def eraseRight : T ⊕ T' → List T :=
  Sum.elim (fun a => [a]) (fun _ => [])

theorem projRight_block (φ : T → List T') (a : T) : projRight (block φ a) = φ a := by
  simp only [block, projRight_cons_inl]
  induction φ a with
  | nil => rfl
  | cons b v ih => simp [ih]

theorem eraseRight_block (φ : T → List T') (a : T) :
    ((block φ a).map eraseRight).flatten = [a] := by
  simp only [block, List.map_cons, List.flatten_cons, List.map_map]
  induction φ a with
  | nil => rfl
  | cons b v ih => simp [eraseRight]

theorem projRight_flatten_block (φ : T → List T') (w : List T) :
    projRight ((w.map (block φ)).flatten) = (w.map φ).flatten := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [projRight_block, ih]

theorem eraseRight_flatten_block (φ : T → List T') (w : List T) :
    (((w.map (block φ)).flatten).map eraseRight).flatten = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      simp only [List.map_cons, List.flatten_cons, List.map_append, List.flatten_append,
        eraseRight_block, ih]
      rfl

/-- **Context-free languages are closed under inverse homomorphisms** from a finite alphabet. -/
theorem IsContextFree.preimage_hom [Finite T] {L : Language T'} (hL : L.IsContextFree)
    (φ : T → List T') :
    Language.IsContextFree {w : List T | (w.map φ).flatten ∈ L} := by
  let P : Language (T ⊕ T') := {u | projRight u ∈ L}
  let R : Language (T ⊕ T') := (Set.range (block φ) : Language (T ⊕ T'))∗
  have hR : R.IsRegular := IsRegular.kstar (IsRegular.of_finite (Set.finite_range _))
  have hP : P.IsContextFree := IsContextFree.preimage_projRight hL
  have h := IsContextFree.homImage (IsContextFree.inf_isRegular hP hR) eraseRight
  have heq : ({w : List T | (w.map φ).flatten ∈ L} : Language T) =
      (fun u => (u.map eraseRight).flatten) '' (P ⊓ R) := by
    ext w
    constructor
    · intro hw
      refine ⟨(w.map (block φ)).flatten, ⟨?_, ?_⟩, eraseRight_flatten_block φ w⟩
      · change projRight _ ∈ L
        rw [projRight_flatten_block]
        exact hw
      · exact Language.mem_kstar.2 ⟨w.map (block φ), rfl, by
          simp only [List.mem_map]
          rintro y ⟨a, -, rfl⟩
          exact ⟨a, rfl⟩⟩
    · rintro ⟨u, ⟨hP, hR⟩, rfl⟩
      obtain ⟨Ls, rfl, hLs⟩ := Language.mem_kstar.1 hR
      obtain ⟨v, rfl⟩ : ∃ v : List T, Ls = v.map (block φ) := by
        clear hP hR
        induction Ls with
        | nil => exact ⟨[], rfl⟩
        | cons y Ls ih =>
            obtain ⟨a, rfl⟩ := hLs y List.mem_cons_self
            obtain ⟨v, rfl⟩ := ih fun z hz => hLs z (List.mem_cons_of_mem _ hz)
            exact ⟨a :: v, rfl⟩
      change projRight _ ∈ L at hP
      rw [projRight_flatten_block] at hP
      change ((((v.map (block φ)).flatten).map eraseRight).flatten.map φ).flatten ∈ L
      rw [eraseRight_flatten_block]
      exact hP
  rw [heq]
  exact h

/-- **Context-free languages are closed under inverse free-monoid morphisms** from a finite
alphabet, in the form of `wordMorphismPreimage`. -/
theorem IsContextFree.preimage_wordMorphism [Finite T] {L : Language T'} (hL : L.IsContextFree)
    (σ : FreeMonoid T →* FreeMonoid T') : (wordMorphismPreimage σ L).IsContextFree := by
  rw [wordMorphismPreimage_eq_flatten]
  exact IsContextFree.preimage_hom hL _

end Cslib.Language
