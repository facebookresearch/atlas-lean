/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.Encoded
public import CSLibExt.Computability.Languages.ContextFree.Ambiguity
public import Cslib.Computability.Languages.LanguageHom
import all CSLibExt.Computability.Languages.ContextFree.Hom

/-!
# Terminal-word coding of encoded context-free grammars

`EncodedCFG.mapTerminals` is a computable transformation of grammar encodings, not an
existential choice of a grammar for the image language. Its semantic construction is the
one in `ContextFree.Hom`; the language theorem below reuses that file's proof.

Leftmost derivations transport with their exact lists of rule values and reflect to source
derivations. An injective induced word homomorphism makes the maps on sentential forms,
rules, and traces injective, so it preserves and reflects grammar ambiguity as well as
language overlap. Repeated entries of an encoded rule list are still deduplicated by `toCFG`.
The source alphabet need not be finite, and the general transport permits erasing maps.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Language.EncodedCFG

variable {T T' : Type*}

private def expandEncodedSymbol (φ : T → List T') : ℕ ⊕ T → List (ℕ ⊕ T')
  | .inl A => [.inl A]
  | .inr a => (φ a).map Sum.inr

/-- Replace every terminal in every production by its codeword, retaining the start and
nonterminal labels. The production list is mapped, not re-enumerated or deduplicated. -/
def mapTerminals (φ : T → List T') (g : EncodedCFG T) : EncodedCFG T' :=
  ⟨g.start, g.rules.map fun r => (r.1, r.2.flatMap fun
    | .inl A => [.inl A]
    | .inr a => (φ a).map Sum.inr)⟩

/-- The semantic sentential-form map used by terminal coding. It is definitionally the
expansion from `ContextFree.Hom`, with a public name for exact derivation transport. -/
def mapTerminalForm (φ : T → List T') (u : List (Symbol T ℕ)) : List (Symbol T' ℕ) :=
  u.flatMap fun
    | .terminal a => (φ a).map Symbol.terminal
    | .nonterminal A => [Symbol.nonterminal A]

/-- The semantic rule map used by terminal coding; its input nonterminal is unchanged. -/
def mapTerminalRule (φ : T → List T') (r : ContextFreeRule T ℕ) : ContextFreeRule T' ℕ :=
  ⟨r.input, mapTerminalForm φ r.output⟩

@[simp]
theorem start_mapTerminals (φ : T → List T') (g : EncodedCFG T) :
    (mapTerminals φ g).start = g.start := rfl

@[simp]
theorem mapTerminalForm_nil (φ : T → List T') : mapTerminalForm φ [] = [] := rfl

@[simp]
theorem mapTerminalForm_terminal (φ : T → List T') (a : T) (u : List (Symbol T ℕ)) :
    mapTerminalForm φ (Symbol.terminal a :: u) =
      (φ a).map Symbol.terminal ++ mapTerminalForm φ u := rfl

@[simp]
theorem mapTerminalForm_nonterminal (φ : T → List T') (A : ℕ) (u : List (Symbol T ℕ)) :
    mapTerminalForm φ (Symbol.nonterminal A :: u) =
      Symbol.nonterminal A :: mapTerminalForm φ u := rfl

@[simp]
theorem mapTerminalForm_append (φ : T → List T') (u v : List (Symbol T ℕ)) :
    mapTerminalForm φ (u ++ v) = mapTerminalForm φ u ++ mapTerminalForm φ v :=
  List.flatMap_append

@[simp]
theorem mapTerminalForm_map_terminal (φ : T → List T') (w : List T) :
    mapTerminalForm φ (w.map Symbol.terminal) =
      ((_root_.Language.Hom.lift φ) w).map Symbol.terminal := by
  simp [mapTerminalForm, _root_.Language.Hom.lift_eq_flatMap,
    List.flatMap_map, List.map_flatMap]

@[simp]
theorem mapTerminalRule_input (φ : T → List T') (r : ContextFreeRule T ℕ) :
    (mapTerminalRule φ r).input = r.input := rfl

@[simp]
theorem mapTerminalRule_output (φ : T → List T') (r : ContextFreeRule T ℕ) :
    (mapTerminalRule φ r).output = mapTerminalForm φ r.output := rfl

private theorem decode_expanded_form (φ : T → List T') (u : List (ℕ ⊕ T)) :
    (u.flatMap (expandEncodedSymbol φ)).map decodeSymbol =
      mapTerminalForm φ (u.map decodeSymbol) := by
  induction u with
  | nil => rfl
  | cons s u ih =>
    cases s <;>
      simp_all [expandEncodedSymbol, decodeSymbol, mapTerminalForm]

private theorem decode_expanded_rule (φ : T → List T') (r : ℕ × List (ℕ ⊕ T)) :
    decodeRule (r.1, r.2.flatMap (expandEncodedSymbol φ)) =
      mapTerminalRule φ (decodeRule r) := by
  apply ContextFreeRule.ext
  · rfl
  · exact decode_expanded_form φ r.2

section Semantics

variable [DecidableEq T] [DecidableEq T']

/-- The rules of the transformed grammar are exactly the images of source rule values.
This statement uses Finset membership, so duplicate encoded occurrences are not new choices. -/
theorem mem_rules_mapTerminals (φ : T → List T') (g : EncodedCFG T)
    (r : ContextFreeRule T' ℕ) :
    r ∈ (mapTerminals φ g).toCFG.rules ↔
      ∃ r₀ ∈ g.toCFG.rules, mapTerminalRule φ r₀ = r := by
  constructor
  · intro hr
    obtain ⟨e, he, heq⟩ := mem_toCFG_rules.mp hr
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
    exact ⟨decodeRule e₀, mem_toCFG_rules.mpr ⟨e₀, he₀, rfl⟩,
      (decode_expanded_rule φ e₀).symm.trans heq⟩
  · rintro ⟨r₀, hr₀, rfl⟩
    obtain ⟨e, he, rfl⟩ := mem_toCFG_rules.mp hr₀
    exact mem_toCFG_rules.mpr ⟨_, List.mem_map.mpr ⟨e, he, rfl⟩,
      decode_expanded_rule φ e⟩

omit [DecidableEq T] [DecidableEq T'] in
private theorem mapTerminalForm_eq_expandForm (φ : T → List T') (u : List (Symbol T ℕ)) :
    mapTerminalForm φ u = expandForm φ u := by
  unfold mapTerminalForm expandForm
  apply congrArg (fun f : Symbol T ℕ → List (Symbol T' ℕ) => u.flatMap f)
  funext s
  cases s <;> rfl

omit [DecidableEq T] [DecidableEq T'] in
private theorem mapTerminalRule_eq_expandRule (φ : T → List T') (r : ContextFreeRule T ℕ) :
    mapTerminalRule φ r = expandRule φ r := by
  simp only [mapTerminalRule, expandRule, mapTerminalForm_eq_expandForm]

private theorem toCFG_mapTerminals (φ : T → List T') (g : EncodedCFG T) :
    (mapTerminals φ g).toCFG = homGrammar φ g.toCFG := by
  classical
  have hrules : (mapTerminals φ g).toCFG.rules = (homGrammar φ g.toCFG).rules := by
    ext r
    simpa only [homGrammar, Finset.mem_image, mapTerminalRule_eq_expandRule] using
      mem_rules_mapTerminals φ g r
  exact congrArg (fun rules =>
    ({ NT := ℕ, initial := g.start, rules := rules } : ContextFreeGrammar T')) hrules

/-- Terminal-word coding generates exactly the image under the canonical word homomorphism. -/
theorem language_mapTerminals (φ : T → List T') (g : EncodedCFG T) :
    (mapTerminals φ g).language = g.language.image (_root_.Language.Hom.lift φ) := by
  classical
  rw [language, toCFG_mapTerminals, homGrammar_language]
  rfl

/-- Membership in the coded language, with the original word retained as a witness. -/
theorem mem_language_mapTerminals (φ : T → List T') (g : EncodedCFG T) (w : List T') :
    w ∈ (mapTerminals φ g).language ↔
      ∃ u ∈ g.language, (_root_.Language.Hom.lift φ) u = w := by
  rw [language_mapTerminals, _root_.Language.mem_image]

/-- Injective word coding preserves and reflects the existence of a common word. -/
theorem overlap_mapTerminals_iff (φ : T → List T')
    (hinj : Function.Injective (_root_.Language.Hom.lift φ)) (g₁ g₂ : EncodedCFG T) :
    (∃ w, w ∈ (mapTerminals φ g₁).language ∧ w ∈ (mapTerminals φ g₂).language) ↔
      ∃ w, w ∈ g₁.language ∧ w ∈ g₂.language := by
  constructor
  · rintro ⟨w, h₁, h₂⟩
    obtain ⟨u, hu, he⟩ := (mem_language_mapTerminals φ g₁ w).mp h₁
    obtain ⟨v, hv, he'⟩ := (mem_language_mapTerminals φ g₂ w).mp h₂
    have huv : u = v := hinj (he.trans he'.symm)
    exact ⟨v, huv ▸ hu, hv⟩
  · rintro ⟨w, h₁, h₂⟩
    exact ⟨(_root_.Language.Hom.lift φ) w,
      (mem_language_mapTerminals φ g₁ _).mpr ⟨w, h₁, rfl⟩,
      (mem_language_mapTerminals φ g₂ _).mpr ⟨w, h₂, rfl⟩⟩

end Semantics

/-! ## First nonterminals and injectivity of rule traces -/

private theorem firstNonterminal_cases {N : Type*} (u : List (Symbol T N)) :
    (∃ w : List T, u = w.map Symbol.terminal) ∨
      ∃ (p : List T) (A : N) (v : List (Symbol T N)),
        u = p.map Symbol.terminal ++ Symbol.nonterminal A :: v := by
  induction u with
  | nil => exact Or.inl ⟨[], rfl⟩
  | cons s u ih =>
    cases s with
    | nonterminal A => exact Or.inr ⟨[], A, u, rfl⟩
    | terminal a =>
      rcases ih with ⟨w, rfl⟩ | ⟨p, A, v, rfl⟩
      · exact Or.inl ⟨a :: w, rfl⟩
      · exact Or.inr ⟨a :: p, A, v, rfl⟩

private theorem terminalPrefix_eq {N : Type*} {p q : List T} {A B : N}
    {u v : List (Symbol T N)}
    (h : p.map Symbol.terminal ++ Symbol.nonterminal A :: u =
      q.map Symbol.terminal ++ Symbol.nonterminal B :: v) : p = q ∧ A = B ∧ u = v := by
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => simpa using h
    | cons b q => simp at h
  | cons a p ih =>
    cases q with
    | nil => simp at h
    | cons b q =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq, Symbol.terminal.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨rfl, rfl, rfl⟩ := ih h
      exact ⟨rfl, rfl, rfl⟩

/-- Injectivity on terminal words implies injectivity on mixed sentential forms.
Nonterminals delimit maximal blocks of terminals, including empty blocks. -/
theorem mapTerminalForm_injective {φ : T → List T'}
    (hinj : Function.Injective (_root_.Language.Hom.lift φ)) :
    Function.Injective (mapTerminalForm φ) := by
  have aux : ∀ n, ∀ u v : List (Symbol T ℕ), u.length ≤ n →
      mapTerminalForm φ u = mapTerminalForm φ v → u = v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro u v hlen he
      rcases firstNonterminal_cases u with ⟨p, rfl⟩ | ⟨p, A, u, rfl⟩ <;>
        rcases firstNonterminal_cases v with ⟨q, rfl⟩ | ⟨q, B, v, rfl⟩
      · simp only [mapTerminalForm_map_terminal] at he
        have hpq := hinj (List.map_injective_iff.mpr (fun _ _ h => Symbol.terminal.inj h) he)
        exact congrArg (List.map Symbol.terminal) hpq
      · simp only [mapTerminalForm_append, mapTerminalForm_map_terminal,
          mapTerminalForm_nonterminal] at he
        have hm : Symbol.nonterminal B ∈ ((_root_.Language.Hom.lift φ) p).map Symbol.terminal := by
          rw [he]
          simp
        simp at hm
      · simp only [mapTerminalForm_append, mapTerminalForm_map_terminal,
          mapTerminalForm_nonterminal] at he
        have hm : Symbol.nonterminal A ∈ ((_root_.Language.Hom.lift φ) q).map Symbol.terminal := by
          rw [← he]
          simp
        simp at hm
      · simp only [mapTerminalForm_append, mapTerminalForm_map_terminal,
          mapTerminalForm_nonterminal] at he
        obtain ⟨hp, hA, huv⟩ := terminalPrefix_eq he
        have hpq := hinj hp
        have huv' : u = v := ih u.length (by
          simp only [List.length_append, List.length_map, List.length_cons] at hlen
          omega) u v le_rfl huv
        rw [hpq, hA, huv']
  exact fun u v h => aux u.length u v le_rfl h

/-- Injective word coding does not merge distinct production values. -/
theorem mapTerminalRule_injective {φ : T → List T'}
    (hinj : Function.Injective (_root_.Language.Hom.lift φ)) :
    Function.Injective (mapTerminalRule φ) := by
  intro r s h
  apply ContextFreeRule.ext
  · simpa only [mapTerminalRule_input] using
      congrArg (fun r : ContextFreeRule T' ℕ => r.input) h
  · exact mapTerminalForm_injective hinj (congrArg ContextFreeRule.output h)

/-- Injective word coding does not merge distinct leftmost rule-list traces. -/
theorem mapTerminalRules_injective {φ : T → List T'}
    (hinj : Function.Injective (_root_.Language.Hom.lift φ)) :
    Function.Injective (List.map (mapTerminalRule φ)) :=
  List.map_injective_iff.mpr (mapTerminalRule_injective hinj)

section Leftmost

variable [DecidableEq T] [DecidableEq T'] {g : EncodedCFG T} {φ : T → List T'}

/-- Map a leftmost derivation and its exact rule trace. No injectivity is required. -/
theorem leftDerivation_mapTerminals {u : List (Symbol T ℕ)} {w : List T}
    {rs : List (ContextFreeRule T ℕ)} (h : LeftDerivation g.toCFG u w rs) :
    LeftDerivation (mapTerminals φ g).toCFG (mapTerminalForm φ u)
      ((_root_.Language.Hom.lift φ) w) (rs.map (mapTerminalRule φ)) := by
  induction h using @LeftDerivation.rec T g.toCFG with
  | done w =>
    simpa only [mapTerminalForm_map_terminal, List.map_nil] using
      (LeftDerivation.done (g := (mapTerminals φ g).toCFG) ((_root_.Language.Hom.lift φ) w))
  | @step p v w r rs hr _ ih =>
    simp only [mapTerminalForm_append, mapTerminalForm_map_terminal] at ih
    simpa only [mapTerminalForm_append, mapTerminalForm_map_terminal,
      mapTerminalForm_nonterminal, List.map_cons, mapTerminalRule_input] using
      (LeftDerivation.step (p := (_root_.Language.Hom.lift φ) p)
        (v := mapTerminalForm φ v) ((mem_rules_mapTerminals φ g _).mpr ⟨r, hr, rfl⟩) ih)

private theorem reflect_leftDerivation {s : List (Symbol T' ℕ)} {w : List T'}
    {rs : List (ContextFreeRule T' ℕ)}
    (h : LeftDerivation (mapTerminals φ g).toCFG s w rs) :
    ∀ u, mapTerminalForm φ u = s → ∃ w₀ rs₀,
      LeftDerivation g.toCFG u w₀ rs₀ ∧ (_root_.Language.Hom.lift φ) w₀ = w ∧
        rs₀.map (mapTerminalRule φ) = rs := by
  induction h using @LeftDerivation.rec T' (mapTerminals φ g).toCFG with
  | done w =>
    intro u he
    rcases firstNonterminal_cases u with ⟨p, rfl⟩ | ⟨p, A, v, rfl⟩
    · rw [mapTerminalForm_map_terminal] at he
      exact ⟨p, [], LeftDerivation.done p,
        List.map_injective_iff.mpr (fun _ _ h => Symbol.terminal.inj h) he, rfl⟩
    · simp only [mapTerminalForm_append, mapTerminalForm_map_terminal,
        mapTerminalForm_nonterminal] at he
      have hm : Symbol.nonterminal A ∈ w.map (Symbol.terminal (N := ℕ)) := by
        rw [← he]
        simp
      simp at hm
  | @step p v w r rs hr _ ih =>
    intro u he
    rcases firstNonterminal_cases u with ⟨q, rfl⟩ | ⟨q, A, v₀, rfl⟩
    · rw [mapTerminalForm_map_terminal] at he
      have hm : Symbol.nonterminal r.input ∈
          ((_root_.Language.Hom.lift φ) q).map (Symbol.terminal (N := ℕ)) := by
        rw [he]
        simp
      simp at hm
    · simp only [mapTerminalForm_append, mapTerminalForm_map_terminal,
        mapTerminalForm_nonterminal] at he
      obtain ⟨r₀, hr₀, rfl⟩ := (mem_rules_mapTerminals φ g r).mp hr
      obtain ⟨hp, hA, hv⟩ := terminalPrefix_eq he
      change A = r₀.input at hA
      subst A
      subst p
      subst v
      obtain ⟨w₀, rs₀, hd, hw, hrs⟩ := ih (q.map Symbol.terminal ++ r₀.output ++ v₀) (by
        simp only [mapTerminalForm_append, mapTerminalForm_map_terminal, mapTerminalRule_output])
      exact ⟨w₀, r₀ :: rs₀, LeftDerivation.step hr₀ hd, hw, by simp only [List.map_cons, hrs]⟩

/-- Every coded leftmost derivation is the image of a source derivation, including its
exact rule list. This existential reflection also holds for noninjective or erasing maps. -/
theorem leftDerivation_mapTerminals_iff {u : List (Symbol T ℕ)} {w : List T'}
    {rs : List (ContextFreeRule T' ℕ)} :
    LeftDerivation (mapTerminals φ g).toCFG (mapTerminalForm φ u) w rs ↔
      ∃ w₀ rs₀, LeftDerivation g.toCFG u w₀ rs₀ ∧
        (_root_.Language.Hom.lift φ) w₀ = w ∧ rs₀.map (mapTerminalRule φ) = rs := by
  constructor
  · exact fun h => reflect_leftDerivation h u rfl
  · rintro ⟨w₀, rs₀, hd, rfl, rfl⟩
    exact leftDerivation_mapTerminals hd

/-- For injective word coding, a specified word and specified trace transport in both directions. -/
theorem leftDerivation_mapTerminals_iff_of_injective
    (hinj : Function.Injective (_root_.Language.Hom.lift φ))
    {u : List (Symbol T ℕ)} {w : List T} {rs : List (ContextFreeRule T ℕ)} :
    LeftDerivation (mapTerminals φ g).toCFG (mapTerminalForm φ u)
      ((_root_.Language.Hom.lift φ) w) (rs.map (mapTerminalRule φ)) ↔
        LeftDerivation g.toCFG u w rs := by
  rw [leftDerivation_mapTerminals_iff]
  constructor
  · rintro ⟨w₀, rs₀, hd, hw, hrs⟩
    obtain rfl := hinj hw
    obtain rfl := mapTerminalRules_injective hinj hrs
    exact hd
  · exact fun h => ⟨w, rs, h, rfl, rfl⟩

/-- Injective word coding preserves and reflects ambiguity of the actual grammar,
not merely a property of its generated language. -/
theorem isAmbiguous_mapTerminals_iff
    (hinj : Function.Injective (_root_.Language.Hom.lift φ)) :
    IsAmbiguous (mapTerminals φ g).toCFG ↔ IsAmbiguous g.toCFG := by
  constructor
  · rintro ⟨w, rs₁, rs₂, hne, h₁, h₂⟩
    obtain ⟨w₁, ts₁, hd₁, hw₁, ht₁⟩ :=
      reflect_leftDerivation h₁ [Symbol.nonterminal g.start] rfl
    obtain ⟨w₂, ts₂, hd₂, hw₂, ht₂⟩ :=
      reflect_leftDerivation h₂ [Symbol.nonterminal g.start] rfl
    have hw : w₁ = w₂ := hinj (hw₁.trans hw₂.symm)
    refine ⟨w₁, ts₁, ts₂, ?_, hd₁, hw.symm ▸ hd₂⟩
    intro heq
    exact hne (ht₁.symm.trans ((congrArg (List.map (mapTerminalRule φ)) heq).trans ht₂))
  · rintro ⟨w, rs₁, rs₂, hne, h₁, h₂⟩
    exact ⟨(_root_.Language.Hom.lift φ) w, rs₁.map (mapTerminalRule φ),
      rs₂.map (mapTerminalRule φ), fun heq => hne (mapTerminalRules_injective hinj heq),
      leftDerivation_mapTerminals h₁, leftDerivation_mapTerminals h₂⟩

end Leftmost

/-! ## Primitive recursiveness on possibly infinite alphabets -/

/-- A primitive-recursive terminal-word map gives a primitive-recursive map of grammar
encodings. In particular, no finite-domain shortcut is needed for the source alphabet. -/
theorem primrec_mapTerminals [Primcodable T] [Primcodable T'] {φ : T → List T'}
    (hφ : Primrec φ) : Primrec (mapTerminals φ) := by
  have hs : Primrec (expandEncodedSymbol φ) := by
    have ht : Primrec fun a => (φ a).map (Sum.inr : T' → ℕ ⊕ T') :=
      Primrec.list_map hφ (Primrec.sumInr.comp Primrec.snd).to₂
    exact (Primrec.sumCasesOn Primrec.id
      (Primrec.list_cons.comp (Primrec.sumInl.comp Primrec.snd) (Primrec.const [])).to₂
      (ht.comp Primrec.snd).to₂).of_eq fun s => by cases s <;> rfl
  have hf : Primrec fun u : List (ℕ ⊕ T) => u.flatMap (expandEncodedSymbol φ) :=
    Primrec.list_flatMap Primrec.id (hs.comp Primrec.snd).to₂
  have hr : Primrec fun r : ℕ × List (ℕ ⊕ T) => (r.1, r.2.flatMap (expandEncodedSymbol φ)) :=
    Primrec.pair Primrec.fst (hf.comp Primrec.snd)
  exact primrec₂_mk.comp primrec_start
    (Primrec.list_map primrec_rules (hr.comp Primrec.snd).to₂)

end Cslib.Language.EncodedCFG
