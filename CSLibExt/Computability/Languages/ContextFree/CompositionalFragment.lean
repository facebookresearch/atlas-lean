/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Syntax
public import CSLibExt.Computability.Languages.ContextFree.Probabilistic

/-!
# A frozen seven-rule compositional fragment

Three tokens (everybody, admires, someone), six categories, and seven
distinct rules. The valid-domain compiler assigns each valid tree its
simply typed lambda term through seven typed semantic actions, and
the valid sentence trees are exactly the two designated parses.
-/

@[expose] public section

namespace Cslib.Language.CompositionalFragment

open Cslib.Languages.LambdaCalculus.Stlc
open scoped CslibStlc

/-- Tokens: `Fin 3` (contract: everybody = 0, admires = 1, someone = 2). -/
abbrev Token := Fin 3

/-- Categories: `Fin 6` (contract: S = 0, Subj = 1, Obj = 2, TV = 3,
VP = 4, SP = 5). -/
abbrev Cat := Fin 6

/-- Token `everybody` (index 0). -/
def everybodyTok : Token := 0

/-- Token `admires` (index 1). -/
def admiresTok : Token := 1

/-- Token `someone` (index 2). -/
def someoneTok : Token := 2

/-- Category `S` (index 0, start category). -/
def catS : Cat := 0

/-- Category `Subj` (index 1). -/
def catSubj : Cat := 1

/-- Category `Obj` (index 2). -/
def catObj : Cat := 2

/-- Category `TV` (index 3). -/
def catTV : Cat := 3

/-- Category `VP` (index 4). -/
def catVP : Cat := 4

/-- Category `SP` (index 5). -/
def catSP : Cat := 5

/-- Semantic type `e` (entities): `Ty.base false`. -/
def eTy : Ty Bool := Ty.base false

/-- Semantic type `t` (truth values): `Ty.base true`. -/
def tTy : Ty Bool := Ty.base true

/-- Semantic type `P = e => t` (predicates). -/
def PTy : Ty Bool := eTy ⇒ tTy

/-- Semantic type `Q = (e => t) => t` (generalized quantifiers). -/
def QTy : Ty Bool := PTy ⇒ tTy

/-- Semantic type `R = e => e => t` (transitive-verb relations). -/
def RTy : Ty Bool := eTy ⇒ eTy ⇒ tTy

/-- Lexical context `[Q, Q, R]`, head-first de Bruijn order: slot 0 is
`everybody : Q`, slot 1 is `someone : Q`, slot 2 is `admires : R`. -/
def LexCtx : List (Ty Bool) := [QTy, QTy, RTy]

/-- Category-to-type table (contract: S ↦ t, Subj ↦ Q, Obj ↦ Q,
TV ↦ R, VP ↦ P, SP ↦ P). -/
def catTy (c : Cat) : Ty Bool :=
  match c.val with
  | 0 => tTy
  | 1 => QTy
  | 2 => QTy
  | 3 => RTy
  | 4 => PTy
  | _ => PTy

theorem catTy_S : catTy catS = tTy := rfl
theorem catTy_Subj : catTy catSubj = QTy := rfl
theorem catTy_Obj : catTy catObj = QTy := rfl
theorem catTy_TV : catTy catTV = RTy := rfl
theorem catTy_VP : catTy catVP = PTy := rfl
theorem catTy_SP : catTy catSP = PTy := rfl

/-- The seven structural rules by occurrence ID (`Fin 7`); IDs 0–3 are
binary, 4–6 are terminal (contract productions table). Injectivity of
this map is `ruleOf_injective` below: adding two structurally identical
productions with different actions would break that premise and is a
scope change, not a silent extension. -/
def ruleOf (i : Fin 7) : ContextFreeRule Token Cat :=
  match i.val with
  | 0 => ⟨catS, [Symbol.nonterminal catSubj, Symbol.nonterminal catVP]⟩
  | 1 => ⟨catVP, [Symbol.nonterminal catTV, Symbol.nonterminal catObj]⟩
  | 2 => ⟨catS, [Symbol.nonterminal catSP, Symbol.nonterminal catObj]⟩
  | 3 => ⟨catSP, [Symbol.nonterminal catSubj, Symbol.nonterminal catTV]⟩
  | 4 => ⟨catSubj, [Symbol.terminal everybodyTok]⟩
  | 5 => ⟨catObj, [Symbol.terminal someoneTok]⟩
  | _ => ⟨catTV, [Symbol.terminal admiresTok]⟩

/-- The frozen grammar: nonterminals `Cat`, initial `S`, exactly the
seven rules of `ruleOf`. -/
def g : ContextFreeGrammar Token where
  NT := Cat
  initial := catS
  rules := ({ruleOf 0, ruleOf 1, ruleOf 2, ruleOf 3, ruleOf 4, ruleOf 5,
    ruleOf 6} : Finset (ContextFreeRule Token Cat))

/-- Decidable equality on the grammar's nonterminals (as for `ambG.NT`
in Probabilistic.lean). -/
instance : DecidableEq g.NT := inferInstanceAs (DecidableEq Cat)

theorem ruleOf_zero : ruleOf 0 =
    ⟨catS, [Symbol.nonterminal catSubj, Symbol.nonterminal catVP]⟩ := rfl

theorem ruleOf_one : ruleOf 1 =
    ⟨catVP, [Symbol.nonterminal catTV, Symbol.nonterminal catObj]⟩ := rfl

theorem ruleOf_two : ruleOf 2 =
    ⟨catS, [Symbol.nonterminal catSP, Symbol.nonterminal catObj]⟩ := rfl

theorem ruleOf_three : ruleOf 3 =
    ⟨catSP, [Symbol.nonterminal catSubj, Symbol.nonterminal catTV]⟩ := rfl

theorem ruleOf_four : ruleOf 4 =
    ⟨catSubj, [Symbol.terminal everybodyTok]⟩ := rfl

theorem ruleOf_five : ruleOf 5 =
    ⟨catObj, [Symbol.terminal someoneTok]⟩ := rfl

theorem ruleOf_six : ruleOf 6 =
    ⟨catTV, [Symbol.terminal admiresTok]⟩ := rfl

/-- The occurrence-to-rule map is injective in the frozen table. -/
theorem ruleOf_injective : Function.Injective ruleOf := by decide

/-- The grammar has exactly the seven frozen rules. -/
theorem g_rules : g.rules =
    {ruleOf 0, ruleOf 1, ruleOf 2, ruleOf 3, ruleOf 4, ruleOf 5,
      ruleOf 6} := rfl

/-- Seven distinct rules. -/
theorem g_rules_card : g.rules.card = 7 := by decide

theorem mem_rules_iff (r : ContextFreeRule Token Cat) :
    r ∈ g.rules ↔ r = ruleOf 0 ∨ r = ruleOf 1 ∨ r = ruleOf 2 ∨ r = ruleOf 3 ∨
      r = ruleOf 4 ∨ r = ruleOf 5 ∨ r = ruleOf 6 := by
  show r ∈ ({ruleOf 0, ruleOf 1, ruleOf 2, ruleOf 3, ruleOf 4, ruleOf 5,
    ruleOf 6} : Finset (ContextFreeRule Token Cat)) ↔
      r = ruleOf 0 ∨ r = ruleOf 1 ∨ r = ruleOf 2 ∨ r = ruleOf 3 ∨
        r = ruleOf 4 ∨ r = ruleOf 5 ∨ r = ruleOf 6
  simp [Finset.mem_insert, Finset.mem_singleton]

theorem valid_leaf_cases (A : Cat) (a : Token)
    (h : IsValidTree Token g (.leaf A a)) :
    (A = catSubj ∧ a = everybodyTok) ∨ (A = catObj ∧ a = someoneTok) ∨
      (A = catTV ∧ a = admiresTok) := by
  simp only [IsValidTree] at h
  have hmem : (⟨A, [Symbol.terminal a]⟩ : ContextFreeRule Token Cat) ∈ g.rules := h
  rw [mem_rules_iff] at hmem
  rcases hmem with h|h|h|h|h|h|h
  · rw [ruleOf_zero] at h; simp at h
  · rw [ruleOf_one] at h; simp at h
  · rw [ruleOf_two] at h; simp at h
  · rw [ruleOf_three] at h; simp at h
  · rw [ruleOf_four] at h; simp at h; exact Or.inl h
  · rw [ruleOf_five] at h; simp at h; exact Or.inr (Or.inl h)
  · rw [ruleOf_six] at h; simp at h; exact Or.inr (Or.inr h)

theorem valid_node_cases (A B C : Cat)
    (h : (⟨A, [Symbol.nonterminal B, Symbol.nonterminal C]⟩ :
      ContextFreeRule Token Cat) ∈ g.rules) :
    (A = catS ∧ B = catSubj ∧ C = catVP) ∨
      (A = catVP ∧ B = catTV ∧ C = catObj) ∨
      (A = catS ∧ B = catSP ∧ C = catObj) ∨
      (A = catSP ∧ B = catSubj ∧ C = catTV) := by
  rw [mem_rules_iff] at h
  rcases h with h|h|h|h|h|h|h
  · rw [ruleOf_zero] at h; simp at h; exact Or.inl h
  · rw [ruleOf_one] at h; simp at h; exact Or.inr (Or.inl h)
  · rw [ruleOf_two] at h; simp at h; exact Or.inr (Or.inr (Or.inl h))
  · rw [ruleOf_three] at h; simp at h; exact Or.inr (Or.inr (Or.inr h))
  · rw [ruleOf_four] at h; simp at h
  · rw [ruleOf_five] at h; simp at h
  · rw [ruleOf_six] at h; simp at h

/-! ### The seven typed semantic actions -/

/-- Occurrence 0 (`s_subject_wide`): `(qs, vp) ↦ qs (vp)`. -/
def actS1 {Γ : List (Ty Bool)} (qs : Tm Γ QTy) (vp : Tm Γ PTy) :
    Tm Γ tTy :=
  Tm.app qs vp

/-- Occurrence 1 (`vp_apply_object`): `(r, qo) ↦ λ x. qo (λ y. r x y)`.
Outer binder `x`, inner binder `y`; `qo` weakened once, `r` twice; in
the inner body `x = Var.succ Var.zero`, `y = Var.zero`. -/
def actVP {Γ : List (Ty Bool)} (r : Tm Γ RTy) (qo : Tm Γ QTy) :
    Tm Γ PTy :=
  Tm.lam (Tm.app (Tm.weaken qo)
    (Tm.lam (Tm.app (Tm.app (Tm.weaken (Tm.weaken r))
      (Tm.var (Var.succ Var.zero))) (Tm.var Var.zero))))

/-- Occurrence 2 (`s_object_wide`): `(sp, qo) ↦ qo (sp)`; the right
child's generalized quantifier takes scope over the left child's
predicate. -/
def actSObj {Γ : List (Ty Bool)} (sp : Tm Γ PTy) (qo : Tm Γ QTy) :
    Tm Γ tTy :=
  Tm.app qo sp

/-- Occurrence 3 (`sp_apply_subject`): `(qs, r) ↦ λ y. qs (λ x. r x y)`.
Outer binder `y`, inner binder `x`; `qs` weakened once, `r` twice; in
the inner body `x = Var.zero`, `y = Var.succ Var.zero`. -/
def actSP {Γ : List (Ty Bool)} (qs : Tm Γ QTy) (r : Tm Γ RTy) :
    Tm Γ PTy :=
  Tm.lam (Tm.app (Tm.weaken qs)
    (Tm.lam (Tm.app (Tm.app (Tm.weaken (Tm.weaken r))
      (Tm.var Var.zero)) (Tm.var (Var.succ Var.zero)))))

/-- Occurrence 4 (`lex_everybody`): lexical slot 0. -/
def everybodyTm : Tm LexCtx QTy := Tm.var Var.zero

/-- Occurrence 5 (`lex_someone`): lexical slot 1. Same semantic type
`Q` as `everybodyTm`, different variable position and interpretation;
the two entries must not be identified by type. -/
def someoneTm : Tm LexCtx QTy := Tm.var (Var.succ Var.zero)

/-- Occurrence 6 (`lex_admires`): lexical slot 2. -/
def admiresTm : Tm LexCtx RTy := Tm.var (Var.succ (Var.succ Var.zero))

/-! ### The valid-domain compiler -/

/-- Compile a valid derivation tree to the intrinsic term at its root
category's semantic type, by structural recursion on the tree, using
exactly the seven actions above. Invalid trees have no validity
witness, so no default term is returned for an invalid rule. Proof
arguments do not affect the output (`compile_proof_irrel`). -/
def compile : (tr : PDerivTree Cat Token) → IsValidTree Token g tr →
    Tm LexCtx (catTy tr.rootOf)
  | .leaf A a, h => by
      refine if h1 : A = catSubj ∧ a = everybodyTok then ?_ else ?_
      · obtain ⟨rfl, rfl⟩ := h1
        exact everybodyTm
      · refine if h2 : A = catObj ∧ a = someoneTok then ?_ else ?_
        · obtain ⟨rfl, rfl⟩ := h2
          exact someoneTm
        · refine if h3 : A = catTV ∧ a = admiresTok then ?_ else ?_
          · obtain ⟨rfl, rfl⟩ := h3
            exact admiresTm
          · have hc := valid_leaf_cases A a h
            have hfalse : False := by
              rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact h1 ⟨rfl, rfl⟩
              · exact h2 ⟨rfl, rfl⟩
              · exact h3 ⟨rfl, rfl⟩
            exact False.elim hfalse
  | .node A B C l r, h => by
      have h' : (⟨A, [Symbol.nonterminal B, Symbol.nonterminal C]⟩ :
          ContextFreeRule Token Cat) ∈ g.rules ∧
          l.rootOf = B ∧ r.rootOf = C ∧
          IsValidTree Token g l ∧ IsValidTree Token g r := h
      obtain ⟨hrule, hBl, hCr, hVl, hVr⟩ := h'
      have cl := compile l hVl
      have cr := compile r hVr
      refine if h1 : A = catS ∧ B = catSubj ∧ C = catVP then ?_ else ?_
      · obtain ⟨rfl, rfl, rfl⟩ := h1
        have e1 : Tm LexCtx (catTy catSubj) := hBl ▸ cl
        have e2 : Tm LexCtx (catTy catVP) := hCr ▸ cr
        exact actS1 e1 e2
      · refine if h2 : A = catVP ∧ B = catTV ∧ C = catObj then ?_ else ?_
        · obtain ⟨rfl, rfl, rfl⟩ := h2
          have e1 : Tm LexCtx (catTy catTV) := hBl ▸ cl
          have e2 : Tm LexCtx (catTy catObj) := hCr ▸ cr
          exact actVP e1 e2
        · refine if h3 : A = catS ∧ B = catSP ∧ C = catObj then ?_ else ?_
          · obtain ⟨rfl, rfl, rfl⟩ := h3
            have e1 : Tm LexCtx (catTy catSP) := hBl ▸ cl
            have e2 : Tm LexCtx (catTy catObj) := hCr ▸ cr
            exact actSObj e1 e2
          · refine if h4 : A = catSP ∧ B = catSubj ∧ C = catTV then ?_ else ?_
            · obtain ⟨rfl, rfl, rfl⟩ := h4
              have e1 : Tm LexCtx (catTy catSubj) := hBl ▸ cl
              have e2 : Tm LexCtx (catTy catTV) := hCr ▸ cr
              exact actSP e1 e2
            · have hc := valid_node_cases A B C hrule
              have hfalse : False := by
                rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
                · exact h1 ⟨rfl, rfl, rfl⟩
                · exact h2 ⟨rfl, rfl, rfl⟩
                · exact h3 ⟨rfl, rfl, rfl⟩
                · exact h4 ⟨rfl, rfl, rfl⟩
              exact False.elim hfalse

/-- Compile a tree known to have root `B`, at `B`'s semantic type;
the root equality transports the dependent result type of `compile`. -/
def compileAt (B : Cat) (tr : PDerivTree Cat Token) (hroot : tr.rootOf = B)
    (h : IsValidTree Token g tr) : Tm LexCtx (catTy B) :=
  hroot ▸ compile tr h

/-- The compiler's output does not depend on the validity proof. -/
theorem compile_proof_irrel (tr : PDerivTree Cat Token)
    (h₁ h₂ : IsValidTree Token g tr) : compile tr h₁ = compile tr h₂ := by
  rfl

/-- Action equation, occurrence 0 (`s_subject_wide`). -/
theorem compile_node_s_subject_wide (l r : PDerivTree Cat Token)
    (hVl : IsValidTree Token g l) (hVr : IsValidTree Token g r)
    (hl : l.rootOf = catSubj) (hr : r.rootOf = catVP)
    (h : IsValidTree Token g (PDerivTree.node catS catSubj catVP l r)) :
    compile (PDerivTree.node catS catSubj catVP l r) h =
      actS1 (compileAt catSubj l hl hVl) (compileAt catVP r hr hVr) := by
  have hdec : (⟨catS, [Symbol.nonterminal catSubj, Symbol.nonterminal catVP]⟩ :
      ContextFreeRule Token g.NT) ∈ g.rules := by decide
  have hcanon : h = ⟨hdec, hl, hr, hVl, hVr⟩ := rfl
  rw [hcanon]
  rfl

/-- Action equation, occurrence 1 (`vp_apply_object`). -/
theorem compile_node_vp_apply_object (l r : PDerivTree Cat Token)
    (hVl : IsValidTree Token g l) (hVr : IsValidTree Token g r)
    (hl : l.rootOf = catTV) (hr : r.rootOf = catObj)
    (h : IsValidTree Token g (PDerivTree.node catVP catTV catObj l r)) :
    compile (PDerivTree.node catVP catTV catObj l r) h =
      actVP (compileAt catTV l hl hVl) (compileAt catObj r hr hVr) := by
  have hdec : (⟨catVP, [Symbol.nonterminal catTV, Symbol.nonterminal catObj]⟩ :
      ContextFreeRule Token g.NT) ∈ g.rules := by decide
  have hcanon : h = ⟨hdec, hl, hr, hVl, hVr⟩ := rfl
  rw [hcanon]
  rfl

/-- Action equation, occurrence 2 (`s_object_wide`). -/
theorem compile_node_s_object_wide (l r : PDerivTree Cat Token)
    (hVl : IsValidTree Token g l) (hVr : IsValidTree Token g r)
    (hl : l.rootOf = catSP) (hr : r.rootOf = catObj)
    (h : IsValidTree Token g (PDerivTree.node catS catSP catObj l r)) :
    compile (PDerivTree.node catS catSP catObj l r) h =
      actSObj (compileAt catSP l hl hVl) (compileAt catObj r hr hVr) := by
  have hdec : (⟨catS, [Symbol.nonterminal catSP, Symbol.nonterminal catObj]⟩ :
      ContextFreeRule Token g.NT) ∈ g.rules := by decide
  have hcanon : h = ⟨hdec, hl, hr, hVl, hVr⟩ := rfl
  rw [hcanon]
  rfl

/-- Action equation, occurrence 3 (`sp_apply_subject`). -/
theorem compile_node_sp_apply_subject (l r : PDerivTree Cat Token)
    (hVl : IsValidTree Token g l) (hVr : IsValidTree Token g r)
    (hl : l.rootOf = catSubj) (hr : r.rootOf = catTV)
    (h : IsValidTree Token g (PDerivTree.node catSP catSubj catTV l r)) :
    compile (PDerivTree.node catSP catSubj catTV l r) h =
      actSP (compileAt catSubj l hl hVl) (compileAt catTV r hr hVr) := by
  have hdec : (⟨catSP, [Symbol.nonterminal catSubj, Symbol.nonterminal catTV]⟩ :
      ContextFreeRule Token g.NT) ∈ g.rules := by decide
  have hcanon : h = ⟨hdec, hl, hr, hVl, hVr⟩ := rfl
  rw [hcanon]
  rfl

/-- Action equation, occurrence 4 (`lex_everybody`). -/
theorem compile_leaf_everybody
    (h : IsValidTree Token g (PDerivTree.leaf catSubj everybodyTok)) :
    compile (PDerivTree.leaf catSubj everybodyTok) h = everybodyTm := by
  have hdec : IsValidTree Token g (PDerivTree.leaf catSubj everybodyTok) := by
    show (⟨catSubj, [Symbol.terminal everybodyTok]⟩ :
      ContextFreeRule Token g.NT) ∈ g.rules
    decide
  have hcanon : h = hdec := rfl
  rw [hcanon]
  rfl

/-- Action equation, occurrence 5 (`lex_someone`). -/
theorem compile_leaf_someone
    (h : IsValidTree Token g (PDerivTree.leaf catObj someoneTok)) :
    compile (PDerivTree.leaf catObj someoneTok) h = someoneTm := by
  have hdec : IsValidTree Token g (PDerivTree.leaf catObj someoneTok) := by
    show (⟨catObj, [Symbol.terminal someoneTok]⟩ :
      ContextFreeRule Token g.NT) ∈ g.rules
    decide
  have hcanon : h = hdec := rfl
  rw [hcanon]
  rfl

/-- Action equation, occurrence 6 (`lex_admires`). -/
theorem compile_leaf_admires
    (h : IsValidTree Token g (PDerivTree.leaf catTV admiresTok)) :
    compile (PDerivTree.leaf catTV admiresTok) h = admiresTm := by
  have hdec : IsValidTree Token g (PDerivTree.leaf catTV admiresTok) := by
    show (⟨catTV, [Symbol.terminal admiresTok]⟩ :
      ContextFreeRule Token g.NT) ∈ g.rules
    decide
  have hcanon : h = hdec := rfl
  rw [hcanon]
  rfl

/-! ### The two designated parses and the exact classification -/

/-- Surface parse (occurrences preorder 0, 4, 1, 6, 5):
`S → Subj VP`, giving `everybody (λ x. someone (λ y. admires x y))`. -/
def surfaceTree : PDerivTree Cat Token :=
  PDerivTree.node catS catSubj catVP
    (PDerivTree.leaf catSubj everybodyTok)
    (PDerivTree.node catVP catTV catObj
      (PDerivTree.leaf catTV admiresTok)
      (PDerivTree.leaf catObj someoneTok))
/-- Inverse parse (occurrences preorder 2, 3, 4, 6, 5):
`S → SP Obj`, giving `someone (λ y. everybody (λ x. admires x y))`.
This bracketing is an explicitly artificial scope alternative, not a
claim about English syntax. -/
def inverseTree : PDerivTree Cat Token :=
  PDerivTree.node catS catSP catObj
    (PDerivTree.node catSP catSubj catTV
      (PDerivTree.leaf catSubj everybodyTok)
      (PDerivTree.leaf catTV admiresTok))
    (PDerivTree.leaf catObj someoneTok)

/-- The frozen sentence: everybody admires someone. -/
def word : List Token := [everybodyTok, admiresTok, someoneTok]

theorem surfaceTree_valid : IsValidTree Token g surfaceTree := by
  simp only [surfaceTree, IsValidTree, PDerivTree.rootOf]
  refine ⟨?_, rfl, rfl, ?_, ?_, rfl, rfl, ?_, ?_⟩ <;> decide
theorem inverseTree_valid : IsValidTree Token g inverseTree := by
  simp only [inverseTree, IsValidTree, PDerivTree.rootOf]
  refine ⟨?_, rfl, rfl, ⟨?_, rfl, rfl, ?_, ?_⟩, ?_⟩ <;> decide

theorem surfaceTree_root : surfaceTree.rootOf = catS := rfl
theorem inverseTree_root : inverseTree.rootOf = catS := rfl

theorem surfaceTree_yield : surfaceTree.yieldOf = word := rfl
theorem inverseTree_yield : inverseTree.yieldOf = word := rfl

theorem surfaceTree_depth : surfaceTree.depthOf = 3 := rfl
theorem inverseTree_depth : inverseTree.depthOf = 3 := rfl

/-- The two parses of the same token string are distinct trees. -/
theorem surface_ne_inverse : surfaceTree ≠ inverseTree := by decide

theorem valid_root_subj (tr : PDerivTree Cat Token) :
    IsValidTree Token g tr → tr.rootOf = catSubj →
    tr = PDerivTree.leaf catSubj everybodyTok := by
  cases tr with
  | leaf A a =>
    intro hvalid hroot
    rcases valid_leaf_cases A a hvalid with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact absurd hroot (by decide)
    · exact absurd hroot (by decide)
  | node A B C l r =>
    intro hvalid hroot
    have h' : (⟨A, [Symbol.nonterminal B, Symbol.nonterminal C]⟩ :
        ContextFreeRule Token Cat) ∈ g.rules ∧
        l.rootOf = B ∧ r.rootOf = C ∧
        IsValidTree Token g l ∧ IsValidTree Token g r := hvalid
    obtain ⟨hrule, _hBl, _hCr, _hVl, _hVr⟩ := h'
    rcases valid_node_cases A B C hrule with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [PDerivTree.rootOf] at hroot
      exact absurd hroot (by decide)
    · simp only [PDerivTree.rootOf] at hroot
      exact absurd hroot (by decide)
    · simp only [PDerivTree.rootOf] at hroot
      exact absurd hroot (by decide)
    · simp only [PDerivTree.rootOf] at hroot
      exact absurd hroot (by decide)

theorem valid_root_obj (tr : PDerivTree Cat Token) :
    IsValidTree Token g tr → tr.rootOf = catObj →
    tr = PDerivTree.leaf catObj someoneTok := by
  cases tr with
  | leaf A a =>
    intro hvalid hroot
    rcases valid_leaf_cases A a hvalid with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd hroot (by decide)
    · rfl
    · exact absurd hroot (by decide)
  | node A B C l r =>
    intro hvalid hroot
    have h' : (⟨A, [Symbol.nonterminal B, Symbol.nonterminal C]⟩ :
        ContextFreeRule Token Cat) ∈ g.rules ∧
        l.rootOf = B ∧ r.rootOf = C ∧
        IsValidTree Token g l ∧ IsValidTree Token g r := hvalid
    obtain ⟨hrule, _hBl, _hCr, _hVl, _hVr⟩ := h'
    rcases valid_node_cases A B C hrule with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [PDerivTree.rootOf] at hroot
      exact absurd hroot (by decide)
    · simp only [PDerivTree.rootOf] at hroot
      exact absurd hroot (by decide)
    · simp only [PDerivTree.rootOf] at hroot
      exact absurd hroot (by decide)
    · simp only [PDerivTree.rootOf] at hroot
      exact absurd hroot (by decide)

theorem valid_root_tv (tr : PDerivTree Cat Token) :
    IsValidTree Token g tr → tr.rootOf = catTV →
    tr = PDerivTree.leaf catTV admiresTok := by
  cases tr with
  | leaf A a =>
    intro hvalid hroot
    rcases valid_leaf_cases A a hvalid with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd hroot (by decide)
    · exact absurd hroot (by decide)
    · rfl
  | node A B C l r =>
    intro hvalid hroot
    have h' : (⟨A, [Symbol.nonterminal B, Symbol.nonterminal C]⟩ :
        ContextFreeRule Token Cat) ∈ g.rules ∧
        l.rootOf = B ∧ r.rootOf = C ∧
        IsValidTree Token g l ∧ IsValidTree Token g r := hvalid
    obtain ⟨hrule, _hBl, _hCr, _hVl, _hVr⟩ := h'
    rcases valid_node_cases A B C hrule with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [PDerivTree.rootOf] at hroot
      exact absurd hroot (by decide)
    · simp only [PDerivTree.rootOf] at hroot
      exact absurd hroot (by decide)
    · simp only [PDerivTree.rootOf] at hroot
      exact absurd hroot (by decide)
    · simp only [PDerivTree.rootOf] at hroot
      exact absurd hroot (by decide)

theorem valid_root_vp (tr : PDerivTree Cat Token) :
    IsValidTree Token g tr → tr.rootOf = catVP →
    tr = PDerivTree.node catVP catTV catObj
      (PDerivTree.leaf catTV admiresTok)
      (PDerivTree.leaf catObj someoneTok) := by
  cases tr with
  | leaf A a =>
    intro hvalid hroot
    rcases valid_leaf_cases A a hvalid with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd hroot (by decide)
    · exact absurd hroot (by decide)
    · exact absurd hroot (by decide)
  | node A B C l r =>
    intro hvalid hroot
    have h' : (⟨A, [Symbol.nonterminal B, Symbol.nonterminal C]⟩ :
        ContextFreeRule Token Cat) ∈ g.rules ∧
        l.rootOf = B ∧ r.rootOf = C ∧
        IsValidTree Token g l ∧ IsValidTree Token g r := hvalid
    obtain ⟨hrule, hBl, hCr, hVl, hVr⟩ := h'
    rcases valid_node_cases A B C hrule with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [PDerivTree.rootOf] at hroot
      exact absurd hroot (by decide)
    · have hl := valid_root_tv l hVl hBl
      have hr := valid_root_obj r hVr hCr
      rw [hl, hr]
    · simp only [PDerivTree.rootOf] at hroot
      exact absurd hroot (by decide)
    · simp only [PDerivTree.rootOf] at hroot
      exact absurd hroot (by decide)

theorem valid_root_sp (tr : PDerivTree Cat Token) :
    IsValidTree Token g tr → tr.rootOf = catSP →
    tr = PDerivTree.node catSP catSubj catTV
      (PDerivTree.leaf catSubj everybodyTok)
      (PDerivTree.leaf catTV admiresTok) := by
  cases tr with
  | leaf A a =>
    intro hvalid hroot
    rcases valid_leaf_cases A a hvalid with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd hroot (by decide)
    · exact absurd hroot (by decide)
    · exact absurd hroot (by decide)
  | node A B C l r =>
    intro hvalid hroot
    have h' : (⟨A, [Symbol.nonterminal B, Symbol.nonterminal C]⟩ :
        ContextFreeRule Token Cat) ∈ g.rules ∧
        l.rootOf = B ∧ r.rootOf = C ∧
        IsValidTree Token g l ∧ IsValidTree Token g r := hvalid
    obtain ⟨hrule, hBl, hCr, hVl, hVr⟩ := h'
    rcases valid_node_cases A B C hrule with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [PDerivTree.rootOf] at hroot
      exact absurd hroot (by decide)
    · simp only [PDerivTree.rootOf] at hroot
      exact absurd hroot (by decide)
    · simp only [PDerivTree.rootOf] at hroot
      exact absurd hroot (by decide)
    · have hl := valid_root_subj l hVl hBl
      have hr := valid_root_tv r hVr hCr
      rw [hl, hr]

theorem valid_root_s (tr : PDerivTree Cat Token) :
    IsValidTree Token g tr → tr.rootOf = catS →
    tr = surfaceTree ∨ tr = inverseTree := by
  cases tr with
  | leaf A a =>
    intro hvalid hroot
    rcases valid_leaf_cases A a hvalid with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd hroot (by decide)
    · exact absurd hroot (by decide)
    · exact absurd hroot (by decide)
  | node A B C l r =>
    intro hvalid hroot
    have h' : (⟨A, [Symbol.nonterminal B, Symbol.nonterminal C]⟩ :
        ContextFreeRule Token Cat) ∈ g.rules ∧
        l.rootOf = B ∧ r.rootOf = C ∧
        IsValidTree Token g l ∧ IsValidTree Token g r := hvalid
    obtain ⟨hrule, hBl, hCr, hVl, hVr⟩ := h'
    rcases valid_node_cases A B C hrule with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have hl := valid_root_subj l hVl hBl
      have hr := valid_root_vp r hVr hCr
      left
      unfold surfaceTree
      rw [hl, hr]
    · simp only [PDerivTree.rootOf] at hroot
      exact absurd hroot (by decide)
    · have hl := valid_root_sp l hVl hBl
      have hr := valid_root_obj r hVr hCr
      right
      unfold inverseTree
      rw [hl, hr]
    · simp only [PDerivTree.rootOf] at hroot
      exact absurd hroot (by decide)

/-- **Exact classification** (leaf headline): a tree is a valid
`S`-rooted tree of this acyclic seven-rule fragment iff it is the
surface tree or the inverse tree. This classifies structural
`PDerivTree`s only, not arbitrary rewrite traces or English parses. -/
theorem valid_sentence_trees (tr : PDerivTree Cat Token) :
    (IsValidTree Token g tr ∧ tr.rootOf = catS) ↔
      tr = surfaceTree ∨ tr = inverseTree := by
  constructor
  · rintro ⟨hvalid, hroot⟩
    exact valid_root_s tr hvalid hroot
  · rintro (rfl | rfl)
    · exact ⟨surfaceTree_valid, surfaceTree_root⟩
    · exact ⟨inverseTree_valid, inverseTree_root⟩

/-- Both designated trees occur in the bounded valid-tree set at
depth 3 (via the `mem_treesUpTo_iff` interface). -/
theorem surfaceTree_mem_treesUpTo :
    surfaceTree ∈ treesUpTo Token g 3 catS word := by
  refine (mem_treesUpTo_iff Token g 3 catS word surfaceTree).mpr ?_
  exact ⟨surfaceTree_valid, Nat.le_of_eq surfaceTree_depth, surfaceTree_yield,
    surfaceTree_root⟩

theorem inverseTree_mem_treesUpTo :
    inverseTree ∈ treesUpTo Token g 3 catS word := by
  refine (mem_treesUpTo_iff Token g 3 catS word inverseTree).mpr ?_
  exact ⟨inverseTree_valid, Nat.le_of_eq inverseTree_depth, inverseTree_yield,
    inverseTree_root⟩

/-- The frozen sentence belongs to the grammar's language (via the
existing grammar-language interface; no CYK implementation and no
general tree/derivation completeness theorem is claimed). -/
theorem word_mem_language : word ∈ g.language := by
  rw [ContextFreeGrammar.mem_language_iff]
  have p0 : g.Produces [Symbol.nonterminal catS]
      [Symbol.nonterminal catSubj, Symbol.nonterminal catVP] :=
    ⟨ruleOf 0, (by simp [mem_rules_iff] : ruleOf 0 ∈ g.rules),
      ContextFreeRule.Rewrites.head []⟩
  have p4 : g.Produces [Symbol.nonterminal catSubj, Symbol.nonterminal catVP]
      [Symbol.terminal everybodyTok, Symbol.nonterminal catVP] :=
    ⟨ruleOf 4, (by simp [mem_rules_iff] : ruleOf 4 ∈ g.rules),
      ContextFreeRule.Rewrites.head [Symbol.nonterminal catVP]⟩
  have p1 : g.Produces
      [Symbol.terminal everybodyTok, Symbol.nonterminal catVP]
      [Symbol.terminal everybodyTok, Symbol.nonterminal catTV,
        Symbol.nonterminal catObj] :=
    ⟨ruleOf 1, (by simp [mem_rules_iff] : ruleOf 1 ∈ g.rules),
      ContextFreeRule.Rewrites.cons (Symbol.terminal everybodyTok)
        (ContextFreeRule.Rewrites.head [])⟩
  have p6 : g.Produces [Symbol.terminal everybodyTok, Symbol.nonterminal catTV,
        Symbol.nonterminal catObj]
      [Symbol.terminal everybodyTok, Symbol.terminal admiresTok,
        Symbol.nonterminal catObj] :=
    ⟨ruleOf 6, (by simp [mem_rules_iff] : ruleOf 6 ∈ g.rules),
      ContextFreeRule.Rewrites.cons (Symbol.terminal everybodyTok)
        (ContextFreeRule.Rewrites.head [Symbol.nonterminal catObj])⟩
  have p5 : g.Produces [Symbol.terminal everybodyTok, Symbol.terminal admiresTok,
        Symbol.nonterminal catObj]
      [Symbol.terminal everybodyTok, Symbol.terminal admiresTok,
        Symbol.terminal someoneTok] :=
    ⟨ruleOf 5, (by simp [mem_rules_iff] : ruleOf 5 ∈ g.rules),
      ContextFreeRule.Rewrites.cons (Symbol.terminal everybodyTok)
        (ContextFreeRule.Rewrites.cons (Symbol.terminal admiresTok)
          (ContextFreeRule.Rewrites.head []))⟩
  have d := ContextFreeGrammar.Derives.trans
    (ContextFreeGrammar.Produces.single p0)
    (ContextFreeGrammar.Derives.trans
      (ContextFreeGrammar.Produces.single p4)
      (ContextFreeGrammar.Derives.trans
        (ContextFreeGrammar.Produces.single p1)
        (ContextFreeGrammar.Derives.trans
          (ContextFreeGrammar.Produces.single p6)
          (ContextFreeGrammar.Produces.single p5))))
  exact d


end Cslib.Language.CompositionalFragment
