/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Computability.Languages.RegularLanguage
public import Mathlib.Computability.Language
public import Mathlib.Computability.RegularExpressions

open scoped Computability

/-!
# Generalized regular expressions

Mathlib's ordinary regular expressions extended with complement, with
concrete denotation into `Language`, star height, and regularity /
bounded-height predicates for the generalized star height problem.

## Main definitions

* `Cslib.Language.GenRegExp`: generalized regular expressions over an alphabet.
* `Cslib.Language.GenRegExp.denote`: denotation as a `Language`.
* `Cslib.Language.GenRegExp.starHeight`: generalized star height.
* `Cslib.Language.HasGenHeightLe`: bounded generalized star height.
Regularity is Mathlib's `Language.IsRegular`, shared with the rest of
`Cslib.Language`.

## Main results

* `Cslib.Language.GenRegExp.denote_isRegular`: every generalized regular
  expression denotes a regular language; hence
  `Cslib.Language.HasGenHeightLe.isRegular`.
* `Cslib.Language.HasGenHeightLe.mono`, `.compl`, `.add`, `.mul`, `.kstar`:
  bounded height is monotone and closed under the operations, and a star
  raises the bound by at most one; `Cslib.Language.hasGenHeightLe_regex`: an ordinary
  expression bounds the height by its own star height.
* Height zero (star-free in the generalized sense):
  `Cslib.Language.hasGenHeightLe_zero_top` (`Σ*` is the complement of `∅`),
  `Cslib.Language.hasGenHeightLe_zero_singleton` (single words).
* `Cslib.Language.hasGenHeightLe_zero_kstar_true`: over `Bool`, `true*` has
  generalized star height zero although it is written with a star: it is the
  complement of `Σ* false Σ*`.
-/

@[expose] public section

namespace Cslib.Language

universe u

variable {α : Type u}

/-- Star height of an ordinary regular expression: the nesting depth of
`star` (`zero`, `epsilon`, and `char` have height zero). -/
def regularStarHeight : RegularExpression α → ℕ
  | .zero => 0
  | .epsilon => 0
  | .char _ => 0
  | .plus e₁ e₂ => max (regularStarHeight e₁) (regularStarHeight e₂)
  | .comp e₁ e₂ => max (regularStarHeight e₁) (regularStarHeight e₂)
  | .star e => regularStarHeight e + 1

/-- Generalized regular expressions: Mathlib's ordinary regular
expressions extended with complement. -/
inductive GenRegExp (α : Type u) : Type u
  | ofReg : RegularExpression α → GenRegExp α
  | compl : GenRegExp α → GenRegExp α
  | plus : GenRegExp α → GenRegExp α → GenRegExp α
  | comp : GenRegExp α → GenRegExp α → GenRegExp α
  | star : GenRegExp α → GenRegExp α

namespace GenRegExp

/-- Denotation of a generalized regular expression as a language. -/
def denote : GenRegExp α → Language α
  | .ofReg e => e.matches'
  | .compl e => (denote e)ᶜ
  | .plus e₁ e₂ => denote e₁ + denote e₂
  | .comp e₁ e₂ => denote e₁ * denote e₂
  | .star e => (denote e)∗

/-- Generalized star height: the nesting depth of `star`, counting stars
in the ordinary base expression as well. -/
def starHeight : GenRegExp α → ℕ
  | .ofReg e => regularStarHeight e
  | .compl e => starHeight e
  | .plus e₁ e₂ => max (starHeight e₁) (starHeight e₂)
  | .comp e₁ e₂ => max (starHeight e₁) (starHeight e₂)
  | .star e => starHeight e + 1

@[simp]
theorem starHeight_ofReg (e : RegularExpression α) :
    (ofReg e).starHeight = regularStarHeight e :=
  rfl

/-- **Generalized regular expressions denote regular languages.** -/
theorem denote_isRegular : ∀ e : GenRegExp α, e.denote.IsRegular
  | .ofReg _ => IsRegular.regex
  | .compl e => IsRegular.compl (denote_isRegular e)
  | .plus e₁ e₂ => IsRegular.add (denote_isRegular e₁) (denote_isRegular e₂)
  | .comp e₁ e₂ => IsRegular.mul (denote_isRegular e₁) (denote_isRegular e₂)
  | .star e => IsRegular.kstar (denote_isRegular e)

/-- `Σ*`, written without a star: the complement of the empty language. -/
def top : GenRegExp α :=
  compl (ofReg 0)

@[simp]
theorem denote_top : (top : GenRegExp α).denote = ⊤ := by
  change ((0 : RegularExpression α).matches')ᶜ = ⊤
  rw [RegularExpression.matches'_zero]
  exact compl_bot

@[simp]
theorem starHeight_top : (top : GenRegExp α).starHeight = 0 :=
  rfl

end GenRegExp

/-- A language has generalized star height at most `n`. -/
def HasGenHeightLe (L : Language α) (n : ℕ) : Prop :=
  ∃ e : GenRegExp α, e.denote = L ∧ e.starHeight ≤ n

namespace HasGenHeightLe

variable {L L₁ L₂ : Language α} {m n : ℕ}

theorem mono (h : HasGenHeightLe L m) (hmn : m ≤ n) : HasGenHeightLe L n :=
  let ⟨e, he, hh⟩ := h
  ⟨e, he, hh.trans hmn⟩

/-- Languages of bounded generalized star height are regular. -/
theorem isRegular (h : HasGenHeightLe L n) : L.IsRegular := by
  obtain ⟨e, rfl, -⟩ := h
  exact e.denote_isRegular

theorem compl (h : HasGenHeightLe L n) : HasGenHeightLe Lᶜ n :=
  let ⟨e, he, hh⟩ := h
  ⟨.compl e, by rw [← he]; rfl, hh⟩

theorem add (h₁ : HasGenHeightLe L₁ n) (h₂ : HasGenHeightLe L₂ n) :
    HasGenHeightLe (L₁ + L₂) n :=
  let ⟨e₁, he₁, hh₁⟩ := h₁
  let ⟨e₂, he₂, hh₂⟩ := h₂
  ⟨.plus e₁ e₂, by rw [← he₁, ← he₂]; rfl, max_le hh₁ hh₂⟩

theorem mul (h₁ : HasGenHeightLe L₁ n) (h₂ : HasGenHeightLe L₂ n) :
    HasGenHeightLe (L₁ * L₂) n :=
  let ⟨e₁, he₁, hh₁⟩ := h₁
  let ⟨e₂, he₂, hh₂⟩ := h₂
  ⟨.comp e₁ e₂, by rw [← he₁, ← he₂]; rfl, max_le hh₁ hh₂⟩

/-- A star raises the height bound by at most one. -/
theorem kstar (h : HasGenHeightLe L n) : HasGenHeightLe L∗ (n + 1) :=
  let ⟨e, he, hh⟩ := h
  ⟨.star e, by rw [← he]; rfl, Nat.succ_le_succ hh⟩

end HasGenHeightLe

/-- An ordinary regular expression bounds the generalized star height of its language by its
own star height. -/
theorem hasGenHeightLe_regex (e : RegularExpression α) :
    HasGenHeightLe e.matches' (regularStarHeight e) :=
  ⟨.ofReg e, rfl, le_rfl⟩

theorem hasGenHeightLe_zero_top : HasGenHeightLe (⊤ : Language α) 0 :=
  ⟨GenRegExp.top, GenRegExp.denote_top, le_rfl⟩

theorem hasGenHeightLe_zero_zero : HasGenHeightLe (0 : Language α) 0 :=
  ⟨.ofReg 0, RegularExpression.matches'_zero, le_rfl⟩

theorem hasGenHeightLe_zero_one : HasGenHeightLe (1 : Language α) 0 :=
  ⟨.ofReg 1, RegularExpression.matches'_epsilon, le_rfl⟩

/-- Single words have generalized star height zero. -/
theorem hasGenHeightLe_zero_singleton : ∀ w : List α, HasGenHeightLe ({w} : Language α) 0
  | [] => ⟨.ofReg 1, by
      change RegularExpression.matches' (1 : RegularExpression α) = _
      rw [RegularExpression.matches'_epsilon, Language.one_def]
      exact rfl, le_rfl⟩
  | a :: w => by
      have h : ({a :: w} : Language α) = {[a]} * {w} := by
        ext x
        simp [Language.mem_mul, eq_comm]
      rw [h]
      exact HasGenHeightLe.mul ⟨.ofReg (.char a), RegularExpression.matches'_char a, le_rfl⟩
        (hasGenHeightLe_zero_singleton w)

theorem mem_top_mul_false_mul_top {w : List Bool} :
    w ∈ (⊤ * {[false]} * ⊤ : Language Bool) ↔ false ∈ w := by
  constructor
  · intro h
    obtain ⟨u, hu, y, -, rfl⟩ := Language.mem_mul.1 h
    obtain ⟨x, -, f, hf, rfl⟩ := Language.mem_mul.1 hu
    rw [Set.mem_singleton_iff.1 hf]
    simp
  · intro h
    obtain ⟨x, y, rfl⟩ := List.append_of_mem h
    exact Language.mem_mul.2 ⟨x ++ [false], Language.mem_mul.2 ⟨x, trivial, [false], rfl, rfl⟩,
      y, trivial, by simp⟩

theorem mem_kstar_true {w : List Bool} :
    w ∈ ({[true]} : Language Bool)∗ ↔ ∀ b ∈ w, b = true := by
  constructor
  · intro h b hb
    obtain ⟨L, rfl, hL⟩ := Language.mem_kstar.1 h
    obtain ⟨l, hl, hbl⟩ := List.mem_flatten.1 hb
    rw [Set.mem_singleton_iff.1 (hL l hl)] at hbl
    simpa using hbl
  · intro h
    refine Language.mem_kstar.2 ⟨w.map fun _ => [true], ?_, by simp⟩
    induction w with
    | nil => rfl
    | cons b w ih =>
        rw [h b List.mem_cons_self, List.map_cons, List.flatten_cons, List.singleton_append]
        exact congrArg _ (ih fun c hc => h c (List.mem_cons_of_mem _ hc))

/-- **`true*` is star-free in the generalized sense**: over `Bool` it is the complement of
`Σ* false Σ*`. -/
theorem hasGenHeightLe_zero_kstar_true : HasGenHeightLe (({[true]} : Language Bool)∗) 0 := by
  have h : ({[true]} : Language Bool)∗ = (⊤ * {[false]} * ⊤)ᶜ := by
    ext w
    rw [mem_kstar_true]
    change _ ↔ ¬ (w ∈ (⊤ * {[false]} * ⊤ : Language Bool))
    rw [mem_top_mul_false_mul_top]
    constructor
    · intro h hf
      exact Bool.false_ne_true (h false hf)
    · intro h b hb
      cases b
      · exact absurd hb h
      · rfl
  rw [h]
  exact HasGenHeightLe.compl (HasGenHeightLe.mul (HasGenHeightLe.mul hasGenHeightLe_zero_top
    ⟨.ofReg (.char false), RegularExpression.matches'_char false, le_rfl⟩) hasGenHeightLe_zero_top)

end Cslib.Language
