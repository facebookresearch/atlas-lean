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
-/

@[expose] public section

namespace Cslib.Language

universe u

variable {α : Type u}

/-- **Star height of a regular expression.** The star height of an ordinary regular expression
is the nesting depth of the Kleene star in it: the expressions for the empty language and the
empty word and the single letters have star height $0$; a union $e_1 + e_2$ and a concatenation
$e_1 e_2$ have the larger of the star heights of $e_1$ and $e_2$; and $e^*$ has star height one
more than $e$. -/
def regularStarHeight : RegularExpression α → ℕ
  | .zero => 0
  | .epsilon => 0
  | .char _ => 0
  | .plus e₁ e₂ => max (regularStarHeight e₁) (regularStarHeight e₂)
  | .comp e₁ e₂ => max (regularStarHeight e₁) (regularStarHeight e₂)
  | .star e => regularStarHeight e + 1

/-- **Generalized regular expressions.** A generalized regular expression over an alphabet
$\alpha$ is built from ordinary regular expressions over $\alpha$ by complement, union,
concatenation and Kleene star: every ordinary regular expression over $\alpha$ is one, and if
$e$, $e_1$, $e_2$ are generalized regular expressions, then so are the complement $\neg e$, the
union $e_1 + e_2$, the concatenation $e_1 e_2$ and the star $e^*$. -/
inductive GenRegExp (α : Type u) : Type u
  | ofReg : RegularExpression α → GenRegExp α
  | compl : GenRegExp α → GenRegExp α
  | plus : GenRegExp α → GenRegExp α → GenRegExp α
  | comp : GenRegExp α → GenRegExp α → GenRegExp α
  | star : GenRegExp α → GenRegExp α

namespace GenRegExp

/-- **Language of a generalized regular expression.** For an alphabet $\alpha$, the language over
$\alpha$ denoted by a generalized regular expression over $\alpha$ is defined recursively, for
generalized regular expressions $e$, $e_1$, $e_2$: an ordinary regular expression denotes the
language it matches; the complement $\neg e$ denotes the complement, in the set of all words over
$\alpha$, of the language of $e$; the union $e_1 + e_2$ denotes the union and the concatenation
$e_1 e_2$ the concatenation of the languages of $e_1$ and $e_2$; and the star $e^*$ denotes the
Kleene star of the language of $e$. -/
def denote : GenRegExp α → Language α
  | .ofReg e => e.matches'
  | .compl e => (denote e)ᶜ
  | .plus e₁ e₂ => denote e₁ + denote e₂
  | .comp e₁ e₂ => denote e₁ * denote e₂
  | .star e => (denote e)∗

/-- **Generalized star height.** The generalized star height of a generalized regular expression
is the nesting depth of the Kleene star in it, counting the stars inside its ordinary regular
subexpressions: for generalized regular expressions $e$, $e_1$, $e_2$, an ordinary regular
expression has its usual star height; the complement $\neg e$ has the star height of $e$; the
union $e_1 + e_2$ and the concatenation $e_1 e_2$ have the larger of the star heights of $e_1$
and $e_2$; and the star $e^*$ has star height one more than $e$. -/
def starHeight : GenRegExp α → ℕ
  | .ofReg e => regularStarHeight e
  | .compl e => starHeight e
  | .plus e₁ e₂ => max (starHeight e₁) (starHeight e₂)
  | .comp e₁ e₂ => max (starHeight e₁) (starHeight e₂)
  | .star e => starHeight e + 1

end GenRegExp

/-- **Bounded generalized star height.** A language $L$ over an alphabet $\alpha$ has generalized
star height at most $n$, for a natural number $n$, if some generalized regular expression over
$\alpha$ whose generalized star height is at most $n$ denotes $L$. -/
def HasGenHeightLe (L : Set (List α)) (n : ℕ) : Prop :=
  ∃ e : GenRegExp α, e.denote = L ∧ e.starHeight ≤ n

end Cslib.Language
