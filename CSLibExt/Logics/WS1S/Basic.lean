/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WS1S: syntax, semantics and Gödel numbering
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Nat.Pairing

/-!
# WS1S: syntax, semantics and Gödel numbering

Weak monadic second-order logic of one successor (WS1S): first-order variables range over the
naturals and set variables over finite sets of naturals.

* `WS1STerm`, `WS1SFormula`: terms (`var`, `zero`, `succ`) and formulas (`eq`, `lt`, `mem`,
  `falsum`, `imp`, `all`, `allSet`), with the derived `WS1SFormula.neg`, `ex` and `exSet`.
* `WS1STerm.eval`, `WS1SFormula.Holds`: semantics under a first-order assignment `Nat → Nat` and a
  set assignment `Nat → Finset Nat`; a quantifier binds variable `0` and shifts the others.
* `codeWS1STerm`, `codeWS1S`: Gödel numberings by Cantor pairing with one tag per constructor,
  injective (`codeWS1STerm_injective`, `codeWS1S_injective`).

Decidability of WS1S over these codes is deferred: `Cslib.Logic.WS1SWanted.ws1s_decidable` in
`WantedExt.TheoryOfComputation.WS1SDecidabilityWanted`.
-/

@[expose] public section

namespace Cslib.Logic.WS1S

/-- Terms of WS1S: first-order variables, `0`, and successor. -/
inductive WS1STerm where
  /-- First-order variable `i`. -/
  | var : Nat → WS1STerm
  /-- The constant `0`. -/
  | zero : WS1STerm
  /-- Successor. -/
  | succ : WS1STerm → WS1STerm
  deriving DecidableEq

/-- Formulas of WS1S: equality and order of first-order terms, membership of a term
in a set variable, Boolean connectives, and first- and second-order quantification.
Set variables are indexed by `Nat` and range over finite sets of naturals (weakness). -/
inductive WS1SFormula where
  /-- `t₁ = t₂`. -/
  | eq : WS1STerm → WS1STerm → WS1SFormula
  /-- `t₁ < t₂`. -/
  | lt : WS1STerm → WS1STerm → WS1SFormula
  /-- `t ∈ X`. -/
  | mem : WS1STerm → Nat → WS1SFormula
  /-- Falsity. -/
  | falsum : WS1SFormula
  /-- Implication. -/
  | imp : WS1SFormula → WS1SFormula → WS1SFormula
  /-- `∀x. φ`, with `x` the variable `0` after shifting. -/
  | all : WS1SFormula → WS1SFormula
  /-- `∀X. φ`, with `X` the set variable `0` after shifting. -/
  | allSet : WS1SFormula → WS1SFormula
  deriving DecidableEq

namespace WS1SFormula

/-- Negation. -/
def neg (φ : WS1SFormula) : WS1SFormula := .imp φ .falsum

/-- Existential first-order quantification. -/
def ex (φ : WS1SFormula) : WS1SFormula := φ.neg.all.neg

/-- Existential second-order quantification. -/
def exSet (φ : WS1SFormula) : WS1SFormula := φ.neg.allSet.neg

end WS1SFormula

/-- Evaluation of a WS1S term under a first-order assignment `v : Nat → Nat`. -/
def WS1STerm.eval (v : Nat → Nat) : WS1STerm → Nat
  | .var i => v i
  | .zero => 0
  | .succ t => t.eval v + 1

/-- Satisfaction of a WS1S formula under a first-order assignment `v : Nat → Nat` and a
set assignment `V : Nat → Finset Nat`. First-order quantification shifts `v` (the bound
variable is `0`); second-order quantification shifts `V`. -/
def WS1SFormula.Holds (v : Nat → Nat) (V : Nat → Finset Nat) : WS1SFormula → Prop
  | .eq t₁ t₂ => t₁.eval v = t₂.eval v
  | .lt t₁ t₂ => t₁.eval v < t₂.eval v
  | .mem t i => t.eval v ∈ V i
  | .falsum => False
  | .imp φ ψ => φ.Holds v V → ψ.Holds v V
  | .all φ => ∀ x : Nat, φ.Holds (fun i => match i with | 0 => x | j + 1 => v j) V
  | .allSet φ => ∀ X : Finset Nat,
      φ.Holds v (fun i => match i with | 0 => X | j + 1 => V j)

/-- Gödel numbering of WS1S terms, via Cantor pairing with a disjoint tag per
constructor: every code is `Nat.pair tag payload` with tag `0` for variables, `1`
for `0`, `2` for successor. Bare constants are never used as codes, since e.g. the
old `.zero ↦ 1` collided with `.var 1 ↦ Nat.pair 0 1 = 1` (see the regression
examples in `CSLibExtTest.Logics.WS1S.BasicTests`). -/
def codeWS1STerm : WS1STerm → Nat
  | .var i => Nat.pair 0 i
  | .zero => Nat.pair 1 0
  | .succ t => Nat.pair 2 (codeWS1STerm t)

/-- The term numbering is injective: distinct tags plus injectivity of `Nat.pair`
and recursion. Injectivity is what makes the numbering decodable: a code
determines its term (by unpairing the tag, then recursing), so the
`ComputablePred` statement `Cslib.Logic.WS1SWanted.ws1s_decidable` picks out validity of the
supplied formula rather than of some other formula sharing its code. -/
theorem codeWS1STerm_injective : Function.Injective codeWS1STerm := by
  intro a b h
  induction a generalizing b with
  | var i =>
    cases b with
    | var j => simp only [codeWS1STerm, Nat.pair_eq_pair] at h; rw [h.2]
    | zero => simp only [codeWS1STerm, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
    | succ _ => simp only [codeWS1STerm, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
  | zero =>
    cases b with
    | var _ => simp only [codeWS1STerm, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
    | zero => rfl
    | succ _ => simp only [codeWS1STerm, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
  | succ t ih =>
    cases b with
    | var _ => simp only [codeWS1STerm, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
    | zero => simp only [codeWS1STerm, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
    | succ t' => simp only [codeWS1STerm, Nat.pair_eq_pair] at h; rw [ih h.2]

/-- Gödel numbering of WS1S formulas, via Cantor pairing with a disjoint tag per
constructor: every code is `Nat.pair tag payload` with tags `0` (`eq`), `1` (`lt`),
`2` (`mem`), `3` (`falsum`), `4` (`imp`), `5` (`all`), `6` (`allSet`). In
particular `falsum` is `Nat.pair 3 0`, not the bare constant `3`: the old bare `3`
collided with e.g. `.lt` codes, since `Nat.pair 1 1 = 3`. -/
def codeWS1S : WS1SFormula → Nat
  | .eq t₁ t₂ => Nat.pair 0 (Nat.pair (codeWS1STerm t₁) (codeWS1STerm t₂))
  | .lt t₁ t₂ => Nat.pair 1 (Nat.pair (codeWS1STerm t₁) (codeWS1STerm t₂))
  | .mem t i => Nat.pair 2 (Nat.pair (codeWS1STerm t) i)
  | .falsum => Nat.pair 3 0
  | .imp φ ψ => Nat.pair 4 (Nat.pair (codeWS1S φ) (codeWS1S ψ))
  | .all φ => Nat.pair 5 (codeWS1S φ)
  | .allSet φ => Nat.pair 6 (codeWS1S φ)

/-- The formula numbering is injective: distinct tags plus injectivity of `Nat.pair`,
of `codeWS1STerm`, and recursion. -/
theorem codeWS1S_injective : Function.Injective codeWS1S := by
  intro a b h
  induction a generalizing b with
  | eq t₁ t₂ =>
    cases b with
    | eq s₁ s₂ =>
      simp only [codeWS1S, Nat.pair_eq_pair] at h
      rw [codeWS1STerm_injective h.2.1, codeWS1STerm_injective h.2.2]
    | lt _ _ | mem _ _ | falsum | imp _ _ | all _ | allSet _ =>
      simp only [codeWS1S, Nat.pair_eq_pair] at h
      exact absurd h.1 (by decide)
  | lt t₁ t₂ =>
    cases b with
    | lt s₁ s₂ =>
      simp only [codeWS1S, Nat.pair_eq_pair] at h
      rw [codeWS1STerm_injective h.2.1, codeWS1STerm_injective h.2.2]
    | eq _ _ | mem _ _ | falsum | imp _ _ | all _ | allSet _ =>
      simp only [codeWS1S, Nat.pair_eq_pair] at h
      exact absurd h.1 (by decide)
  | mem t i =>
    cases b with
    | mem s j =>
      simp only [codeWS1S, Nat.pair_eq_pair] at h
      rw [codeWS1STerm_injective h.2.1, h.2.2]
    | eq _ _ | lt _ _ | falsum | imp _ _ | all _ | allSet _ =>
      simp only [codeWS1S, Nat.pair_eq_pair] at h
      exact absurd h.1 (by decide)
  | falsum =>
    cases b with
    | falsum => rfl
    | eq _ _ | lt _ _ | mem _ _ | imp _ _ | all _ | allSet _ =>
      simp only [codeWS1S, Nat.pair_eq_pair] at h
      exact absurd h.1 (by decide)
  | imp φ ψ ihφ ihψ =>
    cases b with
    | imp φ' ψ' =>
      simp only [codeWS1S, Nat.pair_eq_pair] at h
      rw [ihφ h.2.1, ihψ h.2.2]
    | eq _ _ | lt _ _ | mem _ _ | falsum | all _ | allSet _ =>
      simp only [codeWS1S, Nat.pair_eq_pair] at h
      exact absurd h.1 (by decide)
  | all φ ih =>
    cases b with
    | all ψ =>
      simp only [codeWS1S, Nat.pair_eq_pair] at h
      rw [ih h.2]
    | eq _ _ | lt _ _ | mem _ _ | falsum | imp _ _ | allSet _ =>
      simp only [codeWS1S, Nat.pair_eq_pair] at h
      exact absurd h.1 (by decide)
  | allSet φ ih =>
    cases b with
    | allSet ψ =>
      simp only [codeWS1S, Nat.pair_eq_pair] at h
      rw [ih h.2]
    | eq _ _ | lt _ _ | mem _ _ | falsum | imp _ _ | all _ =>
      simp only [codeWS1S, Nat.pair_eq_pair] at h
      exact absurd h.1 (by decide)

end Cslib.Logic.WS1S
