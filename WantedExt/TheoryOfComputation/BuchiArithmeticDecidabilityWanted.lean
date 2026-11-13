/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Decidability of Büchi arithmetic
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Computability.RE
public import Mathlib.ModelTheory.Semantics

@[expose] public section

namespace Cslib.Logic.BuchiArithmeticWanted

open FirstOrder FirstOrder.Language

/-- Function symbols of Büchi arithmetic: `0`, `S`, `+`. -/
inductive BuchiFunctions : ℕ → Type
  /-- The constant `0`. -/
  | zero : BuchiFunctions 0
  /-- The successor function `S`. -/
  | succ : BuchiFunctions 1
  /-- Addition. -/
  | add : BuchiFunctions 2

/-- Relation symbols of Büchi arithmetic: `V₂`, the 2-adic valuation relation. -/
inductive BuchiRelations : ℕ → Type
  /-- `V₂(x, y)`: `y` is the largest power of `2` dividing `x`. -/
  | v2 : BuchiRelations 2

/-- The first-order language of Büchi arithmetic: function symbols `0`, `S`, `+` and the
binary relation `V₂`. -/
def BuchiLanguage : FirstOrder.Language where
  Functions := BuchiFunctions
  Relations := BuchiRelations

/-- The standard structure on `ℕ`: `0`, `S`, `+` with their usual meanings, and
`V₂(x, y)` iff `y` is a power of two, `y ∣ x`, and no larger power of two divides `x`
(with `V₂(0, y)` false for all `y`). -/
instance instNat : BuchiLanguage.Structure ℕ where
  funMap f ts := match f with
    | .zero => 0
    | .succ => ts 0 + 1
    | .add => ts 0 + ts 1
  RelMap R ts := match R with
    | .v2 => ∃ k : ℕ, ts 1 = 2 ^ k ∧ ts 1 ∣ ts 0 ∧ ∀ k' : ℕ, ts 0 % 2 ^ (k' + 1) = 0 →
        k' < k

/-- Gödel numbering of Büchi function symbols, via constructor tags. -/
def codeFun {l : ℕ} : BuchiFunctions l → ℕ
  | .zero => 0
  | .succ => 1
  | .add => 2

/-- Gödel numbering of a tuple of codes, via Cantor pairing. -/
def codeTuple : ∀ {l : ℕ}, (Fin l → ℕ) → ℕ
  | 0, _ => 0
  | l + 1, xs => Nat.pair (codeTuple (Fin.init xs)) (xs (Fin.last l))

/-- Gödel numbering of Büchi terms with `n` bound variables in scope, via Cantor pairing. -/
def codeTerm {n : ℕ} : BuchiLanguage.Term (Empty ⊕ Fin n) → ℕ
  | .var (Sum.inl e) => e.elim
  | .var (Sum.inr i) => Nat.pair 1 i.val
  | .func f ts => Nat.pair 2 (Nat.pair (codeFun f) (codeTuple fun i => codeTerm (ts i)))

/-- Gödel numbering of Büchi relation symbols. -/
def codeRel {l : ℕ} : BuchiRelations l → ℕ
  | .v2 => 0

/-- Gödel numbering of Büchi formulas with `n` bound variables in scope, via Cantor
pairing with distinct tags per constructor. The tags make the numbering injective, and
it is primitive-recursive (built from pairing and structural recursion) and computably
decodable by unpairing. -/
def codeFormula {n : ℕ} : BuchiLanguage.BoundedFormula Empty n → ℕ
  | .falsum => 0
  | .equal t₁ t₂ => Nat.pair 1 (Nat.pair (codeTerm t₁) (codeTerm t₂))
  | .rel R ts => Nat.pair 2 (Nat.pair (codeRel R) (codeTuple fun i => codeTerm (ts i)))
  | .imp φ ψ => Nat.pair 3 (Nat.pair (codeFormula φ) (codeFormula ψ))
  | .all φ => Nat.pair 4 (codeFormula φ)

/-- Gödel numbering of Büchi sentences. -/
def codeSentence : BuchiLanguage.Sentence → ℕ := codeFormula

/-- Decidability of Büchi arithmetic: the set of Gödel codes of sentences true in the
standard model `ℕ` is computable. The statement is a `ComputablePred` over `ℕ` via the
explicit Gödel numbering `codeSentence`: a bare `∃ dec : Sentence → Bool` would not
express algorithmic decidability, since classical choice supplies a characteristic
function for every predicate. Büchi arithmetic is equivalent in expressive power to
WS1S (see `WS1SDecidabilityWanted.lean`): both decide the same sets of naturals, and
decidability follows from Büchi's automata construction.
Source: J. R. Büchi, "Weak second-order arithmetic and finite automata", Zeitschrift für
mathematische Logik und Grundlagen der Mathematik 6 (1960), 66-92; see also
J. R. Büchi, "On a decision method in restricted second order arithmetic", Proceedings
of the 1960 International Congress on Logic, Methodology and Philosophy of Science,
Stanford University Press, 1962, 1-11. -/
public theorem_wanted buchi_arithmetic_decidable :
    ComputablePred (fun n : ℕ => ∃ φ : BuchiLanguage.Sentence,
      codeSentence φ = n ∧ (ℕ ⊨ φ))

end Cslib.Logic.BuchiArithmeticWanted
