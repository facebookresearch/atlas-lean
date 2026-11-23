/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STRONG INEQUIVALENCE FOR MONADIC RECURSION SCHEMES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO17] STRONG INEQUIVALENCE FOR
MONADIC RECURSION SCHEMES, p. 277 (reference [Constable, Hunt, and Sahni, 1974];
transformation from STRONG INEQUIVALENCE OF IANOV SCHEMES);
R. L. Constable, H. B. Hunt III and S. Sahni, "On the computational complexity of program
scheme equivalence", SIAM Journal on Computing 9 (1980), 396-416, doi:10.1137/0209031
(journal version of the 1974 Cornell report GJ cites: strong equivalence of linear monadic
recursion schemes is NP-complete).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StrongInequivalenceForMonadicRecursionSchemes

/-!
# STRONG INEQUIVALENCE FOR MONADIC RECURSION SCHEMES is NP-complete

INSTANCE: finite sets `F` and `P` of function and predicate symbols, a set `G` of "defined"
function symbols disjoint from `F`, a specified symbol `f₀ ∈ G`, and two linear monadic
recursion schemes `S₁` and `S₂`, each consisting of a defining statement for each `f ∈ G` of
the form `fx = if px then αx else βx`, where `p ∈ P`, `α, β ∈ (F ∪ G)*`, and `α` and `β` each
contain at most one occurrence of a symbol from `G`.
QUESTION: is there a domain set `D`, an interpretation of each `f ∈ F` as a function
`f : D → D`, an interpretation of each `p ∈ P` as a function `p : D → {T, F}`, and an initial
value `x₀ ∈ D` such that, as defined by the recursion schemes `S₁` and `S₂`, either the two
values for `f₀(x₀)` differ or one is defined and the other isn't?

The symbols are `a₀, …, a_{|F|-1}` of `F`, written `(false, k)`, `g₀, …, g_{|G|-1}` of `G`,
written `(true, k)` (so `F` and `G` are disjoint), and `p₀, …, p_{|P|-1}` of `P`; `f₀` is
`g_{k₀}` for a given index `k₀`. Interpretations are families indexed by `ℕ`, of which only
the indices below `|F|` and `|P|` occur. A scheme is the list of its defining statements, the
`k`-th being `(j, α, β)` for `gₖ x = if pⱼ x then α x else β x`. A word `s₁ s₂ ⋯ sᵣ` applied to
`x` is `s₁(s₂(⋯ sᵣ(x)))`. `Computes S w x y` is the least relation closed under these
equations (the least fixed point semantics of the scheme): `f₀(x₀)` is defined with value `v`
iff `Computes S [g_{k₀}] x₀ v`. All functions are unary and the interpretations are total, so
this agrees with every standard evaluation order.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A recursion scheme: for each defined symbol `gₖ`, its defining statement `(j, α, β)`,
read `gₖ x = if pⱼ x then α x else β x`; a symbol of `F ∪ G` is `(false, k)` for `aₖ ∈ F` and
`(true, k)` for `gₖ ∈ G`. -/
abbrev RecursionScheme := List (ℕ × List (Bool × ℕ) × List (Bool × ℕ))

/-- An instance: `|F|`, `|P|`, `|G|`, the index `k₀` of `f₀ = g_{k₀}`, and the two schemes. -/
abbrev StrongInequivalenceForMonadicRecursionSchemesInstance :=
  ℕ × ℕ × ℕ × ℕ × RecursionScheme × RecursionScheme

/-- A word over `F ∪ G` (with `|F| = nF`, `|G| = nG`) containing at most one occurrence of a
symbol from `G`. -/
def IsLinearWord (nF nG : ℕ) (w : List (Bool × ℕ)) : Prop :=
  (∀ s ∈ w, (s.1 = false → s.2 < nF) ∧ (s.1 = true → s.2 < nG)) ∧
    w.countP (fun s => s.1) ≤ 1

/-- A linear monadic recursion scheme over `F`, `P` and `G`: one defining statement
`gₖ x = if pⱼ x then α x else β x` for each `gₖ ∈ G`, with `pⱼ ∈ P` and `α`, `β` linear
words. -/
def IsScheme (nF nP nG : ℕ) (S : RecursionScheme) : Prop :=
  S.length = nG ∧ ∀ d ∈ S, d.1 < nP ∧ IsLinearWord nF nG d.2.1 ∧ IsLinearWord nF nG d.2.2

/-- Well-formedness of an instance: `f₀ ∈ G` (`k₀ < |G|`), and both schemes are linear
monadic recursion schemes over `F`, `P` and `G`. -/
def WellFormed (i : StrongInequivalenceForMonadicRecursionSchemesInstance) : Prop :=
  i.2.2.2.1 < i.2.2.1 ∧ IsScheme i.1 i.2.1 i.2.2.1 i.2.2.2.2.1 ∧
    IsScheme i.1 i.2.1 i.2.2.1 i.2.2.2.2.2

/-- `Computes S F P w x y`: under the interpretation `F` of the symbols of `F` and `P` of the
predicates, the word `w` applied to `x` is defined by the scheme `S` with value `y`. The
empty word is the identity; `aₖ w` applies `F k` to the value of `w`; `gₖ w` applies the
defining statement `gₖ x = if pⱼ x then α x else β x` of `S` to the value of `w`. -/
inductive Computes {D : Type} (S : RecursionScheme) (F : ℕ → D → D) (P : ℕ → D → Bool) :
    List (Bool × ℕ) → D → D → Prop where
  /-- The empty word is the identity. -/
  | nil (x : D) : Computes S F P [] x x
  /-- A symbol `aₖ` of `F` is applied after the rest of the word. -/
  | base (k : ℕ) (w : List (Bool × ℕ)) (x y : D) :
      Computes S F P w x y → Computes S F P ((false, k) :: w) x (F k y)
  /-- A defined symbol `gₖ` is applied after the rest of the word, by its defining
  statement in `S`. -/
  | defined (k j : ℕ) (α β w : List (Bool × ℕ)) (x y z : D) :
      S[k]? = some (j, α, β) → Computes S F P w x y →
        Computes S F P (if P j y then α else β) y z → Computes S F P ((true, k) :: w) x z

/-- The value `f₀(x₀) = g_{k₀}(x₀)` defined by the scheme `S` is `v`. -/
def DefinesValue {D : Type} (S : RecursionScheme) (F : ℕ → D → D) (P : ℕ → D → Bool)
    (k₀ : ℕ) (x₀ v : D) : Prop :=
  Computes S F P [(true, k₀)] x₀ v

/-- Under some domain, interpretation and initial value, the values of `f₀(x₀)` defined by
`S₁` and `S₂` differ, or exactly one of them is defined. -/
def StrongInequivalenceForMonadicRecursionSchemesFeasible
    (i : StrongInequivalenceForMonadicRecursionSchemesInstance) : Prop :=
  ∃ (D : Type) (F : ℕ → D → D) (P : ℕ → D → Bool) (x₀ : D),
    (∃ v w, DefinesValue i.2.2.2.2.1 F P i.2.2.2.1 x₀ v ∧
        DefinesValue i.2.2.2.2.2 F P i.2.2.2.1 x₀ w ∧ v ≠ w) ∨
      ((∃ v, DefinesValue i.2.2.2.2.1 F P i.2.2.2.1 x₀ v) ∧
        ¬ ∃ w, DefinesValue i.2.2.2.2.2 F P i.2.2.2.1 x₀ w) ∨
      ((¬ ∃ v, DefinesValue i.2.2.2.2.1 F P i.2.2.2.1 x₀ v) ∧
        ∃ w, DefinesValue i.2.2.2.2.2 F P i.2.2.2.1 x₀ w)

open Classical in
/-- STRONG INEQUIVALENCE FOR MONADIC RECURSION SCHEMES as a decision problem over
bitstrings. -/
noncomputable def strongInequivalenceForMonadicRecursionSchemesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := StrongInequivalenceForMonadicRecursionSchemesInstance) x with
  | some i => decide (WellFormed i ∧ StrongInequivalenceForMonadicRecursionSchemesFeasible i)
  | none => false

/-- **STRONG INEQUIVALENCE FOR MONADIC RECURSION SCHEMES is NP-complete.** Source: Garey and
Johnson (1979), [PO17]; Constable, Hunt and Sahni (1980). -/
public theorem_wanted strongInequivalenceForMonadicRecursionSchemes_npComplete :
    strongInequivalenceForMonadicRecursionSchemesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L strongInequivalenceForMonadicRecursionSchemesDec

end MetaMathlibExt.Complexity.NPComplete.StrongInequivalenceForMonadicRecursionSchemes
