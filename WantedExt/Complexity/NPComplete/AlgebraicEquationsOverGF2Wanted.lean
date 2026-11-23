/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ALGEBRAIC EQUATIONS OVER GF[2] is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN9] ALGEBRAIC EQUATIONS OVER GF[2];
A. S. Fraenkel and Y. Yesha, "Complexity of problems in games, graphs and algebraic equations",
Discrete Applied Mathematics 1 (1979), 15-30, doi:10.1016/0166-218X(79)90012-X.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.ZMod.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AlgebraicEquationsOverGF2

/-!
# ALGEBRAIC EQUATIONS OVER GF[2] is NP-complete

Given polynomials `P₁, …, Pₘ` over `GF[2]` in the variables `x₁, …, xₙ`, each a sum of terms
and each term either `1` or a product of distinct variables, is there
`(u₁, …, uₙ) ∈ {0, 1}ⁿ` with `Pᵢ(u₁, …, uₙ) = 0` for `1 ≤ i ≤ m`?

The variables are `x₀, …, x_{n-1}` (indices `Fin n`), `GF[2]` is `ZMod 2`, and each `Pᵢ` is
read as an element of `MvPolynomial (Fin n) (ZMod 2)` and evaluated with `MvPolynomial.eval`.
A term is the list of indices of its variables: `[]` is the term `1`, and `[j₁, …, jᵣ]` with
distinct `jₖ < n` is `x_{j₁} ⋯ x_{jᵣ}`. A polynomial is the list of its terms; a repeated term
is allowed and contributes `t + t = 0`, as in `GF[2]`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of variables and the polynomials `P₁, …, Pₘ`, each a list of
terms, each term a list of variable indices. -/
abbrev AlgebraicEquationsOverGF2Instance := ℕ × List (List (List ℕ))

/-- The variable `x_j` in `MvPolynomial (Fin n) (ZMod 2)`. An index `j ≥ n`, which
`WellFormed` excludes, gives `0`. -/
noncomputable def var (n j : ℕ) : MvPolynomial (Fin n) (ZMod 2) :=
  if h : j < n then MvPolynomial.X ⟨j, h⟩ else 0

/-- The term `x_{j₁} ⋯ x_{jᵣ}` of the index list `[j₁, …, jᵣ]`; the empty list gives `1`. -/
noncomputable def term (n : ℕ) (t : List ℕ) : MvPolynomial (Fin n) (ZMod 2) :=
  (t.map (var n)).prod

/-- The polynomial that is the sum of the given terms. -/
noncomputable def poly (n : ℕ) (P : List (List ℕ)) : MvPolynomial (Fin n) (ZMod 2) :=
  (P.map (term n)).sum

/-- Well-formedness of an instance: in every term the variable indices are distinct and
less than `n`. -/
def WellFormed (i : AlgebraicEquationsOverGF2Instance) : Prop :=
  ∀ P ∈ i.2, ∀ t ∈ P, t.Nodup ∧ ∀ j ∈ t, j < i.1

/-- Some `u ∈ GF[2]ⁿ` is a common zero of all the polynomials. -/
def AlgebraicEquationsOverGF2Feasible (i : AlgebraicEquationsOverGF2Instance) : Prop :=
  ∃ u : Fin i.1 → ZMod 2, ∀ P ∈ i.2, MvPolynomial.eval u (poly i.1 P) = 0

open Classical in
/-- ALGEBRAIC EQUATIONS OVER GF[2] as a decision problem over bitstrings. -/
noncomputable def algebraicEquationsOverGF2Dec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := AlgebraicEquationsOverGF2Instance) x with
  | some i => decide (WellFormed i ∧ AlgebraicEquationsOverGF2Feasible i)
  | none => false

/-- **ALGEBRAIC EQUATIONS OVER GF[2] is NP-complete.** Source: Garey and Johnson (1979), [AN9];
Fraenkel and Yesha (1979). -/
public theorem_wanted algebraicEquationsOverGF2_npComplete :
    algebraicEquationsOverGF2Dec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L algebraicEquationsOverGF2Dec

end MetaMathlibExt.Complexity.NPComplete.AlgebraicEquationsOverGF2
