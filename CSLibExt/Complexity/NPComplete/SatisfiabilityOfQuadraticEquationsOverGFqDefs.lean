/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SATISFIABILITY OF QUADRATIC EQUATIONS OVER GF[q]: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MAXIMUM SATISFIABILITY OF QUADRATIC EQUATIONS OVER GF[Q] (decision version);
J. Håstad, S. Phillips and S. Safra, "A well-characterized approximation problem",
Information Processing Letters 47 (1993), 301-305, doi:10.1016/0020-0190(93)90076-L,
Theorem 4.2 (for every fixed prime `p`, deciding whether all equations of an instance can be
satisfied simultaneously is NP-complete).
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SatisfiabilityOfQuadraticEquationsOverGFq

/-- An instance: the prime `q`, the number `n` of variables, the polynomials of `P` (each a list
of terms `(a, t)`, with coefficient `a` and variable-index list `t`), and the bound `K`. -/
abbrev QuadraticEquationsInstance := ℕ × ℕ × List (List (ℕ × List ℕ)) × ℕ

/-- The variable `x_j` in `MvPolynomial (Fin n) (ZMod q)`. An index `j ≥ n`, which `WellFormed`
excludes, gives `0`. -/
noncomputable def var (q n j : ℕ) : MvPolynomial (Fin n) (ZMod q) :=
  if h : j < n then MvPolynomial.X ⟨j, h⟩ else 0

/-- The term `a · x_{j₁} ⋯ x_{jᵣ}` of a coefficient `a` and an index list `[j₁, …, jᵣ]`. -/
noncomputable def term (q n : ℕ) (t : ℕ × List ℕ) : MvPolynomial (Fin n) (ZMod q) :=
  MvPolynomial.C (t.1 : ZMod q) * (t.2.map (var q n)).prod

/-- The polynomial that is the sum of the given terms. -/
noncomputable def poly (q n : ℕ) (p : List (ℕ × List ℕ)) : MvPolynomial (Fin n) (ZMod q) :=
  (p.map (term q n)).sum

/-- Well-formedness of an instance: `q` is prime; in every term the coefficient is less than
`q` and the variable indices are at most two, distinct, and less than `n`; the polynomials are
pairwise distinct; and `K` is positive. -/
def WellFormed (i : QuadraticEquationsInstance) : Prop :=
  i.1.Prime ∧
    (∀ p ∈ i.2.2.1, ∀ t ∈ p, t.1 < i.1 ∧ t.2.Nodup ∧ t.2.length ≤ 2 ∧ ∀ j ∈ t.2, j < i.2.1) ∧
    (i.2.2.1.map (poly i.1 i.2.1)).Nodup ∧ 0 < i.2.2.2

/-- Some set `P'` of at least `K` of the polynomials has a common root in `GF[q]ⁿ`. -/
def QuadraticEquationsFeasible (i : QuadraticEquationsInstance) : Prop :=
  ∃ P' : Finset (Fin i.2.2.1.length), i.2.2.2 ≤ P'.card ∧
    ∃ x : Fin i.2.1 → ZMod i.1,
      ∀ k ∈ P', MvPolynomial.eval x (poly i.1 i.2.1 (i.2.2.1.get k)) = 0

open Classical in
/-- SATISFIABILITY OF QUADRATIC EQUATIONS OVER GF[q] as a decision problem over bitstrings. -/
noncomputable def quadraticEquationsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := QuadraticEquationsInstance) x with
  | some i => decide (WellFormed i ∧ QuadraticEquationsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SatisfiabilityOfQuadraticEquationsOverGFq
