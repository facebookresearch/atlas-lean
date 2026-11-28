/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM DISJUNCTIVE NORMAL FORM: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO9] MINIMUM
DISJUNCTIVE NORMAL FORM;
J. F. Gimpel, "A method of producing a Boolean function having an arbitrarily
prescribed prime implicant table", IEEE Transactions on Electronic Computers
EC-14 (1965), 485-488, doi:10.1109/PGEC.1965.264175;
E. Allender, L. Hellerstein, P. McCabe, T. Pitassi, and M. Saks, "Minimizing
disjunctive normal form formulas and AC⁰ circuits given a truth table", SIAM
Journal on Computing 38 (2008), 63-84, doi:10.1137/060664537.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.KeyTheorems.KarpLubyDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumDisjunctiveNormalForm

/-- An instance: the number `n` of variables, the list of truth assignments `A`, and the bound
`K`. -/
abbrev MinimumDisjunctiveNormalFormInstance := ℕ × List (List Bool) × ℕ

/-- Well-formedness of an instance: every listed truth assignment has length `n`, and `K` is
positive. -/
def WellFormed (i : MinimumDisjunctiveNormalFormInstance) : Prop :=
  (∀ a ∈ i.2.1, a.length = i.1) ∧ 0 < i.2.2

/-- Some DNF expression over `u₀, …, u_{n-1}` with at most `K` disjuncts is true on exactly the
assignments in `A`. -/
def MinimumDisjunctiveNormalFormFeasible (i : MinimumDisjunctiveNormalFormInstance) : Prop :=
  ∃ E : List (List (ℕ × Bool)), E.length ≤ i.2.2 ∧ (∀ t ∈ E, ∀ l ∈ t, l.1 < i.1) ∧
    ∀ a : List Bool, a.length = i.1 →
      (MetaMathlibExt.Complexity.KeyTheorems.KarpLuby.dnfSat (fun x => a.getD x false) E ↔
        a ∈ i.2.1)

open Classical in
/-- MINIMUM DISJUNCTIVE NORMAL FORM as a decision problem over bitstrings. -/
noncomputable def minimumDisjunctiveNormalFormDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumDisjunctiveNormalFormInstance) x with
  | some i => decide (WellFormed i ∧ MinimumDisjunctiveNormalFormFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumDisjunctiveNormalForm
