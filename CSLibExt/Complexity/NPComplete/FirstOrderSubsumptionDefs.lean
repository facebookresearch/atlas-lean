/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FIRST ORDER SUBSUMPTION: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [LO18] FIRST ORDER SUBSUMPTION (reference:
[Baxter, 1976], [Baxter, 1977]; transformation from 3SAT), p. 264;
L. D. Baxter, *The Complexity of Unification*, Doctoral Thesis, Department of Computer Science,
University of Waterloo (1976);
L. D. Baxter, "The NP-completeness of subsumption", unpublished manuscript (1977).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UnificationForFinitelyPresentedAlgebrasDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FirstOrderSubsumption

open FirstOrder FirstOrder.Language
open MetaMathlibExt.Complexity.NPComplete.UnificationForFinitelyPresentedAlgebras (lang tokens)

/-- An instance: the arities of the function symbols of `C`, the number `|U|` of variables, the
token lists of `E₁, ..., Eₘ` and the token lists of `F₁, ..., Fₙ`. -/
abbrev FirstOrderSubsumptionInstance :=
  List ℕ × ℕ × List (List (ℕ × ℕ)) × List (List (ℕ × ℕ))

/-- The expressions `E₁, ..., Eₘ` over `U ∪ C` whose token lists are those of the instance. -/
def Patterns (i : FirstOrderSubsumptionInstance) (es : List ((lang i.1).Term (Fin i.2.1))) :
    Prop :=
  es.map (tokens Fin.val) = i.2.2.1

/-- The expressions `F₁, ..., Fₙ` over `C` whose token lists are those of the instance. -/
def Targets (i : FirstOrderSubsumptionInstance) (fs : List ((lang i.1).Term Empty)) : Prop :=
  fs.map (tokens Empty.elim) = i.2.2.2

/-- Well-formedness of an instance: the token lists of `E` are those of expressions over `U ∪ C`
and the token lists of `F` are those of expressions over `C`. -/
def WellFormed (i : FirstOrderSubsumptionInstance) : Prop :=
  (∃ es, Patterns i es) ∧ ∃ fs, Targets i fs

/-- Some substitution `s` of expressions over `C` for the variables maps every `Eᵢ` to one of the
`Fⱼ`. -/
def FirstOrderSubsumptionFeasible (i : FirstOrderSubsumptionInstance) : Prop :=
  ∃ es, Patterns i es ∧ ∃ fs, Targets i fs ∧
    ∃ s : Fin i.2.1 → (lang i.1).Term Empty, ∀ e ∈ es, e.subst s ∈ fs

open Classical in
/-- FIRST ORDER SUBSUMPTION as a decision problem over bitstrings. -/
noncomputable def firstOrderSubsumptionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FirstOrderSubsumptionInstance) x with
  | some i => decide (WellFormed i ∧ FirstOrderSubsumptionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FirstOrderSubsumption
