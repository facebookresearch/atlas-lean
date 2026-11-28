/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# AC-UNIFICATION: definitions

Source:
D. Kapur and P. Narendran, "Complexity of unification problems with associative-commutative
operators", Journal of Automated Reasoning 9 (1992), 261-288, doi:10.1007/BF00245463
(membership in NP, hence NP-completeness); D. Benanav, D. Kapur and P. Narendran, "Complexity of
matching problems", Journal of Symbolic Computation 3 (1987), 203-216,
doi:10.1016/S0747-7171(87)80027-5 (NP-hardness). Both results, and the definition used here,
are recorded in D. Kapur and P. Narendran, "Double-exponential complexity of computing a
complete set of AC-unifiers", Proc. 7th IEEE Symposium on Logic in Computer Science (LICS 1992),
11-21, doi:10.1109/LICS.1992.185515, Section 1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ACMatchingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ACUnification

open FirstOrder FirstOrder.Language
open MetaMathlibExt.Complexity.NPComplete.UnificationForFinitelyPresentedAlgebras (lang tokens)
open MetaMathlibExt.Complexity.NPComplete.ACMatching (ACEquiv)

/-- An instance: the arities of the function symbols, the indices of the AC symbols, the number
of variables `|V|`, and the token lists of `s` and of `t`. -/
abbrev ACUnificationInstance := List ℕ × List ℕ × ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)

/-- Well-formedness of an instance: every AC symbol is a binary symbol, and `s` and `t` are
terms with variables `Fin |V|`. -/
def WellFormed (i : ACUnificationInstance) : Prop :=
  (∀ k ∈ i.2.1, i.1[k]? = some 2) ∧
    (∃ s : (lang i.1).Term (Fin i.2.2.1), tokens Fin.val s = i.2.2.2.1) ∧
      ∃ t : (lang i.1).Term (Fin i.2.2.1), tokens Fin.val t = i.2.2.2.2

/-- Some substitution `σ` makes `σ(s)` and `σ(t)` equal modulo associativity and commutativity
of the AC symbols. -/
def ACUnificationFeasible (i : ACUnificationInstance) : Prop :=
  ∃ s t : (lang i.1).Term (Fin i.2.2.1),
    tokens Fin.val s = i.2.2.2.1 ∧ tokens Fin.val t = i.2.2.2.2 ∧
      ∃ σ : Fin i.2.2.1 → (lang i.1).Term ℕ, ACEquiv i.2.1 (s.subst σ) (t.subst σ)

open Classical in
/-- AC-UNIFICATION as a decision problem over bitstrings. -/
noncomputable def acUnificationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ACUnificationInstance) x with
  | some i => decide (WellFormed i ∧ ACUnificationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ACUnification
