/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RIGID E-UNIFICATION is NP-complete

Source:
J. H. Gallier, P. Narendran, D. Plaisted, and W. Snyder, "Rigid E-unification:
NP-completeness and applications to equational matings", Information and Computation 87
(1990), 129-195, doi:10.1016/0890-5401(90)90061-L;
B. Beckert, "A completion-based method for mixed universal and rigid E-unification",
Automated Deduction (CADE-12), LNAI 814 (1994), 678-692, doi:10.1007/3-540-58156-1_49,
Definitions 1 and 2 (the problem) and Section 3 ("Purely rigid E-unification is NP-complete").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.ModelTheory.Semantics
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.UnificationForFinitelyPresentedAlgebrasWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RigidEUnification

open FirstOrder FirstOrder.Language
open MetaMathlibExt.Complexity.NPComplete.UnificationForFinitelyPresentedAlgebras (lang tokens)

/-!
# RIGID E-UNIFICATION is NP-complete

INSTANCE: a finite set `E` of equations `l ≈ r` between first-order terms over a finite
signature and a finite set `V` of variables, and two terms `s` and `t`.
QUESTION: is there a substitution `σ` such that `Eσ ⊨ sσ ≈ tσ`, where the variables in `Eσ` are
held rigid, i.e. treated as constants?

Beckert (Definition 1): "A substitution σ is a solution to the problem, iff Eσ |= (sσ ≈ tσ),
where the free variables in Eσ are “held rigid”, i.e. treated as constants"; the problem is
purely rigid when `E` has no universally quantified variables (Definition 2), and "Purely rigid
E-unification is NP-complete" (Section 3, citing Gallier, Narendran, Plaisted, and Snyder, whose
abstract states "it is shown that rigid E-unification is NP-complete"). Unlike ordinary
E-unification, the substitution is applied to `E` as well as to `s` and `t`, and each variable
of `E` stands for the single term `σ(x)`. When `E` is ground and the signature has a constant
(so that a unifier can be made ground by replacing its remaining variables with that constant),
this is UNIFICATION FOR FINITELY PRESENTED ALGEBRAS
(`WantedExt.Complexity.NPComplete.UnificationForFinitelyPresentedAlgebrasWanted`, Kozen's
problem), whose language `lang` and prefix token encoding `tokens` are reused.

Terms are Mathlib's `(lang ar).Term (Fin |V|)`, over the function symbols `0, …, |ar| - 1` with
arities `ar` (constants have arity `0`), and `σ` is `Term.subst` with a map `Fin |V| → Term`.
Holding the variables of `Eσ` rigid means that they denote fixed but arbitrary elements:
`Eσ ⊨ sσ ≈ tσ` holds when, in every structure for the signature and for every assignment `v`
of elements to the variables, `v` satisfying every equation of `Eσ` implies that it satisfies
`sσ ≈ tσ` (Mathlib's `Term.realize`). For ground equations this semantic consequence coincides
with derivability in ground equational logic (congruence closure).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: a list `ar` of natural arities, a number `|V|`, a list of pairs of raw token
lists (read as the equations of `E`; a list of pairs, not a set) and two raw token lists, read
as the terms `s` and `t`. A token list may be empty or fail to parse; which term or equation
it represents is defined only when parsing succeeds. Successful parsing and the symbol and
variable bounds belong to `WellFormed`. -/
abbrev RigidEUnificationInstance :=
  List ℕ × ℕ × List (List (ℕ × ℕ) × List (ℕ × ℕ)) × List (ℕ × ℕ) × List (ℕ × ℕ)

/-- The equations of `E` whose token lists are those of the instance. -/
def Equations (i : RigidEUnificationInstance)
    (E : List ((lang i.1).Term (Fin i.2.1) × (lang i.1).Term (Fin i.2.1))) : Prop :=
  E.map (fun p => (tokens Fin.val p.1, tokens Fin.val p.2)) = i.2.2.1

/-- Well-formedness of an instance: the token lists are those of an equation set `E` and of
terms `s` and `t`, all over the symbols of `ar` and the variables `Fin |V|`. -/
def WellFormed (i : RigidEUnificationInstance) : Prop :=
  (∃ E, Equations i E) ∧
    (∃ s : (lang i.1).Term (Fin i.2.1), tokens Fin.val s = i.2.2.2.1) ∧
    ∃ t : (lang i.1).Term (Fin i.2.1), tokens Fin.val t = i.2.2.2.2

/-- `Eσ ⊨ sσ ≈ tσ` with the variables held rigid: in every structure, every assignment of the
variables that satisfies all equations of `Eσ` satisfies `sσ ≈ tσ`. -/
def RigidlyEntails {ar : List ℕ} {n : ℕ}
    (E : List ((lang ar).Term (Fin n) × (lang ar).Term (Fin n)))
    (s t : (lang ar).Term (Fin n)) : Prop :=
  ∀ (M : Type) [(lang ar).Structure M] (v : Fin n → M),
    (∀ p ∈ E, p.1.realize v = p.2.realize v) → s.realize v = t.realize v

/-- Some substitution `σ` is a rigid `E`-unifier of `s` and `t`: `Eσ ⊨ sσ ≈ tσ` with the
variables of `Eσ` held rigid. -/
def RigidEUnificationFeasible (i : RigidEUnificationInstance) : Prop :=
  ∃ E, Equations i E ∧
    ∃ s t : (lang i.1).Term (Fin i.2.1),
      tokens Fin.val s = i.2.2.2.1 ∧ tokens Fin.val t = i.2.2.2.2 ∧
        ∃ σ : Fin i.2.1 → (lang i.1).Term (Fin i.2.1),
          RigidlyEntails (E.map fun p => (p.1.subst σ, p.2.subst σ)) (s.subst σ) (t.subst σ)

open Classical in
/-- RIGID E-UNIFICATION as a decision problem over bitstrings. -/
noncomputable def rigidEUnificationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := RigidEUnificationInstance) x with
  | some i => decide (WellFormed i ∧ RigidEUnificationFeasible i)
  | none => false

/-- **RIGID E-UNIFICATION is NP-complete.** Source: Gallier, Narendran, Plaisted, and Snyder
(1990); Beckert (1994), Section 3. -/
public theorem_wanted rigidEUnification_npComplete :
    rigidEUnificationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rigidEUnificationDec

end MetaMathlibExt.Complexity.NPComplete.RigidEUnification
