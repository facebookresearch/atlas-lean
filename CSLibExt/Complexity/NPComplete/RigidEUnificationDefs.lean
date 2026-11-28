/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RIGID E-UNIFICATION: definitions

Source:
J. H. Gallier, P. Narendran, D. Plaisted, and W. Snyder, "Rigid E-unification:
NP-completeness and applications to equational matings", Information and Computation 87
(1990), 129-195, doi:10.1016/0890-5401(90)90061-L;
B. Beckert, "A completion-based method for mixed universal and rigid E-unification",
Automated Deduction (CADE-12), LNAI 814 (1994), 678-692, doi:10.1007/3-540-58156-1_49,
Definitions 1 and 2 (the problem) and Section 3 ("Purely rigid E-unification is NP-complete").
-/
module

public import Mathlib.ModelTheory.Semantics
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UnificationForFinitelyPresentedAlgebrasDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RigidEUnification

open FirstOrder FirstOrder.Language
open MetaMathlibExt.Complexity.NPComplete.UnificationForFinitelyPresentedAlgebras (lang tokens)

/-- An instance: the arities `ar` of the function symbols, the number of variables `|V|`, the
equations of `E` as pairs of token lists, and the token lists of `s` and `t`. -/
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

end MetaMathlibExt.Complexity.NPComplete.RigidEUnification
