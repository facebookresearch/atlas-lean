/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Relation
public import Mathlib.Data.Set.Insert

/-!
# SAFETY OF MONO-OPERATIONAL FILE PROTECTION SYSTEMS: definitions

INSTANCE: a set `R` of generic rights, a set `O` of objects, a set `S ⊆ O` of subjects, sets
`P(s, o) ⊆ R` of rights for each subject `s ∈ S` and object `o ∈ O` (the access matrix), a
finite set `C` of commands, each of the form "if `r₁ ∈ P(X₁, Y₁)` and ... and `rₘ ∈ P(Xₘ, Yₘ)`
then `θ`" (`m ≥ 0`) with a single operation `θ` of the form "enter `r` into `P(X, Y)`" or
"delete `r` from `P(X, Y)`", and a specified right `r' ∈ R`.
QUESTION: is there a sequence of commands from `C`, with actual parameters, such that at some
point in its execution the right `r'` is entered into a set `P(s, o)` that previously did not
contain `r'`?

This is [SR36] SAFETY OF FILE PROTECTION SYSTEMS restricted, as in Garey and Johnson's comment,
to commands with at most one operation (Harrison, Ruzzo and Ullman's "mono-operational"
systems). In [SR36] every operation has the form "enter `rᵢ` into `P(Xⱼ, Yₖ)`" or "delete `rᵢ`
from `P(Xⱼ, Yₖ)`"; operations that create or destroy subjects or objects are not part of the
problem (Garey and Johnson's comment: it becomes undecidable if they are allowed), so the sets
`S` and `O` stay fixed. A command without an
operation changes nothing and enters nothing, so every command here has exactly one operation.
Garey and Johnson defer the execution of commands to Harrison, Ruzzo and Ullman, whose
definitions are followed:

* `R = {0, …, g - 1}`, `O = {0, …, |O| - 1}`, and `S = {0, …, |S| - 1}` with `|S| ≤ |O|`. An
  access matrix is the set of triples `(s, o, r)` with `r ∈ P(s, o)`.
* A command `(k, conds, (e, r, a, b))` has the formal parameters `X₀, …, X_{k-1}`, the
  conditions `(r₁, a₁, b₁) ∈ conds`, each "`r₁` in `(X_{a₁}, X_{b₁})`", and the operation
  "enter `r` into `(X_a, X_b)`" (`e = true`) or "delete `r` from `(X_a, X_b)`" (`e = false`).
  The rights in a command are fixed generic rights; only objects are parameters.
* Running a command replaces its formal parameters by actual parameters, which are objects
  (`x j < |O|`). It is executable when its conditions hold (`r₁ ∈ P(x a₁, x b₁)`) and its
  operation can be executed, which requires the row `x a` to be a subject (`x a < |S|`). It
  then enters `r` into, or deletes `r` from, the cell `(x a, x b)` (`Step`). A command whose
  conditions fail leaves the matrix unchanged, so such runs are omitted from `Step`.
* A command leaks `r'` from a matrix `P` when it is executable there and enters `r'` into a
  cell that does not contain `r'` (`Leaks`); the question asks for a matrix reachable from the
  initial one by `Step` from which some command leaks `r'`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR36] SAFETY OF FILE PROTECTION
SYSTEMS, p. 235 (comment: "If no command can contain more than one operation, then the problem
is NP-complete in general and solvable in polynomial time for fixed systems");
M. A. Harrison, W. L. Ruzzo and J. D. Ullman, "Protection in operating systems",
Communications of the ACM 19 (1976), 461-471, doi:10.1145/360303.360333 (Section 3: the
model; Section 4: safety, mono-operational systems, and NP-completeness of their safety
problem by a reduction from CLIQUE).
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SafetyOfMonoOperationalProtectionSystems

/-- A mono-operational command `(k, conds, (e, r, a, b))`: `k` formal parameters, the
conditions `(r₁, a₁, b₁)` ("`r₁` in `(X_{a₁}, X_{b₁})`"), and the single operation, "enter `r`
into `(X_a, X_b)`" if `e = true` and "delete `r` from `(X_a, X_b)`" if `e = false`. -/
abbrev Command := ℕ × List (ℕ × ℕ × ℕ) × (Bool × ℕ × ℕ × ℕ)

/-- An instance: the number `g` of rights, the number `|O|` of objects, the number `|S|` of
subjects, the initial access matrix as a list of triples `(s, o, r)` (`r ∈ P(s, o)`), the
commands, and the right `r'`. -/
abbrev SafetyOfMonoOperationalProtectionSystemsInstance :=
  ℕ × ℕ × ℕ × List (ℕ × ℕ × ℕ) × List Command × ℕ

/-- Well-formedness of an instance: `|S| ≤ |O|`; every triple of the initial matrix has a
subject, an object and a right; every command uses rights of `R` and formal parameters below
its parameter count `k`; and `r' ∈ R`. -/
def WellFormed (i : SafetyOfMonoOperationalProtectionSystemsInstance) : Prop :=
  i.2.2.1 ≤ i.2.1 ∧
    (∀ t ∈ i.2.2.2.1, t.1 < i.2.2.1 ∧ t.2.1 < i.2.1 ∧ t.2.2 < i.1) ∧
    (∀ c ∈ i.2.2.2.2.1, (∀ t ∈ c.2.1, t.1 < i.1 ∧ t.2.1 < c.1 ∧ t.2.2 < c.1) ∧
      c.2.2.2.1 < i.1 ∧ c.2.2.2.2.1 < c.1 ∧ c.2.2.2.2.2 < c.1) ∧
    i.2.2.2.2.2 < i.1

/-- The initial access matrix: the set of triples `(s, o, r)` listed in the instance. -/
def initialMatrix (i : SafetyOfMonoOperationalProtectionSystemsInstance) :
    Set (ℕ × ℕ × ℕ) :=
  {t | t ∈ i.2.2.2.1}

/-- Command `c` of the instance is executable on the matrix `P` with actual parameters `x`:
`c ∈ C`, every formal parameter is replaced by an object, every condition "`r₁` in
`(X_{a₁}, X_{b₁})`" holds (`(x a₁, x b₁, r₁) ∈ P`), and the row `x a` of the operation is a
subject. -/
def Executable (i : SafetyOfMonoOperationalProtectionSystemsInstance) (c : Command)
    (x : ℕ → ℕ) (P : Set (ℕ × ℕ × ℕ)) : Prop :=
  c ∈ i.2.2.2.2.1 ∧ (∀ j < c.1, x j < i.2.1) ∧ (∀ t ∈ c.2.1, (x t.2.1, x t.2.2, t.1) ∈ P) ∧
    x c.2.2.2.2.1 < i.2.2.1

/-- The matrix after the operation `(e, r, a, b)` with actual parameters `x`: `r` entered into
the cell `(x a, x b)` if `e = true`, deleted from it if `e = false`. -/
def applyOp (op : Bool × ℕ × ℕ × ℕ) (x : ℕ → ℕ) (P : Set (ℕ × ℕ × ℕ)) : Set (ℕ × ℕ × ℕ) :=
  if op.1 then insert (x op.2.2.1, x op.2.2.2, op.2.1) P
  else P \ {(x op.2.2.1, x op.2.2.2, op.2.1)}

/-- One command run: some command is executable on `P` with some actual parameters and turns
`P` into `P'`. -/
def Step (i : SafetyOfMonoOperationalProtectionSystemsInstance)
    (P P' : Set (ℕ × ℕ × ℕ)) : Prop :=
  ∃ c x, Executable i c x P ∧ P' = applyOp c.2.2 x P

/-- Some command leaks `r'` from `P`: it is executable on `P` and its operation enters `r'`
into a cell `(x a, x b)` that does not contain `r'`. -/
def Leaks (i : SafetyOfMonoOperationalProtectionSystemsInstance) (P : Set (ℕ × ℕ × ℕ)) :
    Prop :=
  ∃ c x, Executable i c x P ∧ c.2.2.1 = true ∧ c.2.2.2.1 = i.2.2.2.2.2 ∧
    (x c.2.2.2.2.1, x c.2.2.2.2.2, i.2.2.2.2.2) ∉ P

/-- Some sequence of command runs leads from the initial matrix to a matrix from which some
command leaks `r'`. -/
def SafetyOfMonoOperationalProtectionSystemsFeasible
    (i : SafetyOfMonoOperationalProtectionSystemsInstance) : Prop :=
  ∃ P, Relation.ReflTransGen (Step i) (initialMatrix i) P ∧ Leaks i P

open Classical in
/-- SAFETY OF MONO-OPERATIONAL FILE PROTECTION SYSTEMS (whether `r'` can leak) as a decision
problem over bitstrings. -/
noncomputable def safetyOfMonoOperationalProtectionSystemsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SafetyOfMonoOperationalProtectionSystemsInstance) x with
  | some i => decide (WellFormed i ∧ SafetyOfMonoOperationalProtectionSystemsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SafetyOfMonoOperationalProtectionSystems
