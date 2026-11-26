/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Foundations.Semantics.LTS.Basic
public import Mathlib.Data.Set.Finite.Basic

/-!
# Protection systems in the access-matrix model

The protection systems of Harrison, Ruzzo and Ullman: configurations `(S, O, P)` of subjects,
objects and an access matrix; the six primitive operations; commands with a condition and a body;
the yields relations of operations and of commands; and the safety question, whether a generic
right can leak.

## Main definitions

* `PrimOp`: the primitive operations `enter r into (s, o)`, `delete r from (s, o)`,
  `create subject s`, `create object o`, `destroy subject s` and `destroy object o`.
* `Configuration`: a configuration `(S, O, P)`, with finitely many objects and `S ⊆ O`.
* `PrimOp.Yields`: the relation `Q ⇒_op Q'`, and `PrimOp.lts`, the transition system it gives.
* `Command`, `Command.Holds` and `Command.Yields`: commands, their conditions and the relation
  `Q ⊢_{α(x₁, …, x_k)} Q'`.
* `ProtectionSystem` and `ProtectionSystem.lts`: a finite set of commands, and the transition
  system of their runs.
* `Command.Leaks`, `ProtectionSystem.Leaks` and `ProtectionSystem.Unsafe`: leaks and unsafety.

## Main statements

* `PrimOp.Yields.eq_enter_of_notMem_of_mem`: only `enter r into (s, o)` puts `r` into the cell
  `(s, o)`.
* `ProtectionSystem.Leaks.unsafe`: a configuration that leaks `r` is unsafe for `r`.
* `ProtectionSystem.Unsafe.of_canReach`: a configuration that can reach a configuration unsafe
  for `r` is itself unsafe for `r`.

## Implementation notes

Subjects and objects are names from a type `N`. The paper takes each created subject or object
to be a new symbol, so its model is the case of an infinite type `N`; with a finite `N` creation
can fail for lack of names. The access matrix is a function on all pairs of names that is empty
outside `S × O`, so a configuration of the paper is exactly one `Configuration`. The relations
transcribe the paper's definitions. In particular a primitive operation whose precondition fails
yields no configuration, so a command whose condition holds but one of whose operations cannot
be executed has no successor (the paper's remark on the command `α(X, Y, Z)` just before
Example 2), while a command whose condition fails leaves the configuration unchanged. Generic
rights form an arbitrary type `R`, which the paper takes finite; nothing below uses this.

## References

* M. A. Harrison, W. L. Ruzzo and J. D. Ullman, "Protection in operating systems",
  *Communications of the ACM* 19(8):461–471, 1976: Section 3 (the model) and Section 4 (leaks
  and safety).
-/

@[expose] public section

namespace Cslib.Security.AccessControl.HRU

/-- **Primitive operations of the access-matrix model.** A primitive operation of the
access-matrix model, with generic rights in `R` and operands in `α`: formal parameters in a
command's body, names once actual parameters replace them. -/
inductive PrimOp (R α : Type*) where
  /-- `enter r into (s, o)`: grant subject `s` the right `r` to object `o`. -/
  | enter (r : R) (s o : α)
  /-- `delete r from (s, o)`: remove the right `r` of subject `s` to object `o`. -/
  | delete (r : R) (s o : α)
  /-- `create subject s`. -/
  | createSubject (s : α)
  /-- `create object o`. -/
  | createObject (o : α)
  /-- `destroy subject s`. -/
  | destroySubject (s : α)
  /-- `destroy object o`. -/
  | destroyObject (o : α)
  deriving DecidableEq

namespace PrimOp

variable {R α β : Type*}

/-- **Substituting the operands of a primitive operation.** The primitive operation `op` with
each operand `a` replaced by `f a`; with `f` the actual parameters of a command run, this is the
operation `op*` of the paper. -/
def map (f : α → β) : PrimOp R α → PrimOp R β
  | enter r s o => enter r (f s) (f o)
  | delete r s o => delete r (f s) (f o)
  | createSubject s => createSubject (f s)
  | createObject o => createObject (f o)
  | destroySubject s => destroySubject (f s)
  | destroyObject o => destroyObject (f o)

end PrimOp

/-- **Configurations of a protection system.** A configuration `(S, O, P)` of a protection
system with generic rights in `R` and names in `N`: a set `S` of subjects, a finite set `O ⊇ S`
of objects, and an access matrix `P` giving the set `P[s, o]` of rights of each subject `s ∈ S`
to each object `o ∈ O`. The matrix is a function on all pairs of names that is empty outside
`S × O`. The paper takes each created subject or object to be a new symbol, so its model is the
case of an infinite type `N`; with a finite `N` creation can fail for lack of names. -/
@[ext]
structure Configuration (R N : Type*) where
  /-- The set `S` of current subjects. -/
  subjects : Set N
  /-- The set `O` of current objects. -/
  objects : Set N
  /-- There are finitely many objects. -/
  objects_finite : objects.Finite
  /-- Every subject is an object. -/
  subjects_subset_objects : subjects ⊆ objects
  /-- The access matrix: `matrix s o` is the set `P[s, o]` of rights of `s` to `o`. -/
  matrix : N → N → Set R
  /-- The access matrix is empty outside the rows of subjects and the columns of objects. -/
  mem_of_mem_matrix {s o : N} {r : R} : r ∈ matrix s o → s ∈ subjects ∧ o ∈ objects

namespace PrimOp

variable {R N : Type*}

/-- **The effect of a primitive operation.** The relation `Q ⇒_op Q'` of Harrison, Ruzzo and
Ullman: the primitive operation `op` turns the configuration `Q = (S, O, P)` into
`Q' = (S', O', P')`.

* `enter r into (s, o)` needs `s ∈ S` and `o ∈ O`; it adds `r` to `P[s, o]`.
* `delete r from (s, o)` needs `s ∈ S` and `o ∈ O`; it removes `r` from `P[s, o]`.
* `create subject s` needs `s ∉ O`; it adds `s` to `S` and to `O`, with an empty row and column.
* `create object o` needs `o ∉ O`; it adds `o` to `O`, with an empty column.
* `destroy subject s` needs `s ∈ S`; it removes `s` from `S` and from `O`.
* `destroy object o` needs `o ∈ O \ S`; it removes `o` from `O`.

Every other cell of `S' × O'` keeps its rights. An operation whose precondition fails yields no
configuration. -/
def Yields : PrimOp R N → Configuration R N → Configuration R N → Prop
  | enter r s o, Q, Q' =>
      s ∈ Q.subjects ∧ o ∈ Q.objects ∧ Q'.subjects = Q.subjects ∧ Q'.objects = Q.objects ∧
        Q'.matrix s o = insert r (Q.matrix s o) ∧
        ∀ s₁ o₁, (s₁, o₁) ≠ (s, o) → Q'.matrix s₁ o₁ = Q.matrix s₁ o₁
  | delete r s o, Q, Q' =>
      s ∈ Q.subjects ∧ o ∈ Q.objects ∧ Q'.subjects = Q.subjects ∧ Q'.objects = Q.objects ∧
        Q'.matrix s o = Q.matrix s o \ {r} ∧
        ∀ s₁ o₁, (s₁, o₁) ≠ (s, o) → Q'.matrix s₁ o₁ = Q.matrix s₁ o₁
  | createSubject s, Q, Q' =>
      s ∉ Q.objects ∧ Q'.subjects = insert s Q.subjects ∧ Q'.objects = insert s Q.objects ∧
        (∀ s₁ ∈ Q.subjects, ∀ o₁ ∈ Q.objects, Q'.matrix s₁ o₁ = Q.matrix s₁ o₁) ∧
        (∀ o₁ ∈ Q'.objects, Q'.matrix s o₁ = ∅) ∧ ∀ s₁ ∈ Q'.subjects, Q'.matrix s₁ s = ∅
  | createObject o, Q, Q' =>
      o ∉ Q.objects ∧ Q'.subjects = Q.subjects ∧ Q'.objects = insert o Q.objects ∧
        (∀ s₁ ∈ Q.subjects, ∀ o₁ ∈ Q.objects, Q'.matrix s₁ o₁ = Q.matrix s₁ o₁) ∧
        ∀ s₁ ∈ Q'.subjects, Q'.matrix s₁ o = ∅
  | destroySubject s, Q, Q' =>
      s ∈ Q.subjects ∧ Q'.subjects = Q.subjects \ {s} ∧ Q'.objects = Q.objects \ {s} ∧
        ∀ s₁ ∈ Q'.subjects, ∀ o₁ ∈ Q'.objects, Q'.matrix s₁ o₁ = Q.matrix s₁ o₁
  | destroyObject o, Q, Q' =>
      o ∈ Q.objects ∧ o ∉ Q.subjects ∧ Q'.subjects = Q.subjects ∧
        Q'.objects = Q.objects \ {o} ∧
        ∀ s₁ ∈ Q'.subjects, ∀ o₁ ∈ Q'.objects, Q'.matrix s₁ o₁ = Q.matrix s₁ o₁

/-- **The transition system of primitive operations.** Its transitions are the relations
`Q ⇒_op Q'`, so its multistep transitions `Q ⇒_{op₁} Q₁ ⇒_{op₂} ⋯ ⇒_{opₙ} Qₙ` run a sequence of
primitive operations. -/
def lts : LTS (Configuration R N) (PrimOp R N) where
  Tr Q op Q' := op.Yields Q Q'

/-- **Only entering a right puts it into a cell.** Only `enter r into (s, o)` puts the right `r`
into the cell `(s, o)`: a primitive operation that turns a configuration whose cell `(s, o)` lacks
`r` into one whose cell `(s, o)` contains `r` is `enter r into (s, o)`. -/
theorem Yields.eq_enter_of_notMem_of_mem {op : PrimOp R N} {Q Q' : Configuration R N}
    (h : op.Yields Q Q') {r : R} {s o : N} (hQ : r ∉ Q.matrix s o) (hQ' : r ∈ Q'.matrix s o) :
    op = enter r s o := by
  cases op with
  | enter r' s' o' =>
    obtain ⟨-, -, -, -, hcell, hrest⟩ := h
    by_cases hso : (s, o) = (s', o')
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hso
      rw [hcell, Set.mem_insert_iff] at hQ'
      obtain rfl := hQ'.resolve_right hQ
      rfl
    · exact absurd (hrest s o hso ▸ hQ') hQ
  | delete r' s' o' =>
    obtain ⟨-, -, -, -, hcell, hrest⟩ := h
    by_cases hso : (s, o) = (s', o')
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hso
      exact absurd (hcell ▸ hQ').1 hQ
    · exact absurd (hrest s o hso ▸ hQ') hQ
  | createSubject s' =>
    obtain ⟨-, hS, hO, hold, hrow, hcol⟩ := h
    obtain ⟨hs, ho⟩ := Q'.mem_of_mem_matrix hQ'
    by_cases hss : s = s'
    · subst hss
      exact absurd (hrow o ho ▸ hQ') (Set.notMem_empty r)
    by_cases hos : o = s'
    · subst hos
      exact absurd (hcol s hs ▸ hQ') (Set.notMem_empty r)
    rw [hS, Set.mem_insert_iff] at hs
    rw [hO, Set.mem_insert_iff] at ho
    exact absurd (hold s (hs.resolve_left hss) o (ho.resolve_left hos) ▸ hQ') hQ
  | createObject o' =>
    obtain ⟨-, hS, hO, hold, hcol⟩ := h
    obtain ⟨hs, ho⟩ := Q'.mem_of_mem_matrix hQ'
    by_cases hoo : o = o'
    · subst hoo
      exact absurd (hcol s hs ▸ hQ') (Set.notMem_empty r)
    rw [hO, Set.mem_insert_iff] at ho
    exact absurd (hold s (hS ▸ hs) o (ho.resolve_left hoo) ▸ hQ') hQ
  | destroySubject s' =>
    obtain ⟨-, -, -, hkeep⟩ := h
    obtain ⟨hs, ho⟩ := Q'.mem_of_mem_matrix hQ'
    exact absurd (hkeep s hs o ho ▸ hQ') hQ
  | destroyObject o' =>
    obtain ⟨-, -, -, -, hkeep⟩ := h
    obtain ⟨hs, ho⟩ := Q'.mem_of_mem_matrix hQ'
    exact absurd (hkeep s hs o ho ▸ hQ') hQ

end PrimOp

/-- **Commands of a protection system.** A command `α(X₁, …, X_k)` of a protection system with
generic rights in `R`, which Harrison, Ruzzo and Ullman write as
`command α(X₁, …, X_k) if r₁ in (X_{s₁}, X_{o₁}) and … then op₁ … op_n end`.
Its formal parameters are indexed by `Fin arity`, its condition is the conjunction of its tests
`r ∈ P[X_i, X_j]`, and its body is a sequence of primitive operations on the formal parameters. -/
structure Command (R : Type*) where
  /-- The number `k` of formal parameters. -/
  arity : ℕ
  /-- The tests of the condition: a triple `(r, i, j)` is the test `r ∈ P[X_i, X_j]`. A command
  with no tests has the condition that always holds. -/
  condition : List (R × Fin arity × Fin arity)
  /-- The body: the primitive operations `op₁, …, op_n`, in the order they run. -/
  body : List (PrimOp R (Fin arity))
  deriving DecidableEq

namespace Command

variable {R N : Type*}

/-- **The condition of a command holds.** The condition of the command `α` holds in the
configuration `Q` for the actual parameters `x`: every test `r ∈ P[X_i, X_j]` of `α` has
`r ∈ P[x_i, x_j]`. -/
def Holds (α : Command R) (x : Fin α.arity → N) (Q : Configuration R N) : Prop :=
  ∀ t ∈ α.condition, t.1 ∈ Q.matrix (x t.2.1) (x t.2.2)

/-- **Running a command.** The relation `Q ⊢_{α(x₁, …, x_k)} Q'` of Harrison, Ruzzo and Ullman:
running the command `α` with the actual parameters `x` on the configuration `Q` gives `Q'`. If
the condition of `α` fails in `Q`, then `Q' = Q`. Otherwise `Q'` is the end of a run
`Q ⇒_{op₁*} Q₁ ⇒ ⋯ ⇒_{opₙ*} Q'` of the body with the actual parameters substituted for the formal
ones; if some operation of the body cannot be executed, there is no such `Q'`. -/
def Yields (α : Command R) (x : Fin α.arity → N) (Q Q' : Configuration R N) : Prop :=
  (¬α.Holds x Q ∧ Q' = Q) ∨
    (α.Holds x Q ∧ PrimOp.lts.MTr Q (α.body.map (PrimOp.map x)) Q')

/-- **A command leaks a right.** The command `α` leaks the generic right `r` from the
configuration `Q`: run on `Q`, it can execute a primitive operation that enters `r` into a cell of
the access matrix that did not contain `r` just before. That is, for some actual parameters `x`
the condition of `α` holds in `Q`, and its body splits as `pre ++ op :: post` where the
operations of `pre` run from `Q` to some `Q₁` and `op` turns `Q₁` into some `Q₂` whose cell
`(s, o)` contains `r` while that of `Q₁` does not. The rest of the body need not be
executable. -/
def Leaks (α : Command R) (r : R) (Q : Configuration R N) : Prop :=
  ∃ x : Fin α.arity → N, α.Holds x Q ∧
    ∃ (pre : List (PrimOp R (Fin α.arity))) (op : PrimOp R (Fin α.arity))
      (post : List (PrimOp R (Fin α.arity))), α.body = pre ++ op :: post ∧
      ∃ Q₁ Q₂ : Configuration R N, PrimOp.lts.MTr Q (pre.map (PrimOp.map x)) Q₁ ∧
        (op.map x).Yields Q₁ Q₂ ∧ ∃ s o, r ∉ Q₁.matrix s o ∧ r ∈ Q₂.matrix s o

end Command

/-- **Protection systems as finite sets of commands.** A protection system with generic rights in
`R`: a finite set of commands. -/
structure ProtectionSystem (R : Type*) where
  /-- The finite set `C` of commands. -/
  commands : Finset (Command R)

namespace ProtectionSystem

variable {R N : Type*} (ps : ProtectionSystem R)

/-- **The transition system of a protection system.** Its labels are commands with actual
parameters, and `Q` has a transition labelled `α(x)` to `Q'` when `α` is a command of the system
and `Q ⊢_{α(x)} Q'`. Reachability in it is the relation `⊢*` of Harrison, Ruzzo and Ullman. -/
def lts : LTS (Configuration R N) (Σ α : Command R, Fin α.arity → N) where
  Tr Q a Q' := a.1 ∈ ps.commands ∧ a.1.Yields a.2 Q Q'

/-- **A configuration leaks a right.** The configuration `Q` leaks the generic right `r`: some
command of the protection system leaks `r` from `Q`. -/
def Leaks (r : R) (Q : Configuration R N) : Prop :=
  ∃ α ∈ ps.commands, α.Leaks r Q

/-- **Protection systems in the access-matrix model.** A protection system in the model of
Harrison, Ruzzo and Ullman, with generic rights in a type `R`, is a finite set of commands; the
paper takes the set of generic rights finite, and nothing below uses it. A configuration is a
triple `(S, O, P)` of a set `S` of subjects, a finite set `O ⊇ S` of objects, both made of names
from a type `N`, and an access matrix `P` assigning to each pair `(s, o) ∈ S × O` a set
`P[s, o] ⊆ R` of rights. The paper takes each created subject or object to be a new symbol, so its
model is the case of an infinite type `N`; with a finite `N` creation can fail for lack of names.
The matrix is recorded as a function on all pairs of names that is empty outside `S × O`, so each
configuration of the paper is recorded in exactly one way.

Each command `α(X₁, …, X_k)` has formal parameters, a condition that is a conjunction of tests
`r ∈ P[X_i, X_j]`, and a body that is a sequence of primitive operations: enter `r` into
`(X_i, X_j)`, delete `r` from `(X_i, X_j)`, create or destroy a subject `X_i`, create or destroy an
object `X_i`. A primitive operation turns a configuration `(S, O, P)` into a new one only when its
precondition holds: enter `r` into `(s, o)` and delete `r` from `(s, o)` need `s ∈ S` and
`o ∈ O`, and add `r` to, or remove `r` from, `P[s, o]`; create subject `s` needs `s ∉ O`, and
adds `s` to `S` and to `O` with an empty row and an empty column; create object `o` needs
`o ∉ O`, and adds `o` to `O` with an empty column; destroy subject `s` needs `s ∈ S`, and removes
`s` from `S` and from `O`; destroy object `o` needs `o ∈ O \ S`, and removes `o` from `O`; every
other cell of the new matrix keeps its rights. Running `α` with actual parameters `x₁, …, x_k`,
which may be any names, on a configuration `Q` gives `Q` itself if some test of the condition
fails in `Q`. Otherwise it gives the configuration reached by executing the body with each `x_i`
in place of `X_i`, and it gives no configuration if some operation of the body cannot be
executed. A configuration is reachable from `Q` if finitely many runs of commands of the system
lead to it from `Q`.

A configuration `Q` leaks the right `r` if some command of the system, run on `Q` with actual
parameters for which its condition holds in `Q`, can execute an initial segment of its body whose
last operation enters `r` into a cell that did not contain `r` just before; the rest of the body
need not be executable. A configuration `Q₀` is unsafe for `r` if some configuration reachable
from `Q₀` leaks `r`, and safe for `r` otherwise. -/
def Unsafe (r : R) (Q₀ : Configuration R N) : Prop :=
  ∃ Q, ps.lts.CanReach Q₀ Q ∧ ps.Leaks r Q

variable {ps} {r : R} {Q₀ Q : Configuration R N}

/-- **A configuration that leaks a right is unsafe for it.** A configuration that leaks a generic
right `r` is unsafe for `r`. -/
theorem Leaks.unsafe (h : ps.Leaks r Q) : ps.Unsafe r Q :=
  ⟨Q, LTS.CanReach.refl _ Q, h⟩

/-- **Unsafety propagates backwards along runs of commands.** A configuration that can reach a
configuration unsafe for `r` is itself unsafe for `r`. -/
theorem Unsafe.of_canReach (hQ : ps.lts.CanReach Q₀ Q) (h : ps.Unsafe r Q) : ps.Unsafe r Q₀ := by
  obtain ⟨Q', hQQ', hleak⟩ := h
  exact ⟨Q', hQ.trans hQQ', hleak⟩

end ProtectionSystem

end Cslib.Security.AccessControl.HRU
