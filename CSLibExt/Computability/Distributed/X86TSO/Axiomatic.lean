/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Finite.Defs
public import Mathlib.Order.RelIso.Set

/-!
# The axiomatic x86-TSO model

The axiomatic x86-TSO memory model of Owens, Sarkar and Sewell abstracts an execution of an x86
program as an event structure (`EventStructure`): a type of events, each a read or a write of a
value at a memory address or a register, or an MFENCE, and each belonging to an instruction given
by its processor and its program-order index; an intra-instruction causality relation; and the
sets of events of the LOCK'd instructions. Program order (`EventStructure.po`) is the union of the
order of each processor's instructions and intra-instruction causality. An execution witness
(`ExecutionWitness`) consists of a memory order, a reads-from map and an initial state, and
`ValidExecution` collects the conditions under which a witness is a valid execution of an event
structure. An execution is allowed by the model when its event structure has a valid execution
witness.

The definitions follow Section 3 of the source, which defines event structures before
Section 3.1 and execution witnesses and their validity in Section 3.2 (the technical report
collects the validity conditions in Appendix D.1), with these encodings. Events are the elements
of a type, which identifies them without event ids. Processors, addresses, registers and values
are arbitrary types, rather than natural numbers and 32-bit words, and the processor type
replaces the source's set of processors, which only the well-formedness conditions use. Only
MFENCE barriers are events: no condition of the model mentions LFENCE or SFENCE. As in the source,
the memory order is a reflexive partial order, and the well-formedness conditions on event
structures (technical report, Appendix C) are not part of validity.

## Main definitions

* `Location`, `Action`: the locations and the actions of events.
* `EventStructure`, `EventStructure.po`: event structures and their program order.
* `ExecutionWitness`: memory order, reads-from map and initial state.
* `ValidExecution`: the valid executions of the axiomatic x86-TSO model.

## References

* S. Owens, S. Sarkar and P. Sewell, *A better x86 memory model: x86-TSO*, Theorem Proving in
  Higher Order Logics (TPHOLs 2009), LNCS 5674, Springer (2009), 391–407, Section 3.
* S. Owens, S. Sarkar and P. Sewell, *A better x86 memory model: x86-TSO (extended version)*,
  Technical Report UCAM-CL-TR-745, University of Cambridge (2009), Appendices C and D.1.
-/

@[expose] public section

namespace Cslib.Distributed.X86TSO

variable {E P A R V L : Type*}

/-- **Locations of the x86-TSO model.** A location is either a memory address $a$ or a register
$r$ of a processor $p$ (Owens, Sarkar and Sewell, *TPHOLs 2009*, Section 3). -/
inductive Location (P A R : Type*) where
  /-- The memory location at address `a`. -/
  | mem (a : A)
  /-- The register `r` of processor `p`. -/
  | reg (p : P) (r : R)

/-- **Actions of x86-TSO events.** The action of an event reads a value $v$ at a location $l$,
writes $v$ at $l$, or is an MFENCE (Owens, Sarkar and Sewell, *TPHOLs 2009*, Section 3). The
source's actions also include LFENCE and SFENCE barriers, which are left out, as no condition of
validity uses them. -/
inductive Action (L V : Type*) where
  /-- A read of the value `v` at the location `l`. -/
  | read (l : L) (v : V)
  /-- A write of the value `v` at the location `l`. -/
  | write (l : L) (v : V)
  /-- An MFENCE. -/
  | mfence

/-- **The location of an action.** A read or a write at a location $l$ has location $l$, and an
MFENCE has none. -/
def Action.loc : Action L V → Option L
  | .read l _ => some l
  | .write l _ => some l
  | .mfence => none

/-- **Event structures of the axiomatic x86-TSO model.** An event structure on a type $E$ of
events assigns to each event the processor $p$ and the program-order index $i \in \mathbb{N}$ of
its instruction, the $i$-th instruction of $p$, and its action: a read or a write of a value at a
memory address or at a register of a processor, or an MFENCE. It also carries an
intra-instruction causality relation on the events, and the atomicity data: a set of sets of
events, those of each LOCK'd instruction (Owens, Sarkar and Sewell, *TPHOLs 2009*,
Section 3). -/
structure EventStructure (E P A R V : Type*) where
  /-- The processor of the instruction of each event. -/
  proc : E → P
  /-- The program-order index of the instruction of each event. -/
  poi : E → ℕ
  /-- The action of each event. -/
  action : E → Action (Location P A R) V
  /-- The intra-instruction causality relation. -/
  intraCausality : E → E → Prop
  /-- The sets of events of the LOCK'd instructions. -/
  atomicity : Set (Set E)

namespace EventStructure

variable (S : EventStructure E P A R V)

/-- **Program order of an x86-TSO event structure.** An event $e_1$ precedes an event $e_2$ in
program order when the instructions of $e_1$ and $e_2$ belong to the same processor and that of
$e_1$ has the smaller program-order index, or when $e_1$ precedes $e_2$ in intra-instruction
causality (Owens, Sarkar and Sewell, *TPHOLs 2009*, Section 3.2, `po_iico`). -/
def po (e₁ e₂ : E) : Prop :=
  S.proc e₁ = S.proc e₂ ∧ S.poi e₁ < S.poi e₂ ∨ S.intraCausality e₁ e₂

/-- **Memory reads of an x86-TSO event structure.** The memory reads are the events whose action
is a read at a memory address. -/
def memReads : Set E :=
  {e | ∃ a v, S.action e = .read (.mem a) v}

/-- **Memory writes of an x86-TSO event structure.** The memory writes are the events whose
action is a write at a memory address. -/
def memWrites : Set E :=
  {e | ∃ a v, S.action e = .write (.mem a) v}

/-- **Memory accesses of an x86-TSO event structure.** The memory accesses are the memory reads
and the memory writes. -/
def memAccesses : Set E :=
  S.memReads ∪ S.memWrites

/-- **MFENCE events of an x86-TSO event structure.** The MFENCE events are the events whose
action is an MFENCE. -/
def mfences : Set E :=
  {e | S.action e = .mfence}

/-- **Previous writes in an x86-TSO event structure.** For a relation $\prec$ on events and an
event $e$, the previous writes are the writes $w$ with $w \prec e$ whose location is that of $e$
(Owens, Sarkar and Sewell, *TPHOLs 2009*, Section 3.2, `previous_writes`). -/
def previousWrites (r : E → E → Prop) (e : E) : Set E :=
  {w | (∃ l v, S.action w = .write l v) ∧ r w e ∧ (S.action w).loc = (S.action e).loc}

end EventStructure

/-- **Execution witnesses of the axiomatic x86-TSO model.** An execution witness for events of
type $E$ consists of a memory order $\mathrm{mo}$ and a reads-from map $\mathrm{rf}$, relations on
the events, where $(w, r) \in \mathrm{rf}$ means that the read $r$ reads from the write $w$, and an
initial state, a partial map from locations to values (Owens, Sarkar and Sewell, *TPHOLs 2009*,
Section 3.2). -/
structure ExecutionWitness (E P A R V : Type*) where
  /-- The memory order. -/
  mo : E → E → Prop
  /-- The reads-from map: `rf w r` when the read `r` reads from the write `w`. -/
  rf : E → E → Prop
  /-- The initial state, a partial map from locations to values. -/
  initialState : Location P A R → Option V

open EventStructure

/-- **Valid executions of the axiomatic x86-TSO model.** An execution witness $X$ is a valid
execution of an event structure $S$ when the following hold, with $\mathrm{po}$ the program order
of $S$.

* The memory order $\mathrm{mo}$ relates only memory accesses; it is a partial order on them, and
  a linear order on the memory writes.
* Every memory access has only finitely many $\mathrm{mo}$-predecessors, and for every memory
  write $w$ only finitely many events with the location of $w$ are unrelated to $w$ by
  $\mathrm{mo}$.
* $\mathrm{po}$ is included in $\mathrm{mo}$ for a memory read followed by a memory access, for a
  memory write followed by a memory write, for a memory write followed by a memory read with an
  MFENCE between them, and for two memory accesses one of which belongs to a LOCK'd instruction.
* The memory accesses of each LOCK'd instruction are atomic in $\mathrm{mo}$: every other memory
  access precedes all of them or follows all of them.
* Every pair $(w, r) \in \mathrm{rf}$ relates a read $r$ to a write $w$ of the same value at the
  same location. If $w$ is a memory write, it is $\mathrm{mo}$-maximal among the writes to the
  location of $r$ that precede $r$ in $\mathrm{mo}$ or in $\mathrm{po}$; otherwise it is
  $\mathrm{po}$-maximal among the writes to the location of $r$ that precede $r$ in
  $\mathrm{po}$.
* A read outside the range of $\mathrm{rf}$ reads the initial value of its location, and no write
  to that location precedes it in $\mathrm{mo}$ or in $\mathrm{po}$.

(Owens, Sarkar and Sewell, *TPHOLs 2009*, Section 3.2; technical report UCAM-CL-TR-745,
Appendix D.1, `valid_execution`.) -/
structure ValidExecution (S : EventStructure E P A R V) (X : ExecutionWitness E P A R V) :
    Prop where
  /-- The memory order relates only memory accesses. -/
  mem_of_mo : ∀ ⦃e₁ e₂⦄, X.mo e₁ e₂ → e₁ ∈ S.memAccesses ∧ e₂ ∈ S.memAccesses
  /-- The memory order is a partial order on the memory accesses. -/
  isPartialOrder_mo : IsPartialOrder S.memAccesses (Subrel X.mo (· ∈ S.memAccesses))
  /-- The memory order is a linear order on the memory writes. -/
  isLinearOrder_mo : IsLinearOrder S.memWrites (Subrel X.mo (· ∈ S.memWrites))
  /-- Every memory access has only finitely many predecessors in the memory order. -/
  finite_mo_prefix : ∀ e ∈ S.memAccesses, {e' | X.mo e' e}.Finite
  /-- Every memory write is unrelated by the memory order to only finitely many events with its
  location. -/
  finite_unrelated : ∀ w ∈ S.memWrites,
    {e | (S.action e).loc = (S.action w).loc ∧ ¬ X.mo e w ∧ ¬ X.mo w e}.Finite
  /-- Program order is included in the memory order for a memory read followed by a memory
  access. -/
  mo_of_po_read : ∀ r ∈ S.memReads, ∀ e ∈ S.memAccesses, S.po r e → X.mo r e
  /-- Program order is included in the memory order for two memory writes. -/
  mo_of_po_write : ∀ w₁ ∈ S.memWrites, ∀ w₂ ∈ S.memWrites, S.po w₁ w₂ → X.mo w₁ w₂
  /-- Program order is included in the memory order for a memory write followed by a memory
  read with an MFENCE between them. -/
  mo_of_po_mfence : ∀ w ∈ S.memWrites, ∀ r ∈ S.memReads, ∀ f ∈ S.mfences,
    S.po w f → S.po f r → X.mo w r
  /-- Program order is included in the memory order for two memory accesses one of which belongs
  to a LOCK'd instruction. -/
  mo_of_po_locked : ∀ e₁ ∈ S.memAccesses, ∀ e₂ ∈ S.memAccesses, ∀ es ∈ S.atomicity,
    e₁ ∈ es ∨ e₂ ∈ es → S.po e₁ e₂ → X.mo e₁ e₂
  /-- Every other memory access precedes or follows all memory accesses of a LOCK'd
  instruction in the memory order. -/
  atomic : ∀ es ∈ S.atomicity, ∀ e ∈ S.memAccesses \ es,
    (∀ e' ∈ es ∩ S.memAccesses, X.mo e e') ∨ (∀ e' ∈ es ∩ S.memAccesses, X.mo e' e)
  /-- The reads-from map relates a write to a read of the same value at the same location. -/
  rf_read_write : ∀ ⦃w r⦄, X.rf w r → ∃ l v, S.action w = .write l v ∧ S.action r = .read l v
  /-- A read from a memory write reads from a write that is maximal in the memory order among
  the writes to its location that precede it in the memory order or in program order. -/
  rf_mem : ∀ ⦃w r⦄, X.rf w r → w ∈ S.memAccesses →
    w ∈ S.previousWrites X.mo r ∪ S.previousWrites S.po r ∧
      ∀ w' ∈ S.previousWrites X.mo r ∪ S.previousWrites S.po r, X.mo w w' → w = w'
  /-- A read from a register write reads from a write that is maximal in program order among the
  writes to its location that precede it in program order. -/
  rf_reg : ∀ ⦃w r⦄, X.rf w r → w ∉ S.memAccesses →
    w ∈ S.previousWrites S.po r ∧ ∀ w' ∈ S.previousWrites S.po r, S.po w w' → w = w'
  /-- A read outside the range of the reads-from map reads the initial value of its location,
  and no write to that location precedes it in the memory order or in program order. -/
  initial : ∀ ⦃r l v⦄, S.action r = .read l v → (∀ w, ¬ X.rf w r) →
    X.initialState l = some v ∧ S.previousWrites X.mo r ∪ S.previousWrites S.po r = ∅

end Cslib.Distributed.X86TSO
