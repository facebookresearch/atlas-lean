/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Foundations.Semantics.WeakMemory.X86TSOAbstractMachine

/-!
# Sequentially consistent executions in the x86-TSO machine

Execute the same program against either a single shared memory or the x86-TSO storage machine.
The program is a labelled transition system on arbitrary local state (for example, all threads'
registers and control locations). It interacts with storage on reads including their results,
writes, fences, acquisitions and releases; it can also take local steps. A storage flush is not a
program instruction. The program determines its own instruction ordering and control flow.

An SC store changes memory immediately and so requires that no *other* thread own the lock. On
TSO the enqueue itself has no such guard, but the following flush does. `mTr_immediate` inserts
just that flush after every store, with empty buffers at every matched program boundary.
`outcome_of_sc` preserves the visible trace and exact accepted final state. This finite inclusion
is not its converse, a data-race-freedom theorem, an instruction decoder or a hardware result.

## References

* P. Sewell, S. Sarkar, S. Owens, F. Zappa Nardelli and M. O. Myreen,
  [x86-TSO: A Rigorous and Usable Programmer's Model for x86 Multiprocessors](https://www.cl.cam.ac.uk/~pes20/weakmemory/cacm.pdf),
  *Communications of the ACM* 53(7):89–97, 2010. See §3.1 for the storage rules and the
  synchronization with thread actions, and §5 for the immediate-flush observation.
-/

@[expose] public section

namespace Cslib.Semantics.WeakMemory.X86TSO.SC

universe u v w x y

/-- Sequentially consistent storage: a total shared memory and an optional global lock owner.
There are no pending writes. -/
structure Storage (Thread : Type u) (Address : Type v) (Value : Type w) where
  /-- The current shared value at each address. -/
  memory : Address → Value
  /-- The thread holding the lock, or `none` when it is free. -/
  lockOwner : Option Thread

variable {T : Type u} {A : Type v} {V : Type w} {Q : Type x} {S : Type y}

/-- Match an SC storage boundary by retaining memory and lock ownership and giving *every*
thread an empty FIFO. -/
def Storage.embed (s : Storage T A V) : State T A V :=
  ⟨s.memory, fun _ => [], s.lockOwner⟩

/-- The atomic SC storage steps. Reads return shared memory and stores replace one shared value;
both require the lock to be free or held by the actor. A fence is inert even for a blocked
thread. Acquire needs a free lock and release needs ownership. There is no propagation step. -/
inductive StorageStep [DecidableEq A] : Storage T A V → Label T A V → Storage T A V → Prop where
  | read {s : Storage T A V} {p : T} {a : A} (ok : s.lockOwner = none ∨ s.lockOwner = some p) :
      StorageStep s (.read p a (s.memory a)) s
  | write {s : Storage T A V} {p : T} {a : A} {v : V}
      (ok : s.lockOwner = none ∨ s.lockOwner = some p) :
      StorageStep s (.write p a v) { s with memory := Function.update s.memory a v }
  | mfence (s : Storage T A V) (p : T) : StorageStep s (.mfence p) s
  | acquire {s : Storage T A V} {p : T} (free : s.lockOwner = none) :
      StorageStep s (.acquire p) { s with lockOwner := some p }
  | release {s : Storage T A V} {p : T} (owns : s.lockOwner = some p) :
      StorageStep s (.release p) { s with lockOwner := none }

/-- The storage LTS whose transitions are single atomic SC storage operations. -/
def storageMachine [DecidableEq A] : LTS (Storage T A V) (Label T A V) := ⟨StorageStep⟩

/-- Couple one program to storage. A `none` transition is local to the program. A `some` read,
write, fence, acquire or release must be taken by both systems with exactly the same label.
A `some (.flush p)` transition is taken by storage alone, keeping the program state fixed;
any flush-labelled entries in the program relation are ignored. -/
def coupled (program : LTS Q (Option (Label T A V))) (storage : LTS S (Label T A V)) :
    LTS (Q × S) (Option (Label T A V)) where
  Tr c e d :=
    (match e with
    | some (.flush _) => d.1 = c.1
    | _ => program.Tr c.1 e d.1) ∧
    (match e with
    | none => d.2 = c.2
    | some l => storage.Tr c.2 l d.2)

/-- Erase local program steps and storage propagation, retaining the complete labels of all
synchronized actions, including read values. -/
def visibleTrace (es : List (Option (Label T A V))) : List (Label T A V) :=
  es.filterMap fun e => match e with
    | some (.flush _) => none
    | _ => e

/-- The raw target segment for one source event: a store is followed immediately by propagation
by its own thread, while every other event is retained once. -/
def immediate : Option (Label T A V) → List (Option (Label T A V))
  | some (.write p a v) => [some (.write p a v), some (.flush p)]
  | e => [e]

/-- Inserting the immediate propagations does not change the visible trace. -/
theorem visibleTrace_immediate (es : List (Option (Label T A V))) :
    visibleTrace (es.flatMap immediate) = visibleTrace es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | none => exact ih
    | some l => cases l <;> simp_all [visibleTrace, immediate]

variable (program : LTS Q (Option (Label T A V)))

/-- Match a whole configuration: keep all program state and embed its SC storage with empty
buffers and unchanged lock owner. -/
def boundary (c : Q × Storage T A V) : Q × State T A V := (c.1, c.2.embed)

variable [DecidableEq T] [DecidableEq A]

private theorem step_immediate {c d : Q × Storage T A V} {e : Option (Label T A V)}
    (h : (coupled program storageMachine).Tr c e d) :
    (coupled program (abstractMachine T A V)).MTr (boundary c) (immediate e) (boundary d) := by
  obtain ⟨q, s⟩ := c
  obtain ⟨r, t⟩ := d
  obtain ⟨hp, hs⟩ := h
  cases e with
  | none =>
    change t = s at hs
    subst t
    exact .single _ ⟨hp, rfl⟩
  | some l =>
    change StorageStep s l t at hs
    cases hs with
    | read ok => exact .single _ ⟨hp, Step.readMemory ok rfl⟩
    | mfence => exact .single _ ⟨hp, Step.mfence rfl⟩
    | acquire free => exact .single _ ⟨hp, Step.acquire free rfl⟩
    | release owns => exact .single _ ⟨hp, Step.release owns rfl⟩
    | @write p a v ok =>
      let queued : State T A V := { s.embed with
        buffers := Function.update s.embed.buffers p (s.embed.buffers p ++ [(a, v)]) }
      refine .stepL (s2 := (r, queued)) ⟨hp, Step.write s.embed p a v⟩ (.stepL ?_ .refl)
      refine ⟨rfl, ?_⟩
      have oldest : queued.buffers p = [(a, v)] := by simp [queued, Storage.embed]
      have drain := Step.flush (s := queued) (p := p) (tail := []) ok oldest
      have empty : Function.update queued.buffers p [] = fun _ => [] := by
        funext i
        by_cases hi : i = p <;> simp [queued, hi, Storage.embed]
      rw [empty] at drain
      exact drain

/-- Every finite execution of the coupled SC machine lifts to the *same* program coupled to
`abstractMachine`, with the precise raw trace obtained by inserting one silent flush after each
store. Both endpoints retain program state, shared memory and lock owner, with all buffers empty. -/
theorem mTr_immediate {c d : Q × Storage T A V} {es : List (Option (Label T A V))}
    (run : (coupled program storageMachine).MTr c es d) :
    (coupled program (abstractMachine T A V)).MTr (boundary c) (es.flatMap immediate)
      (boundary d) := by
  induction run with
  | refl => exact .refl
  | stepL h _ ih => exact (step_immediate program h).comp _ ih

/-- An accepted finite outcome of a coupled system: its final program state satisfies `done`,
and a finite run reaches the specified final configuration with exactly the given visible trace.
Acceptance is the client's predicate, not deadlock of a storage machine. -/
def Outcome (storage : LTS S (Label T A V)) (done : Q → Prop) (c : Q × S)
    (trace : List (Label T A V)) (d : Q × S) : Prop :=
  done d.1 ∧ ∃ es, (coupled program storage).MTr c es d ∧ visibleTrace es = trace

/-- Every accepted SC outcome is an x86-TSO outcome for the identical program, initial program
state, memory and lock owner, and acceptance predicate. The visible trace (including read results)
and entire final program state, memory and lock owner agree; the TSO buffers start and end empty. -/
theorem outcome_of_sc {done : Q → Prop} {c d : Q × Storage T A V} {trace : List (Label T A V)}
    (h : Outcome program storageMachine done c trace d) :
    Outcome program (abstractMachine T A V) done (boundary c) trace (boundary d) := by
  obtain ⟨accepted, es, run, rfl⟩ := h
  exact ⟨accepted, es.flatMap immediate, mTr_immediate program run, visibleTrace_immediate es⟩

end Cslib.Semantics.WeakMemory.X86TSO.SC
