/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Mathlib.Logic.Function.Basic

/-!
# The x86-TSO abstract machine

The storage subsystem has shared memory, a FIFO store buffer for each thread, and a global
lock. Only the seven single-step rules are modeled, not instruction execution, initial states,
or progress conditions. Addresses, values, and thread identifiers are abstract types; shared memory
is a total map as in the storage-state description in §3.1.

## References

* P. Sewell, S. Sarkar, S. Owens, F. Zappa Nardelli, and M. O. Myreen,
  [x86-TSO: A Rigorous and Usable Programmer's Model for x86 Multiprocessors][sewell2010],
  *Communications of the ACM* 53(7):89–97, 2010, §3.1, rules 1–7.
* S. Owens, S. Sarkar, and P. Sewell, [A Better x86 Memory Model: x86-TSO][owens2009],
  TPHOLs 2009, LNCS 5674:391–407, Fig. 2 (reference [27] of the CACM article).
  Its formal lock rule requires an empty local buffer, a premise omitted in the CACM prose
  for rule 6. We use the formal lock guard.

[sewell2010]: https://www.cl.cam.ac.uk/~pes20/weakmemory/cacm.pdf
[owens2009]: https://www.cl.cam.ac.uk/~pes20/weakmemory/x86tso-paper.tphols.pdf
-/

@[expose] public section

namespace Cslib.Semantics.WeakMemory.X86TSO

universe u v w

/-- The x86-TSO storage state consists of a total shared-memory map from addresses to values,
 one buffer of pending address-value pairs per thread, and an optional global lock owner.
 Each buffer lists its writes from oldest to newest. No lock owner means the lock is free. -/
structure State (Thread : Type u) (Address : Type v) (Value : Type w) where
  /-- Shared memory maps each address to its current value. -/
  memory : Address → Value
  /-- The pending address-value pairs for each thread, in FIFO order. -/
  buffers : Thread → List (Address × Value)
  /-- The lock owner, or `none` when no thread holds the lock. -/
  lockOwner : Option Thread

/-- The six storage events are a read, a write, a flush, a fence (MFENCE), lock acquisition, and
lock release. Each records the acting thread. Reads and writes also record an address and a
value; the other four carry no additional data. The same read label is used whether the value
comes from memory or a buffer. A flush is the thread-indexed internal propagation event $\tau$. -/
inductive Label (Thread : Type u) (Address : Type v) (Value : Type w) where
  /-- Read the given value at the given address. -/
  | read (thread : Thread) (address : Address) (value : Value)
  /-- Enqueue a write to the given address. -/
  | write (thread : Thread) (address : Address) (value : Value)
  /-- Propagate the oldest buffered write of the given thread. -/
  | flush (thread : Thread)
  /-- Execute an MFENCE. -/
  | mfence (thread : Thread)
  /-- Begin a locked instruction by acquiring the lock. -/
  | acquire (thread : Thread)
  /-- End a locked instruction by releasing the lock. -/
  | release (thread : Thread)

variable {Thread : Type u} {Address : Type v} {Value : Type w}

/-- A thread is not blocked when the lock is free or the thread itself holds it. -/
def State.NotBlocked (s : State Thread Address Value) (p : Thread) : Prop :=
  s.lockOwner = none ∨ s.lockOwner = some p

/-- The value of the newest pending write to `a` by `p`, or `none` if there is no such write. -/
def State.latestWrite [DecidableEq Address] (s : State Thread Address Value)
    (p : Thread) (a : Address) : Option Value :=
  ((s.buffers p).reverse.find? (fun entry => decide (entry.1 = a))).map Prod.snd

/-- A transition relates a storage state, an event, and a resulting storage state. A thread is
unblocked when the lock is free or the thread owns it. Exactly these transitions are allowed:

- An unblocked thread reads the shared value at an address if its local buffer has no write to
  that address, or reads the newest local buffered value for that address otherwise. Neither read
  changes the state.
- Any thread can enqueue an address-value pair at the newest end of its local buffer. Only that
  buffer changes.
- An unblocked thread with a nonempty local buffer can flush its oldest write, removing that
  entry and replacing the value at its address in shared memory. All other components stay fixed.
- A thread with an empty local buffer can execute MFENCE. Neither the lock nor any other part
  of the state changes, and the thread need not be unblocked.
- A thread can acquire a free lock if its local buffer is empty; it becomes the owner. A thread
  can release the lock if it owns the lock and its local buffer is empty; the lock becomes free.
  Both steps leave memory and all buffers unchanged. -/
inductive Step [DecidableEq Thread] [DecidableEq Address] :
    State Thread Address Value → Label Thread Address Value → State Thread Address Value →
      Prop where
  /-- Rule 1: read memory only when the local buffer has no write to the address. -/
  | readMemory {s : State Thread Address Value} {p : Thread} {a : Address}
      (unblocked : s.NotBlocked p) (noWrite : s.latestWrite p a = none) :
      Step s (.read p a (s.memory a)) s
  /-- Rule 2: forward the newest pending local write to the requested address. -/
  | readBuffer {s : State Thread Address Value} {p : Thread} {a : Address} {value : Value}
      (unblocked : s.NotBlocked p) (forwarded : s.latestWrite p a = some value) :
      Step s (.read p a value) s
  /-- Rule 3: append a write to the local buffer, even if another thread holds the lock. -/
  | write (s : State Thread Address Value) (p : Thread) (a : Address) (value : Value) :
      Step s (.write p a value)
        { s with buffers := Function.update s.buffers p (s.buffers p ++ [(a, value)]) }
  /-- Rule 4: remove only the oldest local write and commit it to shared memory. -/
  | flush {s : State Thread Address Value} {p : Thread} {a : Address} {value : Value}
      {tail : List (Address × Value)} (unblocked : s.NotBlocked p)
      (oldest : s.buffers p = (a, value) :: tail) :
      Step s (.flush p)
        { s with memory := Function.update s.memory a value
                 buffers := Function.update s.buffers p tail }
  /-- Rule 5: MFENCE requires an empty local buffer and leaves the state unchanged. -/
  | mfence {s : State Thread Address Value} {p : Thread} (empty : s.buffers p = []) :
      Step s (.mfence p) s
  /-- Rule 6 with the cited formal guard: acquire a free lock with an empty local buffer. -/
  | acquire {s : State Thread Address Value} {p : Thread}
      (free : s.lockOwner = none) (empty : s.buffers p = []) :
      Step s (.acquire p) { s with lockOwner := some p }
  /-- Rule 7: only the owner can release the lock, and only with an empty local buffer. -/
  | release {s : State Thread Address Value} {p : Thread}
      (owns : s.lockOwner = some p) (empty : s.buffers p = []) :
      Step s (.release p) { s with lockOwner := none }

/-- **The x86-TSO abstract machine.** The labeled transition system on shared memory, per-thread
FIFO write buffers, and a global lock, with `Step` as its transition relation. This is the
storage subsystem of Sewell et al., *Communications of the ACM* 53(7):89–97, 2010, §3.1,
rules 1–7, using the empty-buffer acquisition premise of its cited formal lock rule
(Owens, Sarkar, and Sewell, TPHOLs 2009, Fig. 2). -/
def abstractMachine (Thread : Type u) (Address : Type v) (Value : Type w)
    [DecidableEq Thread] [DecidableEq Address] :
    LTS (State Thread Address Value) (Label Thread Address Value) where
  Tr := Step

end Cslib.Semantics.WeakMemory.X86TSO
