/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Logic.Function.Basic

/-!
# The deterministic cell-probe model

A deterministic operation is a finite decision tree of reads and writes on a fixed set of
`cells` cells of `width` bits each. For a given operation input, the tree is chosen without
access to the initial contents. After a read, the word determines the subtree to follow, so
later addresses, written words, and the result can depend on all earlier reads. Pure computation
of the initial tree or of a continuation is free. Only the cell contents persist between
operations; the final memory of one run can be supplied to the next.

The number of cells and the word width are independent parameters: addresses need not fit in a
word. The model permits empty memory and zero-bit words (which have just one possible value).

## References

* E. Demaine, *6.851: Advanced Data Structures*, Lecture 11, "Integer data structures",
  MIT, Fall 2017 scribe notes, [§2.3](https://courses.csail.mit.edu/6.851/spring21/scribe/lec11.pdf).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.CellProbe

universe u

/-- Cell-probe memory with `cells` addresses and word width `width` is the total map
`Fin cells → BitVec width`. Each address has exactly one word; addresses need not fit in a
word. With zero cells there are no addresses, and with zero width there is one possible word. -/
abbrev Memory (cells width : Nat) := Fin cells → BitVec width

/-- A deterministic cell-probe program has `cells` addresses, word width `width` and result type
`α`. It is a finite tree with three node forms:

- A return leaf holds a value of type `α` and accesses no cells.
- A read holds an address in `Fin cells` and one continuation program for each possible word
  in `BitVec width`; the observed word chooses the branch.
- A write holds an address in `Fin cells`, a word in `BitVec width`, and a single continuation
  program. The old cell contents do not choose the continuation. -/
inductive Program (cells width : Nat) (α : Type u) where
  /-- Return a value without probing memory. -/
  | pure (result : α)
  /-- Read a cell and choose the continuation from the word read. -/
  | read (address : Fin cells) (next : BitVec width → Program cells width α)
  /-- Replace a cell's word, then continue without observing its previous contents. -/
  | write (address : Fin cells) (value : BitVec width) (next : Program cells width α)

/-- A cell-probe execution result contains the value of type `α` at the reached return leaf, the
final memory (still a map `Fin cells → BitVec width`), and a natural-number count of read and
write occurrences on the execution path, including repeated probes. -/
structure RunResult (cells width : Nat) (α : Type u) where
  /-- The value at the reached leaf. -/
  result : α
  /-- The cell contents after all writes on the execution path. -/
  memory : Memory cells width
  /-- The number of read and write occurrences on the execution path. -/
  probes : Nat

/-- Execute a deterministic cell-probe program on the total memory `Fin cells → BitVec width`.
A return leaves memory unchanged and costs zero. A read of a bounded address selects the
continuation for its current word and passes it unchanged memory. A write replaces just the
addressed word before running its continuation, without observing the old word. Each executed
read or write adds one probe, including repeated accesses to the same address and writes of a
word already stored there. No other computation is charged. The result records the returned
value, final memory, and total probes. Addresses need not fit in a word; zero cells admit no
probes, and zero-bit words have exactly one possible value. -/
def Program.run {cells width : Nat} {α : Type u} (program : Program cells width α)
    (memory : Memory cells width) : RunResult cells width α :=
  match program with
  | .pure result => ⟨result, memory, 0⟩
  | .read address next =>
    let tail := (next (memory address)).run memory
    { tail with probes := tail.probes + 1 }
  | .write address value next =>
    let tail := next.run (Function.update memory address value)
    { tail with probes := tail.probes + 1 }
termination_by structural program

end Cslib.Algorithms.Lean.CellProbe
