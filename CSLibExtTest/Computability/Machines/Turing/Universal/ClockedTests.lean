/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.Universal.Clocked
public meta import CSLibExt.Computability.Machines.Turing.Universal.Clocked

@[expose] public section

/-!
# Tests for the clocked universal machine on stacks

The keyed entries of a small code, the scan semantics against table lookup, and concrete runs of
the stack machine: from the stacks of the initial configuration it stops at `hlt` with the halting
configuration when the clock suffices, and at `tmo` otherwise, within `clockTime`; from the input
bits `encIn c x T` it reaches `done` with `encOut (c.evalSteps x T)` on `O` within `univTime`.
-/

set_option autoImplicit false

open _root_.Turing

namespace CSLibExtTest.Computability.Machines.Turing.Universal.Clocked

open Cslib.Turing.Universal Cslib.Turing.Universal.Clocked

/-- Flip every input bit, walk back to the first cell and halt (as in `CodeTests`). -/
def flipBits : Code :=
  ⟨[[some (2, 0), some (1, 4), some (1, 3)], [none, some (0, 1), some (0, 1)],
    [some (3, 1), some (2, 0), some (2, 0)]]⟩

#guard entries flipBits =
  [(0, 0, 2, 0), (0, 1, 1, 4), (0, 2, 1, 3), (1, 1, 0, 1), (1, 2, 0, 1), (2, 0, 3, 1),
    (2, 1, 2, 0), (2, 2, 2, 0)]

#guard (List.range 5).all fun q ↦ (List.range 5).all fun a ↦
  findEntry q a (entries flipBits) == flipBits.lookup q a

/-- Eight entries: four markers each, plus their numbers, which sum to `38`. -/
example : (codeCells flipBits).length = 8 * 4 + 38 := by decide

/-- Run the stack machine until it reaches `hlt` or `tmo`, for at most `n` steps; also return the
number of steps taken. -/
def runUntil : ℕ → ℕ → TM2.Cfg Γ Lab Bool → Option (ℕ × TM2.Cfg Γ Lab Bool)
  | 0, _, _ => none
  | n + 1, i, c =>
    if c.l = some .hlt ∨ c.l = some .tmo then some (i, c)
    else (TM2.step prog c).bind (runUntil n (i + 1))

/-- The start configuration on the code `c`, the bits `x` and the clock `T`. -/
def start (c : Code) (x : List Bool) (T : ℕ) : TM2.Cfg Γ Lab Bool :=
  ⟨some .sc0, false, stk c T (Code.init x) 0 0⟩

/-- The label, the step count, and the state, head, left and right stacks at the stop. -/
def summary (c : Code) (x : List Bool) (T : ℕ) :
    Option (ℕ × Option Lab × List Bool × List Bool × List Bool × List Bool) :=
  (runUntil 100000 0 (start c x T)).map fun (i, d) ↦
    (i, d.l, d.stk .Q, d.stk .H, d.stk .L, d.stk .R)

/-- The stacks of the halting configuration after 8 steps on `[true, false]`. -/
def haltCfg : Code.Cfg := flipBits.cfgAfter [true, false] 8

#guard haltCfg = ⟨3, [0], 1, [2, 0]⟩

#guard (summary flipBits [true, false] 8).map (·.2) =
  some (some .hlt, List.replicate 3 true, [true], cells [0], cells [2, 0])

#guard (summary flipBits [true, false] 8).any fun r ↦ decide (r.1 ≤ clockTime flipBits 8)

#guard (summary flipBits [true, false] 7).map (·.2.1) = some (some .tmo)

#guard (summary flipBits [true, false] 7).any fun r ↦ decide (r.1 ≤ clockTime flipBits 7)

#guard (summary flipBits [false, false, true] 11).map (·.2.1) = some (some .hlt)

#guard (summary flipBits [false, false, true] 10).map (·.2.1) = some (some .tmo)

/-- Run the whole machine from the input bits until `done`, for at most `n` steps; return the
number of steps and the output stack. -/
def runAll : ℕ → ℕ → TM2.Cfg Γ Lab Bool → Option (ℕ × List Bool)
  | 0, _, _ => none
  | n + 1, i, c =>
    if c.l = some .done then some (i, c.stk .O)
    else (TM2.step prog c).bind (runAll n (i + 1))

/-- The whole machine on `(c, x, T)`: the step count and the output bits. -/
def whole (c : Code) (x : List Bool) (T : ℕ) : Option (ℕ × List Bool) :=
  runAll 100000 0 ⟨some .pc0, false, Function.update (fun _ ↦ []) .X (encIn c x T)⟩

#guard (whole flipBits [true, false] 8).map (·.2) = some (encOut (some [1, 2]))
#guard (whole flipBits [true, false] 8).map (·.2) =
  some (encOut (flipBits.evalSteps [true, false] 8))
#guard (whole flipBits [true, false] 7).map (·.2) = some (encOut none)
#guard (whole flipBits [false, false, true] 11).map (·.2) = some (encOut (some [2, 2, 1]))
#guard (whole flipBits [] 2).map (·.2) = some (encOut (some []))
#guard (whole ⟨[[some (1, 2), some (1, 2), some (1, 2)]]⟩ [true, true] 1).map (·.2) =
  some (encOut (some [0, 2]))
#guard (whole flipBits [true, false] 8).any fun r ↦ decide (r.1 ≤ univTime flipBits [true, false] 8)
#guard (whole flipBits [true, false, true] 20).any fun r ↦
  decide (r.1 ≤ univTime flipBits [true, false, true] 20)

end CSLibExtTest.Computability.Machines.Turing.Universal.Clocked
