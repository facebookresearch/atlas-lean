/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.TuringMachine.BitOps

namespace MetaMathlibExt

open Turing TM2Program Function

/-! A concrete compare-and-restore machine built from `cmpB` and `moveB`. Stacks `0` and `1` hold
bit blocks (symbols `some b`; `none` is a marker ending a block); stacks `2` and `3` are scratch.
Label `0` compares; labels `1`, `2` restore after "equal" and halt at `5`; labels `3`, `4` restore
after "different" and halt at `6`. -/

/-- The compare-and-restore machine. -/
def cmpMachine : Fin 7 → TM2.Stmt (fun _ : Fin 4 => Option Bool) (Fin 7) Bool
  | 0 => cmpB 0 1 2 3 id id some some 0 1 3
  | 1 => moveB 2 0 id some 1 2
  | 2 => moveB 3 1 id some 2 5
  | 3 => moveB 2 0 id some 3 4
  | 4 => moveB 3 1 id some 4 6
  | _ => .halt

/-- Blocks `u` and `w` (each followed by a rest) on stacks `0` and `1`, scratch stacks holding
`r` and `r'`. -/
def cmpInitR (u w r r' : List (Option Bool)) : ∀ _ : Fin 4, List (Option Bool)
  | 0 => u
  | 1 => w
  | 2 => r
  | 3 => r'

/-- Blocks `u` and `w` on stacks `0` and `1`, scratch empty. -/
def cmpInit (u w : List (Option Bool)) : ∀ _ : Fin 4, List (Option Bool) := cmpInitR u w [] []

/-- Run `n` steps from label `0` with scratch contents `r`, `r'`; report the label and the four
stacks. -/
def cmpAfterR (n : ℕ) (u w r r' : List (Option Bool)) :
    Option (Option (Fin 7) × List (Option Bool) × List (Option Bool) × List (Option Bool) ×
      List (Option Bool)) :=
  ((flip bind (TM2.step cmpMachine))^[n] (some ⟨some 0, false, cmpInitR u w r r'⟩)).map
    fun c => (c.l, c.stk 0, c.stk 1, c.stk 2, c.stk 3)

/-- `cmpAfterR` with empty scratch stacks. -/
def cmpAfter (n : ℕ) (u w : List (Option Bool)) :
    Option (Option (Fin 7) × List (Option Bool) × List (Option Bool) × List (Option Bool) ×
      List (Option Bool)) :=
  cmpAfterR n u w [] []

-- Equal blocks `10` (followed by different rests): 3 compare steps, 3 + 3 restore steps, then
-- "equal" (label 5) with both stacks back as they were.
example : cmpAfter 9 [some true, some false, none, some true] [some true, some false, none] =
    some (some 5, [some true, some false, none, some true], [some true, some false, none], [],
      []) := rfl

-- `10` against `11`: mismatch at the second bit, "different" (label 6), stacks restored.
example : cmpAfter 6 [some true, some false] [some true, some true] =
    some (some 6, [some true, some false], [some true, some true], [], []) := rfl

-- `10` against `101`: the first block ends first, so "different".
example : cmpAfter 9 [some true, some false] [some true, some false, some true] =
    some (some 6, [some true, some false], [some true, some false, some true], [], []) := rfl

-- Two empty blocks (a marker on top of one stack) are equal.
example : cmpAfter 3 [none, some true] [] = some (some 5, [none, some true], [], [], []) := rfl

-- Scratch stacks with old contents ending a block (a marker on top): restoration is exact and
-- the old contents stay (`moveB_restore`).
example : cmpAfterR 6 [some true, some false] [some true, some true] [none, some true] [none] =
    some (some 6, [some true, some false], [some true, some true], [none, some true], [none]) :=
  rfl

-- Old scratch contents that do not end a block break restoration (the precondition of
-- `moveB_restore` matters): the stray bit `false` below the pushed `true` is moved too.
example : cmpAfterR 7 [some true] [some true] [some false] [] =
    some (some 5, [some false, some true], [some true], [], []) := rfl

-- One step before the end of the first run the machine is still restoring stack `1`.
example : (cmpAfter 8 [some true, some false, none, some true]
    [some true, some false, none]).map (·.1) = some (some 2) := rfl

/-- The four stacks of `cmpMachine` are distinct. -/
theorem cmpMachine_distinct : Distinct4 (0 : Fin 4) 1 2 3 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- `cmpB_run` applies to the machine: comparing `10` with `10` ends at label `1` ("equal")
after `c.length + 1` steps for a common prefix `c`. -/
example : ∃ (c : List Bool) (v' : Bool) (S' : ∀ _ : Fin 4, List (Option Bool)),
    c <+: [true, false] ∧ c <+: [true, false] ∧
    (∀ bit, ([true, false].drop c.length).head? = some bit →
      ([true, false].drop c.length).head? ≠ some bit) ∧
    Run cmpMachine (c.length + 1) ⟨some 0, false, cmpInit [some true, some false] [some true,
      some false]⟩ ⟨some (if [true, false] = [true, false] then 1 else 3), v', S'⟩ ∧
    S' 0 = ([some true, some false] : List (Option Bool)).drop c.length ++ [] ∧
    S' 1 = ([some true, some false] : List (Option Bool)).drop c.length ++ [] ∧
    S' 2 = (c.map some).reverse ++ [] ∧ S' 3 = (c.map some).reverse ++ [] ∧
    ∀ k, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 3 → S' k = cmpInit [some true, some false]
      [some true, some false] k :=
  cmpB_run (M := cmpMachine) rfl cmpMachine_distinct [true, false] [true, false]
    [some true, some false] [] [some true, some false] [] false _ (by simp [cmpInit, cmpInitR])
    (by simp [cmpInit, cmpInitR]) (by simp [IsBitBlock]) (by simp [IsBitBlock])
    (by simp [EndsBitBlock]) (by simp [EndsBitBlock])

end MetaMathlibExt
