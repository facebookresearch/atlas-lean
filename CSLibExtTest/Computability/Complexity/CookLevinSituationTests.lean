/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.CookLevin.Situation

/-! Concrete checks of the Cook-Levin situation tables (`Situation`) against real `TM2.step` runs on
two small machines, evaluated by `decide`. -/

@[expose] public section

namespace Cslib.Complexity.CookLevin.Situation

open MetaMathlibExt Turing Function

/-! ## [EX] Concrete check (evidence): a machine that halts partway through the run

Stacks `false` (input `a`) and `true` (`b`); alphabet `Bool`; labels `Fin 2`; state `Option Bool`.
* label 0: pop `a` into the state; if something was popped, push it on `b` and go to 1; else halt.
* label 1: push `true` on `b` and pop it again (cancels); pop an original symbol of `b` into the
  state; push it back and push `false` (net on `b`: 1 consumed, 2 pushed); peek `a`; go to 0.

On input of length 3 the machine halts after 7 steps. `ops` of the two trees are 2 and 6, so
`d = 6`, `g = 3`, `A0 = 9`. The table-driven row update is checked against the real idle-extended
run for `T = 10` steps (rows 7..10 are halted). -/

section Example

open TM2.Stmt in
/-- Program of the first example machine. -/
def exProg : Fin 2 → TM2.Stmt (fun _ : Bool => Bool) (Fin 2) (Option Bool)
  | 0 => pop false (fun _ o => o) <|
      branch (fun v => v.isSome) (push true (fun v => v.getD false) (goto fun _ => 1)) halt
  | 1 => push true (fun _ => true) <| pop true (fun v _ => v) <| pop true (fun _ o => o) <|
      push true (fun v => v.getD false) <| push true (fun _ => false) <|
        peek false (fun v _ => v) <| goto fun _ => 0

/-- The first example machine. -/
abbrev exM : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := fun _ => Bool
  Λ := Fin 2
  main := 0
  σ := Option Bool
  initialState := none
  m := exProg

/-- Label code of the first example. -/
def o3 : Option (Fin 2) → ℕ
  | none => 0
  | some i => i + 1

/-- Label decoding of the first example. -/
def d3 (n : ℕ) : Option (Fin 2) := if n = 1 then some 0 else if n = 2 then some 1 else none

/-- State code of the first example. -/
def v3 : Option Bool → ℕ
  | none => 0
  | some false => 1
  | some true => 2

/-- State decoding of the first example. -/
def e3 (n : ℕ) : Option Bool := if n = 1 then some false else if n = 2 then some true else none

/-- A computable `Enc` for `exM`. -/
def exE : Enc exM where
  KK := 2
  kc := fun b => if b then 1 else 0
  kd := fun n => decide (n = 1)
  kc_lt := by decide
  kd_kc := by decide
  kc_kd := by decide
  A0 := 9
  lc := fun x => o3 x.1 * 3 + v3 x.2
  ld := fun c => (d3 (c / 3), e3 (c % 3))
  lc_lt := by decide
  ld_lc := by decide
  lc_ld := by decide
  sz := fun _ => 2
  dec := fun _ i => decide (i.val = 1)
  enc := fun _ x => if x then 2 else 1
  enc_dec := by decide
  push_mem := fun _ _ x _ => ⟨if x then 1 else 0, by cases x <;> rfl⟩
  input_mem := fun x => ⟨if x then 1 else 0, by cases x <;> rfl⟩

/-- The real run, idle-extended (a halted configuration stays put). -/
def exRun (c : exM.Cfg) : ℕ → exM.Cfg
  | 0 => c
  | t + 1 => (TM2.step exM.m (exRun c t)).getD (exRun c t)

/-- Initial configuration of the first example. -/
def exInit : exM.Cfg := initList exM [true, false, true]

/-- Combined (label, state) code of a configuration. -/
def rowCode (c : exM.Cfg) : ℕ := exE.lc (c.l, c.var)

/-- Top-indexed cell code of stack `k`, depth `j` (`0` = ⊥). -/
def cell (c : exM.Cfg) (k j : ℕ) : ℕ :=
  ((c.stk (exE.kd k))[j]?).elim 0 (exE.enc _)

/-- The situation index of a configuration (mixed radix of its code and windows). -/
def sitIdx (c : exM.Cfg) : ℕ :=
  Enc.mix exE.g (rowCode c) (exE.KK * depth exM)
    (fun n => cell c (n / depth exM) (n % depth exM))

/-- **Table-driven row update** (what the clause families force): pushed fill, in-range shift,
overflow ⊥. -/
def tabRow (H i : ℕ) (old : ℕ → ℕ → ℕ) (k j : ℕ) : ℕ :=
  if j < exE.pl i k then exE.pu i k j
  else if j < H - max (exE.pl i k) (exE.cn i k) + exE.pl i k then
    old k (j - exE.pl i k + exE.cn i k)
  else 0

/-- Row `t` → row `t+1`: the situation is found correctly, and code + every cell of row `t+1`
are what the tables prescribe. -/
def rowOK (H t : ℕ) : Bool :=
  let c := exRun exInit t
  let c' := exRun exInit (t + 1)
  let i := sitIdx c
  decide (i < exE.N) && decide (exE.la i = rowCode c) &&
    decide (∀ k < exE.KK, ∀ j < depth exM, exE.wa i k j = cell c k j) &&
    decide (rowCode c' = exE.na i) &&
    decide (∀ k < exE.KK, ∀ j < H, cell c' k j = tabRow H i (cell c) k j)

theorem ex_depth : depth exM = 6 := by decide

theorem ex_g : exE.g = 3 := by decide

/-- The machine is running at row 6 and halted from row 7 on. -/
theorem ex_halts : (exRun exInit 6).l = some 0 ∧ (exRun exInit 7).l = none ∧
    (exRun exInit 10).l = none := by decide

/-- **Check**: all 10 transitions (rows 0..10, halted from row 7) follow the tables, `H = 16`. -/
theorem ex_rows : ∀ t < 10, rowOK 16 t = true := by decide

/-- The halted situations used by rows 7..9 have `na = la`, no pushes, no consumption (instance
of `Enc.halted`, here by evaluation). -/
theorem ex_halted_rows : ∀ t < 10, 7 ≤ t →
    exE.na (sitIdx (exRun exInit t)) = exE.la (sitIdx (exRun exInit t)) ∧
    ∀ k < 2, exE.pl (sitIdx (exRun exInit t)) k = 0 ∧ exE.cn (sitIdx (exRun exInit t)) k = 0 := by
  decide

/-- Negative control: a row update that ignores consumption (`cn := 0`) fails on this run. -/
def tabRowBad (H i : ℕ) (old : ℕ → ℕ → ℕ) (k j : ℕ) : ℕ :=
  if j < exE.pl i k then exE.pu i k j
  else if j < H then old k (j - exE.pl i k) else 0

theorem ex_neg : ¬ ∀ t < 10, ∀ k < 2, ∀ j < 16,
    cell (exRun exInit (t + 1)) k j = tabRowBad 16 (sitIdx (exRun exInit t)) (cell (exRun exInit t)) k j := by
  decide

end Example

/-! ## [EX2] Second concrete check (evidence, not part of the proof): B1-T's generic definitions
on a different machine

Three stacks `0` (input), `1`, `2`; alphabet `Fin 3`; labels `Fin 3`; state `Fin 4` (`3` = "none").
* label 0: pop `0` into the state; if empty go to 2; else push it on `1`, push `0` on `2`, peek
  `1` (reads the symbol pushed this step), `load`, go to 1.
* label 1: pop `2` twice (the second pop reads an original symbol or hits height 0), push the state
  on `2`, peek `0`, go to 0.
* label 2: pop `1` twice, peek `1` (reads depth 2 of the originals), push on `0` then pop it again
  (cancels), push `2` on `2`, halt.

`ops` = 4, 4, 6, so `d = 6`, `g = 4`, `A0 = 16`. Every row of the idle-extended run is compared
with `Enc.tabRow` / `Enc.na` via the generic `Enc.sitIdx`, `Enc.cell`, `Enc.code`, `stepI`,
`runI` (the definitions `table_agree` is about), by `decide` against Mathlib's `TM2.step`. -/

section Example2

/-- `Fin 4 → Fin 3`, reducing mod 3. -/
def f43 (v : Fin 4) : Fin 3 := ⟨v.val % 3, Nat.mod_lt _ (by decide)⟩

open TM2.Stmt in
/-- Program of the second example machine. -/
def ex2Prog : Fin 3 → TM2.Stmt (fun _ : Fin 3 => Fin 3) (Fin 3) (Fin 4)
  | 0 => pop 0 (fun _ o => (o.map Fin.castSucc).getD 3) <|
      branch (fun v => v = 3) (goto fun _ => 2) <|
        push 1 f43 <| push 2 (fun _ => 0) <| peek 1 (fun v o => if o.isSome then v else 3) <|
          load (fun v => v) <| goto fun _ => 1
  | 1 => pop 2 (fun v _ => v) <| pop 2 (fun v o => if o.isNone then 0 else v) <|
      push 2 f43 <| peek 0 (fun v _ => v) <| goto fun _ => 0
  | 2 => pop 1 (fun _ o => (o.map Fin.castSucc).getD 3) <| pop 1 (fun v _ => v) <|
      peek 1 (fun v o => (o.map Fin.castSucc).getD v) <| push 0 f43 <| pop 0 (fun v _ => v) <|
        push 2 (fun _ => 2) <| halt

/-- The second example machine. -/
abbrev ex2M : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 2
  Γ := fun _ => Fin 3
  Λ := Fin 3
  main := 0
  σ := Fin 4
  initialState := 0
  m := ex2Prog

/-- Label code of the second example. -/
def oL : Option (Fin 3) → ℕ
  | none => 0
  | some i => i + 1

/-- Label decoding of the second example. -/
def dL (n : ℕ) : Option (Fin 3) := if h : 0 < n ∧ n ≤ 3 then some ⟨n - 1, by omega⟩ else none

/-- A computable `Enc` for `ex2M`. -/
def ex2E : Enc ex2M where
  KK := 3
  kc := fun k => k.val
  kd := fun n => ⟨n % 3, Nat.mod_lt _ (by decide)⟩
  kc_lt := by decide
  kd_kc := by decide
  kc_kd := by decide
  A0 := 16
  lc := fun x => oL x.1 * 4 + x.2.val
  ld := fun c => (dL (c / 4), ⟨c % 4, Nat.mod_lt _ (by decide)⟩)
  lc_lt := by decide
  ld_lc := by decide
  lc_ld := by decide
  sz := fun _ => 3
  dec := fun _ i => i
  enc := fun _ x => x.val + 1
  enc_dec := fun _ _ => rfl
  push_mem := fun _ _ x _ => ⟨x, rfl⟩
  input_mem := fun x => ⟨x, rfl⟩

/-- Input of the second example. -/
def ex2In : List (Fin 3) := [2, 0, 1, 1]

/-- Idle-extended run of the second example. -/
def ex2Run (t : ℕ) : ex2M.Cfg := runI ex2M (initList ex2M ex2In) t

/-- Row `t` → row `t+1` through the generic B1-T definitions, plus the height hypothesis. -/
def row2OK (H t : ℕ) : Bool :=
  let c := ex2Run t
  let i := ex2E.sitIdx c
  decide (∀ k : Fin 3, (c.stk k).length ≤ H - depth ex2M) &&
    decide (i < ex2E.N) && decide (ex2E.la i = ex2E.code c) &&
    decide (∀ k < ex2E.KK, ∀ j < depth ex2M, ex2E.wa i k j = ex2E.cell c k j) &&
    decide (ex2E.code (ex2Run (t + 1)) = ex2E.na i) &&
    decide (∀ k < ex2E.KK, ∀ j < H,
        ex2E.cell (ex2Run (t + 1)) k j = ex2E.tabRow H i (ex2E.cell c) k j)

theorem ex2_depth : depth ex2M = 6 := by decide

theorem ex2_g : ex2E.g = 4 := by decide

/-- The machine is running at row 9 and halted from row 10 on. -/
theorem ex2_halts : (ex2Run 9).l = some 2 ∧ (ex2Run 10).l = none ∧ (ex2Run 14).l = none := by
  decide

/-- **Check**: all 14 transitions (rows 0..14, halted from row 10) satisfy the height hypothesis
and follow the tables, `H = 16`. -/
theorem ex2_rows : ∀ t < 14, row2OK 16 t = true := by decide

/-- Negative control: the same check with the net consumption dropped from the shift fails. -/
theorem ex2_neg : ¬ ∀ t < 14, ∀ k < 3, ∀ j < 16,
    ex2E.cell (ex2Run (t + 1)) k j =
      (if j < ex2E.pl (ex2E.sitIdx (ex2Run t)) k then ex2E.pu (ex2E.sitIdx (ex2Run t)) k j
       else ex2E.cell (ex2Run t) k (j - ex2E.pl (ex2E.sitIdx (ex2Run t)) k)) := by
  decide

end Example2

end Cslib.Complexity.CookLevin.Situation
