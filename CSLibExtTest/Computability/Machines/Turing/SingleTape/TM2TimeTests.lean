/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.SingleTape.TM2Time
public meta import CSLibExt.Computability.Machines.Turing.SingleTape.TM2Time

@[expose] public section

/-!
# Tests for the time overhead of the single-tape emulation

`pushPop` is a one-stack machine over `Bool`: its main label pushes `true` and jumps to a label
that pops it and halts. On the input `false` it halts after two steps with the stack `false`. Its
single-tape emulation `MetaMathlibExt.TM2ToTM0.tr pushPop.m` is run on the encoded input: it halts
after `22` steps, against the bound `C t (|L| + C t + 1) = 3248` of `exists_tm0_run_of_tm2_run`
for `t = 2`, `|L| = 1` and `C = emulationConstant pushPop = 28`.
-/

set_option autoImplicit false

open Relation Turing Cslib.Turing.TM2Time
open scoped MetaMathlibExt.TM2ToTM0

namespace CSLibExtTest.Computability.Machines.Turing.SingleTape.TM2Time

/-- One stack of Booleans. The main label `false` pushes `true` and jumps to the label `true`,
which pops and halts. -/
def pushPop : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := fun _ ↦ Bool
  Λ := Bool
  main := false
  σ := Unit
  initialState := ()
  m
    | false => .push () (fun _ ↦ true) (.goto fun _ ↦ true)
    | true => .pop () (fun s _ ↦ s) .halt

/-- Run a machine with a step function for `k` steps, or until it halts. -/
def run {α : Type*} (f : α → Option α) : ℕ → α → α
  | 0, c => c
  | k + 1, c => (f c).elim c (run f k)

/-- The single-tape emulation of `pushPop`. -/
abbrev emu : TM0.Machine (TM2to1.Γ' pushPop.K pushPop.Γ) (TM1to0.Λ' (TM2to1.tr pushPop.m)) :=
  MetaMathlibExt.TM2ToTM0.tr pushPop.m

/-- The initial configuration of the emulation on the input `false`. -/
abbrev emuInit : TM0.Cfg (TM2to1.Γ' pushPop.K pushPop.Γ) (TM1to0.Λ' (TM2to1.tr pushPop.m)) :=
  TM0.init (TM2to1.trInit pushPop.k₀ [false])

/-! On `false`, `pushPop` halts after two steps, leaving `false` on its stack. -/

#guard ((flip bind pushPop.step)^[2] (some (initList pushPop [false]))).map
  (fun c ↦ ((c.l : Option Bool), (c.stk () : List Bool))) == some (none, [false])

#guard ((flip bind pushPop.step)^[3] (some (initList pushPop [false]))).isNone

/-! The emulation steps `21` times without halting and halts on step `22`. -/

#guard (List.range 22).all fun k ↦ (TM0.step emu (run (TM0.step emu) k emuInit)).isSome

#guard (TM0.step emu (run (TM0.step emu) 22 emuInit)).isNone

/-- The machine constant of `pushPop`: its statements have size `2` each and its push bound is
`P = pushBound = 1`, so `C = 3 (2 · 4 + 1) + 1`. -/
theorem emulationConstant_pushPop : emulationConstant pushPop = 28 := by
  decide

/-- The two-step run of `pushPop` on `false` ends in a halted configuration. -/
theorem pushPop_halts : ∃ c, (flip bind pushPop.step)^[2] (some (initList pushPop [false])) =
    some c ∧ pushPop.step c = none :=
  ⟨_, rfl, rfl⟩

/-- `exists_tm0_halt_of_tm2_halt` on `pushPop`: the emulation halts within `3248` steps. -/
example : ∃ (c₁ : TM1.Cfg (TM2to1.Γ' pushPop.K pushPop.Γ)
      (TM2to1.Λ' pushPop.K pushPop.Γ pushPop.Λ pushPop.σ) pushPop.σ) (n : ℕ),
      RelatesInSteps (fun a b ↦ b ∈ TM0.step emu a) emuInit (TM1to0.trCfg _ c₁) n ∧
      TM0.step emu (TM1to0.trCfg _ c₁) = none ∧ n ≤ 3248 := by
  obtain ⟨c, h, hc⟩ := pushPop_halts
  obtain ⟨c₁, n, -, hr, hhalt, hn⟩ := exists_tm0_halt_of_tm2_halt pushPop [false] h hc
  exact ⟨c₁, n, hr, hhalt, by rwa [emulationConstant_pushPop] at hn⟩

/-- `exists_tm0_run_of_tm2_run` instantiated: every run of `pushPop` on any input, of any
length, is emulated within the quadratic bound. -/
example (L : List Bool) (t : ℕ) (c : pushPop.Cfg)
    (h : (flip bind pushPop.step)^[t] (some (initList pushPop L)) = some c) :
    ∃ (c₁ : TM1.Cfg (TM2to1.Γ' pushPop.K pushPop.Γ)
      (TM2to1.Λ' pushPop.K pushPop.Γ pushPop.Λ pushPop.σ) pushPop.σ) (n : ℕ),
      TM2to1.TrCfg c c₁ ∧
      RelatesInSteps (fun a b ↦ b ∈ TM0.step emu a)
        (TM0.init (TM2to1.trInit pushPop.k₀ L)) (TM1to0.trCfg _ c₁) n ∧
      n ≤ 28 * t * (L.length + 28 * t + 1) := by
  rw [← emulationConstant_pushPop]
  exact exists_tm0_run_of_tm2_run pushPop L h

end CSLibExtTest.Computability.Machines.Turing.SingleTape.TM2Time
