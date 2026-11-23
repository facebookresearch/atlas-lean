/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.TokenRing

/-!
# Tests for Dijkstra's token ring

Concrete configurations checked against the definitions, then fed to the theorems.

* Two machines with states in `ZMod 3`: in the constant-zero configuration only machine `0` is
  privileged, and its move passes the privilege to machine `1`.
* Three machines with states in `ZMod 4`: a move by machine `1` passes the privilege to machine
  `2`, whose move wraps it around to machine `0`.
* One machine: it is the only privileged machine before and after its move.
-/

@[expose] public section

namespace Cslib.Distributed.TokenRing.Tests

/-! ### Two machines: a move by machine `0` -/

/-- Two machines, both in state `0`. -/
def two₀ : ZMod 2 → ZMod 3 := fun _ => 0

/-- `two₀` after machine `0` increments its state. -/
def two₁ : ZMod 2 → ZMod 3 := fun i => if i = 0 then 1 else 0

example : privileged two₀ 0 := by
  unfold privileged two₀
  decide

/-- Machine `0` is the unique privileged machine of `two₀`. -/
theorem two₀_legit : Legit two₀ := by
  refine ⟨0, ?_, ?_⟩ <;> unfold privileged two₀ <;> decide

/-- Machine `0` moves from `two₀` to `two₁`. -/
theorem two₀_step : Step two₀ two₁ := by
  refine ⟨0, ?_, ?_⟩
  · unfold privileged two₀
    decide
  · unfold moveVal two₀ two₁
    decide

example : Legit two₁ :=
  legit_closed two₀_legit two₀_step

example : privileged two₁ 1 ∧ ¬ privileged two₁ 0 := by
  unfold privileged two₁
  decide

/-! ### Three machines: a move by machine `1`, then a wrapping move by machine `2` -/

/-- Three machines in states `1, 0, 0`. -/
def three₀ : ZMod 3 → ZMod 4 := fun i => if i = 0 then 1 else 0

/-- `three₀` after machine `1` copies its predecessor: states `1, 1, 0`. -/
def three₁ : ZMod 3 → ZMod 4 := fun i => if i = 2 then 0 else 1

/-- `three₁` after machine `2` copies its predecessor: states `1, 1, 1`. -/
def three₂ : ZMod 3 → ZMod 4 := fun _ => 1

/-- Machine `1` is the unique privileged machine of `three₀`. -/
theorem three₀_legit : Legit three₀ := by
  refine ⟨1, ?_, ?_⟩ <;> unfold privileged three₀ <;> decide

/-- Machine `1` moves from `three₀` to `three₁`. -/
theorem three₀_step : Step three₀ three₁ := by
  refine ⟨1, ?_, ?_⟩
  · unfold privileged three₀
    decide
  · unfold moveVal three₀ three₁
    decide

/-- Closure after a move by a machine other than `0`. -/
theorem three₁_legit : Legit three₁ :=
  legit_closed three₀_legit three₀_step

example : privileged three₁ 2 ∧ ¬ privileged three₁ 1 := by
  unfold privileged three₁
  decide

/-- The last machine moves from `three₁` to `three₂`. -/
theorem three₁_step : Step three₁ three₂ := by
  refine ⟨2, ?_, ?_⟩
  · unfold privileged three₁
    decide
  · unfold moveVal three₁ three₂
    decide

example : Legit three₂ :=
  legit_closed three₁_legit three₁_step

example : privileged three₂ 0 ∧ ¬ privileged three₂ 2 := by
  unfold privileged three₂
  decide

/-! ### One machine -/

/-- One machine in state `5`. -/
def one₀ : ZMod 1 → ZMod 7 := fun _ => 5

/-- `one₀` after its move. -/
def one₁ : ZMod 1 → ZMod 7 := fun _ => 6

/-- The only machine of `one₀` is privileged. -/
theorem one₀_legit : Legit one₀ := by
  refine ⟨0, ?_, ?_⟩ <;> unfold privileged one₀ <;> decide

/-- The only machine moves from `one₀` to `one₁`. -/
theorem one₀_step : Step one₀ one₁ := by
  refine ⟨0, ?_, ?_⟩
  · unfold privileged one₀
    decide
  · unfold moveVal one₀ one₁
    decide

example : Legit one₁ :=
  legit_closed one₀_legit one₀_step

example : privileged one₁ 0 := by
  unfold privileged one₁
  decide

end Cslib.Distributed.TokenRing.Tests
