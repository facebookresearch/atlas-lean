/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.MultiTape.Basic
public import CSLibExt.Computability.Machines.Turing.MultiTape.TimeFromSpace

@[expose] public section

/-!
# The restored CSLib v4.35 multi-tape API keeps its arguments in order

`Basic.lean` and `TimeFromSpace.lean` restate declarations CSLib v4.36 dropped. As in CSLib
v4.35, the run lemmas, the `HaltsAt` lemmas, `exists_haltsAt` and the space of a run take the
machine before the input, and `core_step_eq_of_core_eq` takes the input before the machine, so
code that passes these arguments by position elaborates as it did against CSLib v4.35.
-/

set_option autoImplicit false

namespace CSLibExtTest.Computability.Machines.Turing.MultiTape.RestoredSignatures

open _root_.Turing

variable {k : ℕ} {State Symbol : Type} (tm : MultiTapeTM k Symbol State) (input : List Symbol)
  (cfg : Cfg k Symbol State input) (t : ℕ)

example : tm.runFrom cfg (t + 1) = tm.step (tm.runFrom cfg t) :=
  @MultiTapeTM.runFrom_succ k State Symbol tm input cfg t

example (s : ℕ) (h₁ : tm.HaltsAt cfg s) (h₂ : tm.HaltsAt cfg t) : s = t :=
  @MultiTapeTM.HaltsAt.unique k State Symbol tm input cfg s t h₁ h₂

example (h : (tm.runFrom cfg t).Halted) : ∃ u ≤ t, tm.HaltsAt cfg u :=
  @MultiTapeTM.exists_haltsAt k State Symbol tm input cfg t h

example : @MultiTapeTM.spaceUsed k State Symbol tm input cfg t =
    ∑ i, @MultiTapeTM.spaceUsedByTape k State Symbol tm input cfg t i :=
  rfl

example {c₁ c₂ : Cfg k Symbol State input} (h : c₁.core = c₂.core) :
    (tm.step c₁).core = (tm.step c₂).core :=
  @core_step_eq_of_core_eq k State Symbol input tm c₁ c₂ h

end CSLibExtTest.Computability.Machines.Turing.MultiTape.RestoredSignatures
