/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.ContinuousMappedLoopHomotopy
public import Batteries.Tactic.Lint

/-! # The original jointly continuous mapped-loop value -/

public section

open scoped Topology

universe u v

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {f g : C(X, Y)}

example (H : ContinuousMap.HomotopyRel f g {x}) (t s : unitInterval) (γ : LoopSpace X x) :
    (H.mappedLoopFamily (t, γ)) s = H (t, γ s) :=
  ContinuousMap.HomotopyRel.mappedLoopFamily_apply H t γ s

#print axioms ContinuousMap.HomotopyRel.mappedLoopFamily_apply

run_cmd do
  let env ← Lean.getEnv
  let selected := `MathlibExt.Topology.Homotopy.ContinuousMappedLoopHomotopy
  let trusted : Array Lean.Name := #[``propext, ``Quot.sound, ``Classical.choice]
  let mut count : Nat := 0
  for i in [0:env.header.moduleNames.size] do
    unless selected == env.header.moduleNames[i]! do
      continue
    for name in env.header.moduleData[i]!.constNames do
      count := count + 1
      let axioms ← Lean.collectAxioms name
      let forbidden := axioms.filter fun ax => !trusted.contains ax
      unless forbidden.isEmpty do
        throwError "{name} depends on forbidden axioms: {forbidden}"
  Lean.logInfo m!"Std3 checked {count} mapped-loop supplier declarations"

#lint only unusedArguments in MathlibExt.Topology.Homotopy.ContinuousMappedLoopHomotopy
