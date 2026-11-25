/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.GreedyPolicyBound
public meta import CSLibExt.Algorithms.Lean.MDP.GreedyPolicyBound
public import Mathlib.Algebra.Order.Field.Rat
public meta import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Fin.VecNotation
public meta import Mathlib.Data.Fin.VecNotation

/-!
# Greedy policies of approximate values: tests

Executed fixtures over `ℚ` on the maintenance MDP of the value-iteration tests (`γ = 9/10`,
optimal policy `![0, 1, 1]`). For perturbations `V = V* + δ` with `|δ| ≤ d`, the run computes a
greedy policy for `V` (first action of largest value), evaluates it exactly, and checks
`0 ≤ V*(s) - V^π(s) ≤ 2 γ d / (1 - γ)` (`optimalValue_sub_policyValue_greedy_le`); it throws
otherwise. Closed checks instantiate the theorems over `ℝ`.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision

private abbrev St := Fin 3
private abbrev Ac := Fin 2

private meta def machine : MDP St Ac ℚ where
  reward := ![![3, 1], ![2, 0], ![-1, -4]]
  prob := ![![![1/2, 1/2, 0], ![1, 0, 0]],
    ![![0, 1/2, 1/2], ![3/4, 1/4, 0]],
    ![![0, 0, 1], ![1/2, 1/2, 0]]]

private meta def γm : ℚ := 9 / 10
private meta def sts : List St := List.finRange 3

/-- Solve `(I - γ P_π) V = r_π` exactly by Gauss-Jordan elimination. -/
private meta def evaluate (π : St → Ac) : St → ℚ := Id.run do
  let n := 3
  let mut m : Array (Array ℚ) := sts.toArray.map fun i =>
    (sts.toArray.map fun j => (if i = j then 1 else 0) - γm * machine.prob i (π i) j).push
      (machine.reward i (π i))
  for c in [0:n] do
    let some p := (List.range' c (n - c)).find? (fun r => ((m.getD r #[]).getD c 0) != 0)
      | pure ()
    let tmp := m.getD c #[]
    m := (m.set! c (m.getD p #[])).set! p tmp
    let pivot := ((m.getD c #[]).getD c 0)
    m := m.set! c ((m.getD c #[]).map (· / pivot))
    for r in [0:n] do
      if r != c then
        let f := ((m.getD r #[]).getD c 0)
        m := m.set! r (((m.getD r #[]).zip (m.getD c #[])).map fun (x, y) => x - f * y)
  let t := (List.range n).map fun i => ((m.getD i #[]).getD n 0)
  return fun s => t.getD s.val 0

private meta def greedyQ (V : St → ℚ) : St → Ac := fun s =>
  if qValue machine γm V s 1 > qValue machine γm V s 0 then 1 else 0

#eval do
  let Vs := evaluate ![0, 1, 1]
  unless sts.all fun s => bellman machine γm Vs s == Vs s do
    throw (IO.userError "![0, 1, 1] is not optimal")
  let mut checks := 0
  for d in [(1 : ℚ) / 10, 1, 5, 20] do
    for (δ : St → ℚ) in [![d, -d, d], ![-d, d, -d], ![d, d, -d], ![0, -d, d], ![-d, 0, d / 2]] do
      let V : St → ℚ := fun s => Vs s + δ s
      let π := greedyQ V
      let Vπ := evaluate π
      for s in sts do
        unless 0 ≤ Vs s - Vπ s ∧ Vs s - Vπ s ≤ 2 * γm * d / (1 - γm) do
          throw (IO.userError s!"Singh-Yee bound fails for d = {d}")
        checks := checks + 1
  IO.println s!"greedy policies of approximate values: {checks} exact checks passed"

/-! Closed checks over `ℝ` -/

example (M : MDP St Ac ℝ) (γ : ℝ) (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (V : St → ℝ) (hV : ∀ s, |V s - optimalValue M γ hM hγ0 hγ1 s| ≤ 1) (s : St) :
    optimalValue M γ hM hγ0 hγ1 s - policyValue M γ hM hγ0 hγ1 (greedy M γ V) s ≤
      2 * γ * 1 / (1 - γ) :=
  (optimalValue_sub_policyValue_greedy_le hM hγ0 hγ1 hV s).2

#print axioms optimalValue_sub_policyValue_greedy_le
#print axioms optimalValue_sub_policyValue_greedy_valueIteration_le

end Cslib.Algorithms.Lean.MarkovDecision
