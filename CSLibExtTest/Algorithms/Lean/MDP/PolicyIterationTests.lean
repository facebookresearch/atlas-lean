/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.PolicyIteration
public meta import CSLibExt.Algorithms.Lean.MDP.PolicyIteration
public import Mathlib.Algebra.Order.Field.Rat
public meta import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Fin.VecNotation
public meta import Mathlib.Data.Fin.VecNotation

/-!
# Policy iteration tests

Executed fixtures over `ℚ`, on the maintenance MDP of the value-iteration tests (three states,
two actions, `γ = 9/10`). Policy evaluation solves the policy's linear system exactly (Gaussian
elimination); each run checks the computed value solves `policyBellman` exactly, that the greedy
policy's update equals the Bellman optimality update (`policyBellman_greedy`), that values never
decrease (the policy improvement theorem), and that iteration stops at a policy whose value solves
the Bellman optimality equation within `|A| ^ |S| = 8` steps; it throws otherwise. Run from all
eight starting policies. Closed checks instantiate the theorems over `ℝ`.
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

private meta def showV {n : ℕ} {β : Type} (V : Fin n → β) : List β := (List.finRange n).map V

private meta def ofList {n : ℕ} (t : List ℚ) : Fin n → ℚ := fun s => t.getD s.val 0

/-- Solve `(I - γ P_π) V = r_π` exactly by Gauss-Jordan elimination; the values as a list. -/
private meta def evaluateList (π : St → Ac) : List ℚ := Id.run do
  let n := 3
  let mut a : Array (Array ℚ) := (List.finRange n).toArray.map fun i =>
    ((List.finRange n).toArray.map fun j =>
      (if i = j then 1 else 0) - γm * machine.prob i (π i) j).push (machine.reward i (π i))
  for c in [0:n] do
    let some p := (List.range' c (n - c)).find? (fun r => ((a.getD r #[]).getD c 0) != 0) | pure ()
    let tmp := a.getD c #[]
    a := (a.set! c (a.getD p #[])).set! p tmp
    let pivot := ((a.getD c #[]).getD c 0)
    a := a.set! c ((a.getD c #[]).map (· / pivot))
    for r in [0:n] do
      if r != c then
        let f := ((a.getD r #[]).getD c 0)
        a := a.set! r (((a.getD r #[]).zip (a.getD c #[])).map fun (x, y) => x - f * y)
  return (List.range n).map fun i => ((a.getD i #[]).getD n 0)

/-- Evaluate in `IO`, so the table is computed once (a closure over an unevaluated table would
redo the elimination on every lookup). -/
private meta def evaluate (π : St → Ac) : IO (St → ℚ) := do
  let t ← pure (evaluateList π)
  pure (ofList t)

/-- A greedy policy, computed: the first action of largest value. -/
private meta def greedyQ (V : St → ℚ) : St → Ac := fun s =>
  if qValue machine γm V s 1 > qValue machine γm V s 0 then 1 else 0

private meta def supDist {n : ℕ} (V W : Fin n → ℚ) : ℚ :=
  (List.finRange n).foldl (fun m s => max m |V s - W s|) 0

#eval do
  let starts : List (St → Ac) :=
    [![0, 0, 0], ![0, 0, 1], ![0, 1, 0], ![0, 1, 1], ![1, 0, 0], ![1, 0, 1], ![1, 1, 0], ![1, 1, 1]]
  let mut maxSteps := 0
  for π0 in starts do
    let mut π := π0
    let mut steps := 0
    let mut done := false
    for _ in [0:9] do
      if done then continue
      let V ← evaluate π
      unless supDist (policyBellman machine γm π V) V == 0 do
        throw (IO.userError s!"start {showV π0}: value of {showV π} is not a fixed point")
      let πl ← pure ((List.finRange 3).map (greedyQ V))
      let π' : St → Ac := fun s => πl.getD s.val 0
      unless supDist (policyBellman machine γm π' V) (bellman machine γm V) == 0 do
        throw (IO.userError s!"start {showV π0}: greedy update differs from the Bellman update")
      let V' ← evaluate π'
      unless (List.finRange 3).all fun s => V s ≤ V' s do
        throw (IO.userError s!"start {showV π0}: improvement decreased a value")
      if supDist V' V == 0 then
        unless supDist (bellman machine γm V) V == 0 do
          throw (IO.userError s!"start {showV π0}: stalled at a non-optimal policy")
        done := true
      else
        π := π'
        steps := steps + 1
    unless done && steps ≤ 8 do throw (IO.userError s!"start {showV π0}: no convergence")
    maxSteps := max maxSteps steps
  IO.println s!"policy iteration from all 8 policies: optimal value \
    {evaluateList ![0, 1, 1]} reached in at most {maxSteps} improvement steps (bound 8)"

/-! Closed checks over `ℝ` -/

example (M : MDP St Ac ℝ) (γ : ℝ) (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π : St → Ac) :
    policyValue M γ hM hγ0 hγ1 (policyIteration hM hγ0 hγ1 (Fintype.card (St → Ac)) π) =
      optimalValue M γ hM hγ0 hγ1 :=
  policyValue_policyIteration hM hγ0 hγ1 π

#print axioms policyValue_le_policyValue_improve
#print axioms policyValue_improve_eq_iff
#print axioms policyValue_improve_ne
#print axioms policyValue_policyIteration

end Cslib.Algorithms.Lean.MarkovDecision
